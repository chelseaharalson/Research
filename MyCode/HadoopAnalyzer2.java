package MyCode;

import java.io.File;
import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Iterator;
import java.util.Properties;
import java.util.HashSet;
import java.util.HashMap;

import com.ibm.wala.classLoader.IBytecodeMethod;
import com.ibm.wala.classLoader.IClass;
import com.ibm.wala.classLoader.IMethod;
import com.ibm.wala.classLoader.ShrikeBTMethod;
import com.ibm.wala.ipa.callgraph.AnalysisCache;
import com.ibm.wala.ipa.callgraph.AnalysisOptions;
import com.ibm.wala.ipa.callgraph.AnalysisScope;
import com.ibm.wala.ipa.callgraph.CallGraph;
import com.ibm.wala.ipa.callgraph.CallGraphBuilder;
import com.ibm.wala.ipa.callgraph.CallGraphBuilderCancelException;
import com.ibm.wala.ipa.callgraph.CallGraphStats;
import com.ibm.wala.ipa.callgraph.CGNode;
import com.ibm.wala.ipa.callgraph.ContextSelector;
import com.ibm.wala.ipa.callgraph.Entrypoint;
import com.ibm.wala.ipa.callgraph.propagation.PropagationCallGraphBuilder;
import com.ibm.wala.ipa.callgraph.propagation.HeapModel;
import com.ibm.wala.ipa.callgraph.propagation.InstanceKey;
import com.ibm.wala.ipa.callgraph.propagation.PointerAnalysis;
import com.ibm.wala.ipa.callgraph.propagation.PointerKey;
import com.ibm.wala.ipa.callgraph.propagation.SSAContextInterpreter;
import com.ibm.wala.ipa.callgraph.propagation.cfa.nCFABuilder;
import com.ibm.wala.ipa.callgraph.propagation.cfa.ZeroXContainerCFABuilder;
import com.ibm.wala.ipa.callgraph.propagation.cfa.ZeroXCFABuilder;
import com.ibm.wala.ipa.callgraph.propagation.cfa.ZeroXInstanceKeys;
import com.ibm.wala.ipa.callgraph.impl.DefaultEntrypoint;
import com.ibm.wala.ipa.callgraph.impl.ExplicitCallGraph;
import com.ibm.wala.ipa.callgraph.impl.Util;
import com.ibm.wala.ipa.callgraph.impl.Everywhere;
import com.ibm.wala.ipa.cfg.ExplodedInterproceduralCFG;
import com.ibm.wala.ipa.cha.ClassHierarchy;
import com.ibm.wala.ipa.cha.ClassHierarchyException;
import com.ibm.wala.ipa.cha.IClassHierarchy;
import com.ibm.wala.ipa.slicer.NormalReturnCaller;
import com.ibm.wala.ipa.slicer.Slicer;
import com.ibm.wala.ipa.slicer.Statement;
import com.ibm.wala.ipa.slicer.StatementWithInstructionIndex;
import com.ibm.wala.ipa.slicer.Slicer.ControlDependenceOptions;
import com.ibm.wala.ipa.slicer.Slicer.DataDependenceOptions;
import com.ibm.wala.ipa.slicer.thin.ThinSlicer;
import com.ibm.wala.shrikeCT.InvalidClassFileException; 
import com.ibm.wala.ssa.IR;
import com.ibm.wala.ssa.SSAAbstractInvokeInstruction;
import com.ibm.wala.ssa.SSACFG;
import com.ibm.wala.ssa.SSAConditionalBranchInstruction;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.ssa.SSAMonitorInstruction;
import com.ibm.wala.ssa.SSAInvokeInstruction;
import com.ibm.wala.ssa.SSASwitchInstruction;
import com.ibm.wala.ssa.analysis.ExplodedControlFlowGraph;
import com.ibm.wala.ssa.analysis.IExplodedBasicBlock;
import com.ibm.wala.types.ClassLoaderReference;
import com.ibm.wala.types.TypeName;
import com.ibm.wala.types.TypeReference;
import com.ibm.wala.util.config.AnalysisScopeReader;
import com.ibm.wala.util.graph.NumberedEdgeManager;
import com.ibm.wala.util.intset.IntSet;
import com.ibm.wala.util.intset.OrdinalSet;
import com.ibm.wala.util.intset.IntSetAction;
import com.ibm.wala.util.intset.IntIterator;
import com.ibm.wala.util.io.CommandLine;
import com.ibm.wala.util.strings.StringStuff;
import com.ibm.wala.util.warnings.Warnings;


public class HadoopAnalyzer2 {
//Should read this from the command line
  static String pType;
  static String targetClassNames;
  static String mainClass;
  static String entryClass;
  static String exclusionsFile;
  static CallGraphBuilder builder;
  static IClassHierarchy cha;
  static CallGraph cg;
  static ExplodedInterproceduralCFG icfg;
  static PointerAnalysis pointerAnalysis; 
  static HeapModel heapModel;
  
  static HashSet<CGNode> visitedNodes = new HashSet<CGNode>();
  
  // maps locking instructions to the the points-to set of the conditional statements acquired
  static HashMap<SSAInstruction,OrdinalSet<? extends InstanceKey>>  conditionalInstructions = new HashMap<SSAInstruction,OrdinalSet<? extends InstanceKey>>(); 

  // maps instructions to <cgnode,basicblock>
  static HashMap<SSAInstruction, Triple<Integer, CGNode, IExplodedBasicBlock>> instructionContext = new  HashMap<SSAInstruction, Triple<Integer, CGNode, IExplodedBasicBlock>>();
  //  CGNode => HashSet<SSAInstruction>
  static HashMap<CGNode, HashSet<SSAInstruction>> callSites = new HashMap<CGNode, HashSet<SSAInstruction>>();

  static  class Triple<T1, T2, T3> {

    Object val1;
    Object val2;
    Object val3;

    public Triple(Object v1, Object v2, Object v3) 
    {
        val1 = v1;
        val2 = v2;
        val3 = v3; 
    }      
  }
/**
 * Usage: ScopeFileCallGraph -scopeFile file_path [-entryClass class_name |
 * -mainClass class_name]
 * 
 * If given -mainClass, uses main() method of class_name as entrypoint. If
 * given -entryClass, uses all public methods of class_name.
 * 
 * @throws IOException
 * @throws ClassHierarchyException
 * @throws CallGraphBuilderCancelException
 * @throws IllegalArgumentException
 */
  public static void main(String[] args) throws Exception, IOException, ClassHierarchyException, IllegalArgumentException,
          CallGraphBuilderCancelException, InvalidClassFileException {
  long start = System.currentTimeMillis();
  Properties p = CommandLine.parse(args);
  String scopeFile = p.getProperty("scopeFile");
  entryClass = p.getProperty("entryClass");
  mainClass = p.getProperty("mainClass");
  targetClassNames = p.getProperty("targetClassNames");
  exclusionsFile = p.getProperty("exclusionsFile");

  pType = p.getProperty("pointerAnalysis"); 
  if (pType == null)
     pType = "zeroOneConCFA";
  // Format: Each line represents a separate statement specification
  // className;methodName;lineNo

  if (mainClass != null && entryClass != null) {
    throw new IllegalArgumentException("only specify one of mainClass or entryClass");
  }
  // use exclusions to eliminate certain library packages

  if (targetClassNames == null)
System.out.println("WARNING: Analysis could be more efficient by specifying a semicolon separated list of target classes (excluding mainClass and entryClass) with -targetClassNames option (use / instead of . in class names)"); 

  System.out.println("building call graph...");
  configureAndCreateCallGraph(scopeFile, mainClass, entryClass); 

//  CallGraphBuilder builder = Util.makeNCFABuilder(2, options, cache, cha, scope);
//  CallGraphBuilder builder = Util.makeVanillaNCFABuilder(2, options, cache, cha, scope);




  pointerAnalysis = builder.getPointerAnalysis();
  heapModel = pointerAnalysis.getHeapModel();
  //System.out.println("Exploding the call graph.." + cg.getClass().getName());
                  
  icfg = ExplodedInterproceduralCFG.make(cg);

  for(CGNode node: icfg.getCallGraph()) 
  { 
      if (!isATarget(node)) continue; 
      ExplodedControlFlowGraph graph = (ExplodedControlFlowGraph)  icfg.getCFG(node);

      if (graph == null) continue; 
      
      //System.out.println("adding call sites of this method:");
      HashSet<SSAInstruction> csites = callSites.get(node);
      if (csites != null) 
      {
          //for(SSAInstruction csins: csites) 
          {
              System.out.println("Call site for "  + node.getMethod().getName() + " (Instruction " + csites + " )");
          }
      }
      
      IR ir = node.getIR();
      if (ir == null) continue;
      SSAInstruction[] insts = ir.getInstructions();
      for(int i=0; i < insts.length; i++) 
      {
          SSAInstruction inst = insts[i];
          instructionContext.put(inst, new Triple(i, node, graph.getBlockForInstruction(i)));
          addCallSites(node, inst);
          //System.out.println(inst);
          if (inst instanceof SSAConditionalBranchInstruction)
          {
            SSAConditionalBranchInstruction ci = (SSAConditionalBranchInstruction) inst;
            System.out.println("CONTROL STATEMENT: " + node.getMethod().getName() + "   " + ci);
          }
          //transitivePredecessor(inst, node, visitedNodes);
      }
      //System.out.println(node);
       
  }
  
  // Thin slicing...
  /*ArrayList<Statement> seedStatements = new ArrayList<Statement>();
  
  for(CGNode sliceNode: icfg.getCallGraph())
  {
     // find seed statement
     Statement statement = findCallTo(sliceNode, "newInstance");
     if (statement != null)
     {
         seedStatements.add(statement);
     }
  }
                          
  Collection<Statement> slice = null;
  
  for(Statement statement: seedStatements) 
  {                
      //context-insensitive slice
      ThinSlicer ts = new ThinSlicer(cg,pointerAnalysis);
      slice = ts.computeBackwardThinSlice (statement);
      dumpSlice(statement, slice);                        
   }*/

          
  long end = System.currentTimeMillis();
  System.out.println("done");
  System.out.println("took " + (end-start) + "ms");
  System.out.println(CallGraphStats.getStats(cg));

}
  
  private static boolean isAnEntryClass(String name) 
  {
    String[] entryClassName = entryClass.split(";");
    for(int i=0; i < entryClassName.length; i++)
    {
       if (name.indexOf(entryClassName[i]) >= 0)
       {
          return true;
       }
    }
    return false;
  }

  private static boolean isATarget(CGNode node) 
  {
      String className = node.getMethod().getDeclaringClass().getName().toString(); 
      if (mainClass != null && className.indexOf(mainClass) >= 0)
          return true;
      if (entryClass != null && isAnEntryClass(className))
          return true;  
      if (targetClassNames == null) // All classes will be analyzed
          return true; 
      String[] targetClassName = targetClassNames.split(";");        
      for(int i=0; i < targetClassName.length; i++) 
      {
        if (className.indexOf(targetClassName[i]) >= 0)
        return true;
      }
      return false; 
  }
  
  private static void configureAndCreateCallGraph(String scopeFile, String mainClass, String entryClass) throws IOException, ClassHierarchyException, CallGraphBuilderCancelException  {
    File exclusionsFile = null;
    AnalysisScope scope = AnalysisScopeReader.readJavaScope(scopeFile, exclusionsFile, HadoopAnalyzer4.class.getClassLoader()); 
    cha = ClassHierarchy.make(scope);
    //System.out.println(cha.getNumberOfClasses() + " classes");
    //System.out.println(Warnings.asString());
    Warnings.clear();
    AnalysisOptions options = new AnalysisOptions();
    Iterable<Entrypoint> entrypoints = null;
    if (entryClass != null) {
       ArrayList<Entrypoint> all = new ArrayList<Entrypoint>();
       String[] entryClassName = entryClass.split(";");
       for(int i=0; i < entryClassName.length; i++) {
          System.out.println("Making entry points for class " + entryClassName[i]);
          // Removing the prefix L before passing to makePublicEntryPoints!
          all.addAll((Collection<Entrypoint>)makePublicEntrypoints(scope, cha, entryClassName[i].substring(1)));
      }
       entrypoints = all;
    }
    else entrypoints = Util.makeMainEntrypoints(scope, cha, mainClass);
    //Iterable<Entrypoint> entrypoints = entryClass != null ? makePublicEntrypoints(scope, cha, entryClass) : Util.makeMainEntrypoints(scope, cha, mainClass);
    options.setEntrypoints(entrypoints);
    options.setHandleStaticInit(true);
    // you can dial down reflection handling if you like
    options.setReflectionOptions(AnalysisOptions.ReflectionOptions.NONE);
    AnalysisCache cache = new AnalysisCache();
    // other builders can be constructed with different Util methods
    Util.addDefaultSelectors(options, cha);
    Util.addDefaultBypassLogic(options, scope, Util.class.getClassLoader(), cha);
    ContextSelector appSelector = null;
    SSAContextInterpreter appInterpreter = null;
  
    // This disables ZeroXInstanceKeys.SMUSH_PRIMITIVE_HOLDERS (by not explicitly specifying it)
    if (pType.equals("zeroOneConCFA"))
       builder = new ZeroXContainerCFABuilder(cha, options, cache, appSelector, appInterpreter, ZeroXInstanceKeys.ALLOCATIONS | ZeroXInstanceKeys.SMUSH_MANY |  ZeroXInstanceKeys.SMUSH_STRINGS | ZeroXInstanceKeys.SMUSH_THROWABLES);
    else if (pType.equals("zeroOneCFA"))
       builder = new ZeroXCFABuilder(cha, options, cache, appSelector, appInterpreter, ZeroXInstanceKeys.ALLOCATIONS | ZeroXInstanceKeys.SMUSH_MANY |  ZeroXInstanceKeys.SMUSH_STRINGS | ZeroXInstanceKeys.SMUSH_THROWABLES);
    else if (pType.equals("zeroCFA"))
       builder = new ZeroXCFABuilder(cha, options, cache, appSelector, appInterpreter, ZeroXInstanceKeys.NONE);
    else if (pType.equals("oneCFA")) {
        builder = new nCFABuilder(1, cha, options, cache, appSelector, appInterpreter);
        ((PropagationCallGraphBuilder)builder).setInstanceKeys(new ZeroXInstanceKeys(options, cha, ((PropagationCallGraphBuilder)builder).getContextInterpreter(), ZeroXInstanceKeys.ALLOCATIONS
        | ZeroXInstanceKeys.SMUSH_MANY | ZeroXInstanceKeys.SMUSH_STRINGS
        | ZeroXInstanceKeys.SMUSH_THROWABLES));
    }
    else if (pType.equals("twoCFA")) {
        builder = new nCFABuilder(2, cha, options, cache, appSelector, appInterpreter);
        ((PropagationCallGraphBuilder)builder).setInstanceKeys(new ZeroXInstanceKeys(options, cha, ((PropagationCallGraphBuilder)builder).getContextInterpreter(), ZeroXInstanceKeys.ALLOCATIONS
        | ZeroXInstanceKeys.SMUSH_MANY | ZeroXInstanceKeys.SMUSH_STRINGS
        | ZeroXInstanceKeys.SMUSH_THROWABLES));
    }
  
    
    //Util.makeZeroOneContainerCFABuilder(options, cache, cha, scope);     
    cg = builder.makeCallGraph(options, null);

}

  private static Iterable<Entrypoint> makePublicEntrypoints(AnalysisScope scope, IClassHierarchy cha, String entryClass) 
  {
    Collection<Entrypoint> result = new ArrayList<Entrypoint>();
    System.out.println(StringStuff.deployment2CanonicalTypeString(entryClass));
    System.out.println(TypeReference.findOrCreate(ClassLoaderReference.Application,
        StringStuff.deployment2CanonicalTypeString(entryClass)));
    IClass klass = cha.lookupClass(TypeReference.findOrCreate(ClassLoaderReference.Application,
        StringStuff.deployment2CanonicalTypeString(entryClass)));
    for (IMethod m : klass.getDeclaredMethods()) 
    {
      System.out.println("Adding method " + m + " as an entry point");
      //if (m.isPublic()) {
        result.add(new DefaultEntrypoint(m, cha));
      //}
    }
    return result;
  }
  
  private static void addCallSites(CGNode node, SSAInstruction inst)
  {
    if (inst instanceof SSAInvokeInstruction) 
    {
      java.util.Set<CGNode> mnodes = cg.getNodes(((SSAInvokeInstruction)inst).getCallSite().getDeclaredTarget());
      for(CGNode n : mnodes)
      {
         addToSetOld(callSites, n, inst);
         //System.out.println("Call site for "  + node.getMethod().getName() + " (Instruction " + inst + " )");
      }
    }
  }
  
  private static void addToSetOld(HashMap<CGNode, HashSet<SSAInstruction>> oneToMany, CGNode key, SSAInstruction value) 
  {
    HashSet<SSAInstruction> set; 
    if (oneToMany.containsKey(key)) 
    {
      set  = (HashSet<SSAInstruction>) oneToMany.remove(key);
    }
    else 
    {
      //System.out.println("Call site for "  + key.getMethod().getName() + " (Instruction " + value + " )");
      set = new HashSet<SSAInstruction>();
      set.add(value);
      oneToMany.put(key, set);
    }
  }
  
  static CGNode transitivePredecessor(SSAInstruction inst, CGNode cur, HashSet<CGNode> visited) throws Exception 
  {  
      if (cur == null) 
      {
        return null;
      }
      if (visitedNodes.contains(cur)) 
      {
        //System.out.println("VISITED!");
        return null;
      }
      visitedNodes.add(cur);  
      System.out.println("FIRST PRED: " + cur);
      java.util.Iterator<CGNode> preds = cg.getPredNodes(cur);
      for(;preds.hasNext();) 
      {
        //CGNode res =  transitivePredecessor(inst, preds.next(), visitedNodes);
        CGNode res = preds.next();
        if (res != null)
        {
          System.out.println("PREDS: " + res);
          //return res; 
        }
      }
      return null;      
  }
  
  static boolean explorePredecessors(HashSet<IExplodedBasicBlock> visited, ExplodedControlFlowGraph graph, CGNode node, 
      SSAInstruction orig, IExplodedBasicBlock pred) {
          /*if (visited.contains(pred))
          {
            return false;
          }
          visited.add(pred);*/
          if (pred != null)
          {
            SSAInstruction cinst = pred.getInstruction();
            if (cinst instanceof SSAConditionalBranchInstruction)
            {
              SSAConditionalBranchInstruction ci = (SSAConditionalBranchInstruction) cinst;
              System.out.println("CONTROL STATEMENT: " + ci);
            }
          }
          else
          {
            java.util.Collection<IExplodedBasicBlock> preds = graph.getNormalPredecessors(pred);
            boolean foundConditional = false;
            for (IExplodedBasicBlock pr: preds)
            {
              if (explorePredecessors(visited, graph, node, orig, pr))
              {
                System.out.println("CONTROL STATEMENT: " + pr);
                foundConditional = true;
                return foundConditional;
              }
            }
          }
          return false;
  }
  
  public static Statement findCallTo(CGNode n, String methodName) 
  {
     if (targetClassNames != null && targetClassNames.indexOf(n.getMethod().getDeclaringClass().getName().toString()) < 0)
     {
       return null;  
     }

     IR ir = n.getIR();
     if (ir == null) 
     {
       return null;
     }
     for (Iterator<SSAInstruction> it = ir.iterateAllInstructions(); it.hasNext();)
     {
         SSAInstruction s = it.next();
         if (s instanceof com.ibm.wala.ssa.SSAAbstractInvokeInstruction) 
         {
             com.ibm.wala.ssa.SSAAbstractInvokeInstruction call = (com.ibm.wala.ssa.SSAAbstractInvokeInstruction) s;
             if (call.getCallSite().getDeclaredTarget().getName().toString().equals(methodName)) 
             {
                 com.ibm.wala.util.intset.IntSet indices = ir.getCallInstructionIndices(call.getCallSite());
                 com.ibm.wala.util.debug.Assertions.productionAssertion(indices.size() == 1, "expected 1 but got " + indices.size());
                 return new com.ibm.wala.ipa.slicer.NormalStatement(n, indices.intIterator().next());
             }
         }
     }
     //Assertions.UNREACHABLE("failed to find call to " + methodName + " in " + n);
     return null;
   }
  
  public static void dumpSlice(Statement seed, Collection<Statement> slice) 
  {
      for (Statement s : slice) 
      {
          if (s.getKind() == Statement.Kind.NORMAL_RET_CALLER) // ignore special kinds of statements
          {
             SSAAbstractInvokeInstruction inst = ((NormalReturnCaller)s).getInstruction();
             if (inst.getDeclaredTarget().getName().toString().indexOf("getInt") >= 0 
                 && (inst.getDeclaredTarget().getDeclaringClass().getName().toString().indexOf("Lorg/apache/hadoop/conf/Configuration") >=0 
                 || inst.getDeclaredTarget().getDeclaringClass().getName().toString().indexOf("Lorg/apache/hadoop/mapred/JobConf") >=0) 
                 && inst.getDeclaredTarget().getDescriptor().toString().indexOf("Ljava/lang/String;") >= 0) 
             {   
               System.out.println(s);
             }
             int bcIndex, instructionIndex = ((StatementWithInstructionIndex) s).getInstructionIndex();
             try {
                   bcIndex = ((ShrikeBTMethod) s.getNode().getMethod()).getBytecodeIndex(instructionIndex);
                   try {
                         int src_line_number = s.getNode().getMethod().getLineNumber(bcIndex);
                         System.out.println ( "Source line number = " + src_line_number + " in class " + s.getNode().getMethod().getDeclaringClass());
                   } 
                   catch (Exception e) 
                   {
                     System.out.println("Bytecode index no good" + " in class " + s.getNode().getMethod().getDeclaringClass());
                     System.out.println(e.getMessage());
                   }
             } 
             catch (Exception e)
             {
                 System.out.println("it's probably not a BT method (e.g. it's a fakeroot method)" + " in class " + s.getNode().getMethod().getDeclaringClass());
                 System.out.println(e.getMessage());
             } 
             }
          }
    }
  
}