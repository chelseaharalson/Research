package MyCode;

import java.io.File;
import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Iterator;
import java.util.Map.Entry;
import java.util.Properties;
import java.util.HashSet;
import java.util.HashMap;

import MyCode.AliasedLockOrder.Quad;
import MyCode.AliasedLockOrder.Triple;

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
import com.ibm.wala.ipa.callgraph.propagation.rta.CallSite;
import com.ibm.wala.ipa.callgraph.impl.DefaultEntrypoint;
import com.ibm.wala.ipa.callgraph.impl.ExplicitCallGraph;
import com.ibm.wala.ipa.callgraph.impl.Util;
import com.ibm.wala.ipa.callgraph.impl.Everywhere;
import com.ibm.wala.ipa.cfg.ExplodedInterproceduralCFG;
import com.ibm.wala.ipa.cha.ClassHierarchy;
import com.ibm.wala.ipa.cha.ClassHierarchyException;
import com.ibm.wala.ipa.cha.IClassHierarchy;
import com.ibm.wala.ipa.slicer.NormalReturnCaller;
import com.ibm.wala.ipa.slicer.NormalStatement;
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
import com.ibm.wala.ssa.SSAPutInstruction;
import com.ibm.wala.ssa.SSASwitchInstruction;
import com.ibm.wala.ssa.SymbolTable;
import com.ibm.wala.ssa.analysis.ExplodedControlFlowGraph;
import com.ibm.wala.ssa.analysis.IExplodedBasicBlock;
import com.ibm.wala.types.ClassLoaderReference;
import com.ibm.wala.types.TypeName;
import com.ibm.wala.types.TypeReference;
import com.ibm.wala.util.config.AnalysisScopeReader;
import com.ibm.wala.util.debug.Assertions;
import com.ibm.wala.util.graph.NumberedEdgeManager;
import com.ibm.wala.util.intset.IntSet;
import com.ibm.wala.util.intset.OrdinalSet;
import com.ibm.wala.util.intset.IntSetAction;
import com.ibm.wala.util.intset.IntIterator;
import com.ibm.wala.util.io.CommandLine;
import com.ibm.wala.util.strings.StringStuff;
import com.ibm.wala.util.warnings.Warnings;
import com.ibm.wala.ssa.ConstantValue;
import com.ibm.wala.analysis.typeInference.*;


public class HadoopAnalyzer_v2 {
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
  static Integer kDeep;
  static Integer kBranch;
  static Integer nodeCount;
  static Integer statementCount;
  
  // maps instructions to <cgnode,basicblock>
  static HashMap<SSAInstruction, Triple<Integer, CGNode, IExplodedBasicBlock>> instructionContext = new  HashMap<SSAInstruction, Triple<Integer, CGNode, IExplodedBasicBlock>>();
  
  static ArrayList<SSAInstruction> controlStatements = new ArrayList<SSAInstruction>();
  
  static ArrayList<SSAInstruction> newInstanceInstr = new ArrayList<SSAInstruction>();
  
  static HashMap<CGNode, HashSet<SSAInstruction>> callSites = new HashMap<CGNode, HashSet<SSAInstruction>>();

  static class Triple<T1, T2, T3> {

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
  if (p.getProperty("kDeep") == null)
    kDeep = 0;
  else
    kDeep = Integer.parseInt(p.getProperty("kDeep"));
  
  if (p.getProperty("kBranch") == null)
    kBranch = 0;
  else
    kBranch = Integer.parseInt(p.getProperty("kBranch"));
  

  pType = p.getProperty("pointerAnalysis"); 
  if (pType == null)
     pType = "zeroOneConCFA";
  // Format: Each line represents a separate statement specification
  // className;methodName;lineNo

  if (mainClass != null && entryClass != null) {
    throw new IllegalArgumentException("only specify one of mainClass or entryClass");
  }
  // use exclusions to eliminate certain library packages
  
  //System.out.println("kdeep: " + kDeep + "   kbranch: " + kBranch);

  if (targetClassNames == null)
System.out.println("WARNING: Analysis could be more efficient by specifying a semicolon separated list of target classes (excluding mainClass and entryClass) with -targetClassNames option (use / instead of . in class names)"); 

  System.out.println("building call graph...");
  configureAndCreateCallGraph(scopeFile, mainClass, entryClass); 

//  CallGraphBuilder builder = Util.makeNCFABuilder(2, options, cache, cha, scope);
//  CallGraphBuilder builder = Util.makeVanillaNCFABuilder(2, options, cache, cha, scope);


  pointerAnalysis = builder.getPointerAnalysis();
  heapModel = pointerAnalysis.getHeapModel();
  //System.out.println("Exploding the call graph.." + cg.getClass().getName());
   
  // Create the interprocedural control flow graph=======================================================
  icfg = ExplodedInterproceduralCFG.make(cg);
  ArrayList<SSAInstruction> seedInstr = new ArrayList<SSAInstruction>();
  ArrayList<Statement> seedStatements = new ArrayList<Statement>();
  
  Integer idx = 0;    
  for(CGNode node: icfg.getCallGraph()) 
  {
     idx++;
     SSAInstruction instr = findCallToInstr(node, "newInstance");
     if (instr != null)
     {
         seedInstr.add(instr);
     }
     
     if (!isATarget(node)) continue;
     ExplodedControlFlowGraph graph = (ExplodedControlFlowGraph) icfg.getCFG(node);
     
     if (graph == null) continue; 
     IR ir = node.getIR();
     
     if (ir == null) continue;
     SSAInstruction[] insts = ir.getInstructions();
     for(int i=0; i < insts.length; i++) 
     {
         SSAInstruction inst = insts[i];
         instructionContext.put(inst, new Triple(i, node, graph.getBlockForInstruction(i)));
         addCallSites(node, inst);
     }
  }
  
  nodeCount = 0;
  for(SSAInstruction st: seedInstr)
  {
    Triple<Integer, CGNode, IExplodedBasicBlock> contextInfo = instructionContext.get(st);
    CGNode stNode = (CGNode)contextInfo.val2;
    if (!isATarget(stNode)) continue;
    // Explore predecessors of the seed instructions
    explorePredecessorsInterProcedurally(0, 0, new HashSet<SSAInstruction>(), stNode, st);
  }
  
  //System.out.println("Control Statements Size: " + controlStatements.size());
  statementCount = 0;
  for(SSAInstruction si: controlStatements)
  {
    Triple<Integer, CGNode, IExplodedBasicBlock> contextInfo = instructionContext.get(si);
    CGNode siNode = (CGNode)contextInfo.val2;
    Statement statement = createStatement(siNode, "newInstance");
    if (statement != null)
    {
        if (!seedStatements.contains(statement))
        {
          seedStatements.add(statement);
        }
    }
  }
  

  Integer branchCount = 0;
  Collection<Statement> slice = null;
  System.out.println("Seed Statement Size: " + seedStatements.size());
  for (int i = 0; i < 50; i++)
  {
    for(Statement statement: seedStatements)
    {
        branchCount++;
        System.out.println("Slice Size: " + slice.size());
        ThinSlicer ts = new ThinSlicer(cg,pointerAnalysis);
        slice = ts.computeBackwardThinSlice (statement);
        System.out.println("Branch: " + branchCount + " << ");
        dumpSlice(statement, slice);
        System.out.println(" >>");
    }
    if (slice != null)
      seedStatements = new ArrayList<Statement>(slice);
  }
  
  System.out.println("The max node count is: " + nodeCount);
  System.out.println("The max statement count is: " + controlStatements.size());
  
  long end = System.currentTimeMillis();
  System.out.println("done");
  System.out.println("took " + (end-start) + "ms");
  System.out.println(CallGraphStats.getStats(cg));

}
  
  // Explore this particular node where methods are
  public static Integer explorePredecessors(Integer parentID, Integer kBranchCount, HashSet<SSAInstruction> visited, SSAInstruction orig)
  {
    Integer myID = parentID + 1;
    if (((kDeep > 0) && (myID > kDeep)) || ((kBranch > 0) && (kBranchCount >= kBranch)))
    {
      return kBranchCount;
    }
    if (visited.contains(orig))
    {
      return kBranchCount;
    }
    visited.add(orig);
    
    if (orig != null)
    {
      if (orig instanceof SSAConditionalBranchInstruction)
      {
        SSAConditionalBranchInstruction ci = (SSAConditionalBranchInstruction) orig;
        //if (!controlStatements.contains(ci))
        //{
          controlStatements.add(ci);
          kBranchCount++;
        //}
      }
      
      if (orig instanceof SSASwitchInstruction)
      {
        SSASwitchInstruction si = (SSASwitchInstruction) orig;
        //if (!controlStatements.contains(si))
        //{
          controlStatements.add(si);
          kBranchCount++;
        //}
      }
      
      // Loop through preds and then call function recursively on each one.. Explores the predecessors
      Triple<Integer, CGNode, IExplodedBasicBlock> contextInfo = instructionContext.get(orig);
      CGNode predNodes = (CGNode)contextInfo.val2;
      // Finds the call sites of the method
      Iterator<CGNode> preds = cg.getPredNodes(predNodes);
      
      while(preds.hasNext())
      {
        CGNode node = preds.next();
        if (!isATarget(node)) continue;
        ExplodedControlFlowGraph graph = (ExplodedControlFlowGraph) icfg.getCFG(node);
        if (graph == null) continue; 
        IR ir = node.getIR();
        if (ir == null) continue;
        SSAInstruction[] insts = ir.getInstructions();
        for(int i=0; i < insts.length; i++) 
        {
            SSAInstruction inst = insts[i];
            instructionContext.put(inst, new Triple(i, node, graph.getBlockForInstruction(i)));
            explorePredecessors(myID, kBranchCount, visited, inst);
        }
      }
    }
    return kBranchCount;
  }
  
  
  // Interprocedural control-flow analysis.. get to the next node where the method is called
  public static Integer explorePredecessorsInterProcedurally(Integer parentID, Integer kBranchCount, HashSet<SSAInstruction> visited, CGNode current, SSAInstruction inst)
  {
    Integer myID = parentID + 1;
    if (((kDeep > 0) && (myID > kDeep)) || ((kBranch > 0) && (kBranchCount >= kBranch)))
    {
      return kBranchCount;
    }

    if (visited.contains(inst))
    {
      return kBranchCount;
    }
    visited.add(inst);
    
    Triple<Integer, CGNode, IExplodedBasicBlock> contextInfo = instructionContext.get(inst);
    CGNode node = (CGNode)contextInfo.val2;
    IExplodedBasicBlock bb = (IExplodedBasicBlock)contextInfo.val3;
    ExplodedControlFlowGraph graph = (ExplodedControlFlowGraph) icfg.getCFG(node);
    if ((graph != null) && (bb != null))
    {
      Collection<IExplodedBasicBlock> preds = graph.getNormalPredecessors(bb);

      for(IExplodedBasicBlock pred : preds)
      {
        kBranchCount = explorePredecessors(0, kBranchCount, new HashSet<SSAInstruction>(), pred.getInstruction());
      }
    }
    
    Iterator<CGNode> preds2 = cg.getPredNodes(current);
    for(;preds2.hasNext();) 
    {
      nodeCount++;
      CGNode res = preds2.next();
      if (res != null)
      {
        IR ir = res.getIR();
        if (ir == null) continue;
        SSAInstruction[] insts2 = ir.getInstructions();
        // Find the call site where the current is called. res makes a call to current.
        // No loop.. pass call site as an instruction. Keep res.
        
        /*for(int i=0; i < insts2.length; i++) 
        {
            SSAInstruction inst2 = insts2[i];
            instructionContext.put(inst2, new Triple(i, node, graph.getBlockForInstruction(i)));
            kBranchCount = explorePredecessorsInterProcedurally(myID, kBranchCount, visited, res, inst2);
        }*/
        
        HashSet<SSAInstruction> csites = callSites.get(node);
        if (csites != null)
        {
          for(SSAInstruction csins: csites)
          {
            kBranchCount = explorePredecessorsInterProcedurally(myID, kBranchCount, visited, res, csins);
          }  
        }
      }
    }
    return kBranchCount;
  }
  
  
  public static SSAInstruction findCallToInstr(CGNode n, String methodName) 
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
         if (s instanceof SSAAbstractInvokeInstruction)
         {
           SSAAbstractInvokeInstruction call = (SSAAbstractInvokeInstruction) s;
           if (call.getCallSite().getDeclaredTarget().getName().toString().equals(methodName)) 
           {
             return s;
           }
         }
     }
     //Assertions.UNREACHABLE("failed to find call to " + methodName + " in " + n);
     return null;
   }
  
  
  private static void addCallSites(CGNode node, SSAInstruction inst) 
  {
    if (inst instanceof SSAInvokeInstruction) 
    {
      java.util.Set<CGNode> mnodes = cg.getNodes(((SSAInvokeInstruction)inst).getCallSite().getDeclaredTarget());
      OrdinalSet<? extends InstanceKey> lockSet = OrdinalSet.<InstanceKey>empty();
      //java.util.Set<CGNode> mnodes = getPossibleNodes(inst); 
      for(CGNode n : mnodes) 
         addToSetOld(callSites, n, inst);         
    }
  }
  
  
  private static void addToSetOld(HashMap<CGNode, HashSet<SSAInstruction>> oneToMany, CGNode key, SSAInstruction value)
  {
    HashSet<SSAInstruction> set; 
    if (oneToMany.containsKey(key)) 
      set  = (HashSet<SSAInstruction>) oneToMany.remove(key);
    else 
      set  = new HashSet<SSAInstruction>();
        set.add(value);
        oneToMany.put(key, set);
  }
  
  
  public static Statement createStatement(CGNode n, String methodName) 
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
         if (s instanceof SSAAbstractInvokeInstruction) 
         {
             SSAAbstractInvokeInstruction call = (SSAAbstractInvokeInstruction) s;
             if (call.getCallSite().getDeclaredTarget().getName().toString().equals(methodName)) 
             {
                 IntSet indices = ir.getCallInstructionIndices(call.getCallSite());
                 Assertions.productionAssertion(indices.size() == 1, "expected 1 but got " + indices.size());
                 return new NormalStatement(n, indices.intIterator().next());
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
               System.out.println();
               System.out.println(s);
               
             int bcIndex, instructionIndex = ((StatementWithInstructionIndex) s).getInstructionIndex();
             try {
                   bcIndex = ((ShrikeBTMethod) s.getNode().getMethod()).getBytecodeIndex(instructionIndex);
                   try {
                         int src_line_number = s.getNode().getMethod().getLineNumber(bcIndex);
                         System.out.println ( "Source line number = " + src_line_number + " in class " + s.getNode().getMethod().getDeclaringClass());
                         
                         SymbolTable tbl = s.getNode().getIR().getSymbolTable();
                         for (int i = 0; i < inst.getNumberOfParameters(); i++)
                         {
                           int paramValueNum = inst.getUse(i);
                           if (tbl.isStringConstant(paramValueNum)) 
                           {
                             String configParam = tbl.getStringValue(paramValueNum);
                             System.out.println("Configuration Parameters: " + configParam);
                           }
                         }
                   } 
                   catch (Exception e) 
                   {
                     System.out.println("Bytecode index no good" + " in class " + s.getNode().getMethod().getDeclaringClass());
                     System.out.println("ERROR: " + e.getMessage());
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
    AnalysisScope scope = AnalysisScopeReader.readJavaScope(scopeFile, exclusionsFile, HadoopAnalyzer_v2.class.getClassLoader()); 
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
      //System.out.println("Adding method " + m + " as an entry point");
      //if (m.isPublic()) {
        result.add(new DefaultEntrypoint(m, cha));
      //}
    }
    return result;
  }
  
}