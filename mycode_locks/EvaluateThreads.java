package mycode_locks;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.io.PrintWriter;
import java.io.UnsupportedEncodingException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import mycode_locks.FilterRisky.Double;
import mycode_locks.FilterRisky.Hex;
import mycode_locks.FilterRisky.Quad;
import mycode_locks.FilterRisky.Quint;
import mycode_locks.FilterRisky.Triple;

import com.ibm.wala.classLoader.IBytecodeMethod;
import com.ibm.wala.classLoader.IClass;
import com.ibm.wala.classLoader.IMethod;
import com.ibm.wala.ipa.callgraph.AnalysisCache;
import com.ibm.wala.ipa.callgraph.AnalysisOptions;
import com.ibm.wala.ipa.callgraph.AnalysisScope;
import com.ibm.wala.ipa.callgraph.CGNode;
import com.ibm.wala.ipa.callgraph.CallGraph;
import com.ibm.wala.ipa.callgraph.CallGraphBuilder;
import com.ibm.wala.ipa.callgraph.CallGraphBuilderCancelException;
import com.ibm.wala.ipa.callgraph.CallGraphStats;
import com.ibm.wala.ipa.callgraph.ContextSelector;
import com.ibm.wala.ipa.callgraph.Entrypoint;
import com.ibm.wala.ipa.callgraph.impl.DefaultEntrypoint;
import com.ibm.wala.ipa.callgraph.impl.Util;
import com.ibm.wala.ipa.callgraph.propagation.HeapModel;
import com.ibm.wala.ipa.callgraph.propagation.InstanceKey;
import com.ibm.wala.ipa.callgraph.propagation.PointerAnalysis;
import com.ibm.wala.ipa.callgraph.propagation.PropagationCallGraphBuilder;
import com.ibm.wala.ipa.callgraph.propagation.SSAContextInterpreter;
import com.ibm.wala.ipa.callgraph.propagation.cfa.ZeroXCFABuilder;
import com.ibm.wala.ipa.callgraph.propagation.cfa.ZeroXContainerCFABuilder;
import com.ibm.wala.ipa.callgraph.propagation.cfa.ZeroXInstanceKeys;
import com.ibm.wala.ipa.callgraph.propagation.cfa.nCFABuilder;
import com.ibm.wala.ipa.cfg.ExplodedInterproceduralCFG;
import com.ibm.wala.ipa.cha.ClassHierarchy;
import com.ibm.wala.ipa.cha.ClassHierarchyException;
import com.ibm.wala.ipa.cha.IClassHierarchy;
import com.ibm.wala.shrikeCT.InvalidClassFileException;
import com.ibm.wala.ssa.IR;
import com.ibm.wala.ssa.SSAAbstractInvokeInstruction;
import com.ibm.wala.ssa.SSAConditionalBranchInstruction;
import com.ibm.wala.ssa.SSAGetInstruction;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.ssa.SSAInvokeInstruction;
import com.ibm.wala.ssa.SSAMonitorInstruction;
import com.ibm.wala.ssa.SSASwitchInstruction;
import com.ibm.wala.ssa.analysis.ExplodedControlFlowGraph;
import com.ibm.wala.ssa.analysis.IExplodedBasicBlock;
import com.ibm.wala.types.ClassLoaderReference;
import com.ibm.wala.types.MethodReference;
import com.ibm.wala.types.TypeName;
import com.ibm.wala.types.TypeReference;
import com.ibm.wala.util.config.AnalysisScopeReader;
import com.ibm.wala.util.intset.OrdinalSet;
import com.ibm.wala.util.io.CommandLine;
import com.ibm.wala.util.strings.StringStuff;
import com.ibm.wala.util.warnings.Warnings;

public class EvaluateThreads {
  
  static class Triple<T1, T2, T3> {
    T1 val1;
    T2 val2;
    T3 val3;

     public Triple(T1 v1, T2 v2, T3 v3) {
       val1 = v1;
       val2 = v2;
       val3 = v3; 
     }      
  }
  
  static String pType;
  static String targetClassNames;
  static String mainClass;
  static String entryClass;
  static CallGraphBuilder builder;
  static IClassHierarchy cha;
  static CallGraph cg;
  static ExplodedInterproceduralCFG icfg;
  static PointerAnalysis pointerAnalysis; 
  static HeapModel heapModel;
  static String methodFile;
  
  // maps instructions to <cgnode,basicblock>
  static HashMap<SSAInstruction, Triple<Integer, CGNode, IExplodedBasicBlock>> instructionContext = new  HashMap<SSAInstruction, Triple<Integer, CGNode, IExplodedBasicBlock>>();
  
  static ArrayList<IClass> entryClasses = new  ArrayList<IClass>();
  
  //CGNode => HashSet<SSAInstruction>
  static HashMap<CGNode, HashSet<SSAInstruction>> callSites = new HashMap<CGNode, HashSet<SSAInstruction>>();
  static HashMap<CGNode, HashSet<CGNode>> callSitesForInvoke = new HashMap<CGNode, HashSet<CGNode>>();
  
  static HashMap<CGNode, HashSet<CGNode>> threadObjects = new HashMap<CGNode, HashSet<CGNode>>();
  
  public static void main(String[] args) throws Exception, IOException, ClassHierarchyException, IllegalArgumentException, CallGraphBuilderCancelException, InvalidClassFileException {
    long start = System.currentTimeMillis();
    Properties p = CommandLine.parse(args);
    methodFile = p.getProperty("methodFile");
    String scopeFile = p.getProperty("scopeFile");
    entryClass = p.getProperty("entryClass");
    mainClass = p.getProperty("mainClass");
    targetClassNames = p.getProperty("targetClassNames");
    
    if (methodFile == null) {
      throw new Exception("Program file must be provided!"); 
    }
    
    String[] method = parseMethodFile(methodFile);
    String m1 = method[0];
    String m2 = method[1];
    
    pType = p.getProperty("pointerAnalysis"); 
    if (pType == null)
       pType = "zeroOneConCFA";

    if (mainClass != null && entryClass != null) {
      throw new IllegalArgumentException("only specify one of mainClass or entryClass");
    }
    // use exclusions to eliminate certain library packages

    if (targetClassNames == null)
      System.out.println("WARNING: Analysis could be more efficient by specifying a semicolon separated list of target classes (excluding mainClass and entryClass) with -targetClassNames option (use / instead of . in class names)"); 


    System.out.println("Building call graph...");
    configureAndCreateCallGraph(scopeFile, mainClass, entryClass); 

    //      CallGraphBuilder builder = Util.makeNCFABuilder(2, options, cache, cha, scope);
    //      CallGraphBuilder builder = Util.makeVanillaNCFABuilder(2, options, cache, cha, scope);

    pointerAnalysis = builder.getPointerAnalysis();
    heapModel = pointerAnalysis.getHeapModel();
    //System.out.println("Exploding the call graph.." + cg.getClass().getName());
                    
    icfg = ExplodedInterproceduralCFG.make(cg);
    
    ArrayList<SSAInstruction> seedInstr = new ArrayList<SSAInstruction>();
    
    for(CGNode node: icfg.getCallGraph()) {
      if (!isATarget(node)) continue;
      ExplodedControlFlowGraph graph = (ExplodedControlFlowGraph) icfg.getCFG(node);
      
      if (graph == null) continue; 
      IR ir = node.getIR();
      
      if (ir == null || !(node.toString().indexOf("Application") >= 0) ) continue;
      SSAInstruction[] insts = ir.getInstructions();
      for(int i=0; i < insts.length; i++) {
          SSAInstruction inst = insts[i];
          instructionContext.put(inst, new Triple<Integer, CGNode, IExplodedBasicBlock>(i, node, graph.getBlockForInstruction(i)));
          addCallSites(node, inst);
          if (inst instanceof SSAInvokeInstruction) {
            java.util.Set<CGNode> nodes = cg.getNodes(((SSAInvokeInstruction)inst).getDeclaredTarget());
            for(CGNode targetnode : nodes) {
              addCallSitesForInvoke(targetnode, node);                
            }
          }
      }
   }
    
    for (SSAInstruction instr : instructionContext.keySet()) {
      if (instr != null) {
         //System.out.println("Found the seed instruction: " + prettyPrint(instr));
         seedInstr.add(instr);
         Triple<Integer, CGNode, IExplodedBasicBlock> contextInfo = instructionContext.get(instr);
         // Collect reachable nodes up to depth 
         int subgraphHeight = 4;
         collectAllReachableInSubGraph(instr, seedInstr, subgraphHeight);
      }
    }
    
    //System.out.println(threadObjects);
    analyzeThreadObjects(threadObjects, m1, m2);
     
    long end = System.currentTimeMillis();
    System.out.println("done");
    System.out.println("took " + (end-start) + "ms");
    System.out.println(CallGraphStats.getStats(cg));
  }
  
  public static String[] parseMethodFile(String fname) {
    String[] typeArray = null;
    BufferedReader br = null;
    try {
        String currentLine;
        br = new BufferedReader(new FileReader(fname));
        while ((currentLine = br.readLine()) != null) {
            typeArray = currentLine.split(";");
        }
      } catch (IOException e) {
        e.printStackTrace();
      } finally {
          try {
              if (br != null)br.close();
          } catch (IOException ex) {
              ex.printStackTrace();
          }
      }
    return typeArray;
  }
  
  private static void collectAllReachableInSubGraph(SSAInstruction inst,  ArrayList<SSAInstruction> list, int depth) throws InvalidClassFileException {
    Triple<Integer, CGNode, IExplodedBasicBlock> contextInfo = instructionContext.get(inst);
    CGNode node = contextInfo.val2;
    exploreSuccessors(list, node, depth);
  }
  
  private static void  exploreSuccessors(ArrayList<SSAInstruction> list, CGNode current, int depth) {
    IR ir = current.getIR();
    SSAInstruction[] insts = ir.getInstructions();
    for(int i=0; i<insts.length; i++) {
      if (i == insts.length - 1) 
        list.add(insts[i]);
      if (depth > 0) {
        
        // If the current node is a run method of a thread
        java.util.Iterator<CGNode> predsCG;
        if (current.getMethod().getName().toString().indexOf("run") >= 0 &&
            (cha.isSubclassOf(current.getMethod().getDeclaringClass(), cha.lookupClass(TypeReference.JavaLangThread)) ||
                cha.implementsInterface(current.getMethod().getDeclaringClass(), cha.lookupClass(TypeReference.findOrCreate(ClassLoaderReference.Application,
                    TypeName.string2TypeName("Ljava/lang/Runnable"))))
           )) {
            java.util.Set<CGNode> allStartNodesOfInterest = cg.getNodes(MethodReference.
                findOrCreate(ClassLoaderReference.Application,"Ljava/lang/Thread","start","()V"));
            for(CGNode nd : allStartNodesOfInterest) { 
              Iterator<CGNode> succs = cg.getSuccNodes(nd);
              //System.out.println("ND: " + nd);
              while (succs.hasNext()) {
                CGNode threadRun = succs.next();
                //System.out.println("THREAD RUN: " + threadRun);
                if (threadRun.getMethod().toString().indexOf(current.getMethod().getDeclaringClass().getName().toString()) >= 0)
                {
                  
                  if (insts[i] instanceof SSAInvokeInstruction && isInDesiredClass((SSAInvokeInstruction)insts[i])) {
                    MethodReference mr = ((SSAInvokeInstruction)insts[i]).getDeclaredTarget();
                          java.util.Set<CGNode> nodes = cg.getNodes(mr);
                          for(CGNode succno : nodes) {
                            //System.out.println("SUCC: " + succno);
                            addThreadObjects(threadRun, succno);
                            exploreSuccessors(list, succno, depth--);
                          }
                   }
                   
               }
              }
           }
        }
      }
    }
  }
  
  static void analyzeThreadObjects(HashMap<CGNode, HashSet<CGNode>> tobjects, String method1, String method2) {
    for (Map.Entry<CGNode, HashSet<CGNode>> entry : tobjects.entrySet()) {
      CGNode threadObj = entry.getKey();
      HashSet<CGNode> methods = entry.getValue();
      //System.out.println(threadObj + "    " + methods);
      for (CGNode methodNode : methods) {
        //System.out.println(threadObj + "     " + methodNode);
        if (methodNode.getMethod().getName().toString().equals(method1) || methodNode.getMethod().getName().toString().equals(method2)) {
          System.out.println(threadObj + "\t" + methodNode);
        }
      }
    }
  }

  static boolean isInDesiredClass(SSAInvokeInstruction inst) {
    TypeReference cl = inst.getDeclaredTarget().getDeclaringClass();
        //System.out.println("Is " + cl.getName() + " a desired type?");
        for(IClass ecl : entryClasses) {
        //System.out.println("Checking against " + ecl.getName().toString());
        if (ecl.getName().toString().indexOf(cl.getName().toString()) >= 0)
          return true;
         }  
          return false;  
    } 
  
  private static void addCallSites(CGNode node, SSAInstruction inst) {
    if (inst instanceof SSAInvokeInstruction) {
              java.util.Set<CGNode> mnodes = cg.getNodes(((SSAInvokeInstruction)inst).getCallSite().getDeclaredTarget());
              OrdinalSet<? extends InstanceKey> lockSet = OrdinalSet.<InstanceKey>empty();
              //java.util.Set<CGNode> mnodes = getPossibleNodes(inst); 
              for(CGNode n : mnodes) 
                 addToSetOld(callSites, n, inst);         
    }
  }
  
  private static void addCallSitesForInvoke(CGNode targetNode, CGNode node) {
    HashSet<CGNode> callsites = callSitesForInvoke.remove(targetNode);
    if (callsites == null) callsites = new HashSet<CGNode>();
    callsites.add(node);
    callSitesForInvoke.put(targetNode, callsites);
 }
  
  private static void addToSetOld(HashMap<CGNode, HashSet<SSAInstruction>> oneToMany, CGNode key, SSAInstruction value) {
    HashSet<SSAInstruction> set; 
    if (oneToMany.containsKey(key)) 
        set  = (HashSet<SSAInstruction>) oneToMany.remove(key);
    else 
        set  = new HashSet<SSAInstruction>();
          set.add(value);
          oneToMany.put(key, set);
  }
  
  
  private static void addThreadObjects(CGNode targetNode, CGNode node) {
    HashSet<CGNode> tsites = threadObjects.remove(targetNode);
    if (tsites == null) tsites = new HashSet<CGNode>();
    tsites.add(node);
    threadObjects.put(targetNode, tsites);
  }
  
  private static String prettyPrint(SSAInstruction inst) {
    //if (inst instanceof SSAInvokeInstruction)
    //  return inst.toString();
    Triple<Integer, CGNode, IExplodedBasicBlock> contextInfo = instructionContext.get(inst);
    int instIndex = contextInfo.val1.intValue();
    CGNode node = contextInfo.val2;        
    String instSt = inst.toString();
    int pos = instSt.indexOf("(");
    if (pos >= 0)
       instSt = instSt.substring(0,pos); 
    return instSt + " " + prettyPrint(node.getIR(), instIndex);  
  }
  
  private static String prettyPrint(IR ir, int instIndex) {
    String result="";
    try {
      IBytecodeMethod method = (IBytecodeMethod)ir.getMethod();
      IClass decclass =  method.getDeclaringClass();
      int bytecodeIndex = method.getBytecodeIndex(instIndex);
      int sourceLineNum = method.getLineNumber(bytecodeIndex);   
      result ="line " + sourceLineNum + " in " + (decclass.getSourceFileName() == null ? decclass.getName() : decclass.getSourceFileName());
    }
    catch(InvalidClassFileException e) {
       System.out.println(e);
       }
    catch(ClassCastException e) {
      result = "Fake class and method";
    }
    return result;
  }
  
  private static boolean isATarget(CGNode node) {
    String className = node.getMethod().getDeclaringClass().getName().toString(); 
    if (mainClass != null && className.indexOf(mainClass) >= 0)
      return true;
    if (entryClass != null && isAnEntryClass(className))
      return true;  
    if (targetClassNames == null) // All classes will be analyzed
      return true; 
    String[] targetClassName = targetClassNames.split(";");        
    for(int i=0; i < targetClassName.length; i++) {
      if (className.indexOf(targetClassName[i]) >= 0)
        return true;
    }
    return false; 
  }
  
  private static boolean isAnEntryClass(String name) {
    String[] entryClassName = entryClass.split(";");
    for(int i=0; i < entryClassName.length; i++)
       if (name.indexOf(entryClassName[i]) >= 0)
          return true;
    return false;
  }
  
  private static void configureAndCreateCallGraph(String scopeFile, String mainClass, String entryClass) throws IOException, ClassHierarchyException, CallGraphBuilderCancelException  {
      File exclusionsFile = null;
      AnalysisScope scope = AnalysisScopeReader.readJavaScope(scopeFile, exclusionsFile, EvaluateThreads.class.getClassLoader()); 
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
      ContextSelector appSelector = new ThreadSensContextSelector();
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
  
  private static Iterable<Entrypoint> makePublicEntrypoints(AnalysisScope scope, IClassHierarchy cha, String entryClass) {
      Collection<Entrypoint> result = new ArrayList<Entrypoint>();
      System.out.println(StringStuff.deployment2CanonicalTypeString(entryClass));
      System.out.println(TypeReference.findOrCreate(ClassLoaderReference.Application,
          StringStuff.deployment2CanonicalTypeString(entryClass)));
      IClass klass = cha.lookupClass(TypeReference.findOrCreate(ClassLoaderReference.Application,
          StringStuff.deployment2CanonicalTypeString(entryClass)));
      entryClasses.add(klass);
      for (IMethod m : klass.getDeclaredMethods()) {
        System.out.println("Adding method " + m + " as an entry point");
        //if (m.isPublic()) {
          result.add(new DefaultEntrypoint(m, cha));
        //}
      }
      return result;
  }

}
