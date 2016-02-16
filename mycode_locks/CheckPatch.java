package mycode_locks;

import java.io.File;
import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Iterator;
import java.util.Properties;
import java.util.HashSet;
import java.util.Set;
import com.google.common.collect.HashMultiset;
import com.ibm.wala.classLoader.IBytecodeMethod;
import com.ibm.wala.classLoader.IClass;
import com.ibm.wala.classLoader.IMethod;
import com.ibm.wala.classLoader.IField; 
import com.ibm.wala.classLoader.CallSiteReference;
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
import com.ibm.wala.analysis.typeInference.TypeInference;
import com.ibm.wala.shrikeCT.InvalidClassFileException; 
import com.ibm.wala.ssa.IR;
import com.ibm.wala.ssa.SSACFG;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.ssa.SSAGetInstruction;
import com.ibm.wala.ssa.SSAFieldAccessInstruction;
import com.ibm.wala.ssa.SSAMonitorInstruction;
import com.ibm.wala.ssa.SSAInvokeInstruction;
import com.ibm.wala.ssa.analysis.ExplodedControlFlowGraph;
import com.ibm.wala.ssa.analysis.IExplodedBasicBlock;
import com.ibm.wala.shrikeBT.*;
import com.ibm.wala.types.ClassLoaderReference;
import com.ibm.wala.types.TypeName;
import com.ibm.wala.types.TypeReference;
import com.ibm.wala.types.MethodReference;
import com.ibm.wala.util.config.AnalysisScopeReader;
import com.ibm.wala.util.graph.NumberedEdgeManager;
import com.ibm.wala.util.intset.IntSet;
import com.ibm.wala.util.intset.OrdinalSet;
import com.ibm.wala.util.intset.IntSetAction;
import com.ibm.wala.util.intset.IntIterator;
import com.ibm.wala.util.io.CommandLine;
import com.ibm.wala.util.strings.StringStuff;
import com.ibm.wala.util.warnings.Warnings;


import java.util.HashMap;
/**
 * Driver that constructs a call graph for an application specified via a scope file.  
 * Useful for getting some code to copy-paste.    
 */
public class CheckPatch {

    static String searchDirection = " ";
    static boolean SUBCLASS_HANDLING = false;
    // Should read this from the command line
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
    // maps locking instructions to the the points-to set of the locks acquired
    static HashMap<SSAInstruction,OrdinalSet<? extends InstanceKey>>  lockingInstructions = new HashMap<SSAInstruction,OrdinalSet<? extends InstanceKey>>(); 

    static ArrayList<CGNode> lockingMethods = new ArrayList<CGNode>();
    //  SSAInstruction => HashSet<SSAInstruction
    //static HashMap<Object,HashSet<Object>> reachesLocking = new HashMap<Object,HashSet<Object>>();

     //  SSAInstruction => HashSet<SSAInstruction
    //static HashMap<Object,HashSet<Object>> reachedBy = new HashMap<Object,HashSet<Object>>();   

    // maps instructions to <cgnode,basicblock>
    static HashMap<SSAInstruction, Triple<Integer, CGNode, IExplodedBasicBlock>> instructionContext = new  HashMap<SSAInstruction, Triple<Integer, CGNode, IExplodedBasicBlock>>();
    //  CGNode => HashSet<SSAInstruction>
    static HashMap<CGNode, HashSet<SSAInstruction>> callSites = new HashMap<CGNode, HashSet<SSAInstruction>>();

    // SSAInstruction =>  HashSet<SSAInstruction>
    static HashMap<SSAInstruction, HashSet<SSAInstruction>> enclosedBy = new  HashMap<SSAInstruction, HashSet<SSAInstruction>>();

    static HashMap<SSAInstruction, HashSet<SSAInstruction>> enclosedByRegular = new HashMap<SSAInstruction, HashSet<SSAInstruction>>();

    static  HashMap<SSAInstruction, HashSet<SSAInstruction>> enclosedByReverse = new HashMap<SSAInstruction, HashSet<SSAInstruction>>();

    // SSAInstruction =>  HashSet<SSAInstruction>
    static HashMap<SSAInstruction, HashSet<SSAInstruction>> encloses = new HashMap<SSAInstruction, HashSet<SSAInstruction>>();  

    static HashMap<SSAInstruction, HashSet<SSAInstruction>> enclosesRegular = new HashMap<SSAInstruction, HashSet<SSAInstruction>>();

    static HashMap<SSAInstruction, HashSet<SSAInstruction>> enclosesReverse = new HashMap<SSAInstruction, HashSet<SSAInstruction>>();

    static HashMap<String, HashSet<Quad>> revAliasedEnclPairs = new HashMap<String, HashSet<Quad>>();

    static  HashMap<SSAInstruction, HashSet<SSAInstruction>> reachesLocking = new  HashMap<SSAInstruction, HashSet<SSAInstruction>>();

    static HashMap<SSAInstruction, HashSet<CGNode>> reachedByMethod = new HashMap<SSAInstruction, HashSet<CGNode>>();

    static HashMap<SSAInstruction, HashSet<CGNode>> reachedByRunMethod = new HashMap<SSAInstruction, HashSet<CGNode>>();   

    // KeyInstruction -> CGNode -> BasicBlock -> Set of ThreadClasses
    static HashMap<SSAInstruction, HashMap<CGNode, HashMap<IExplodedBasicBlock, HashSet<IClass>>>> reachingThreadStart = new HashMap<SSAInstruction, HashMap<CGNode, HashMap<IExplodedBasicBlock, HashSet<IClass>>>>();

    static HashMap<Quad, HashMap<Triple<CGNode, IExplodedBasicBlock, IExplodedBasicBlock>, Integer>> pairRank = new HashMap<Quad, HashMap<Triple<CGNode, IExplodedBasicBlock, IExplodedBasicBlock>, Integer>>();

    // Class whose methods can be reflectively called ->  via Thread Class IClass -> in method CGNode at basicblock  IExplodedBasicBlock 
    static HashMap<IClass, HashMap<IClass, HashSet<Pair<CGNode, IExplodedBasicBlock>>>> calledViaReflection = new HashMap<IClass,  HashMap<IClass, HashSet<Pair<CGNode, IExplodedBasicBlock>>>>();

    // Class whose methods can be reflectively called -> in class, by method, at line, by thread class
    static HashMap<IClass, HashSet<Quad>> reflectionInfo = new HashMap<IClass, HashSet<Quad>>();

    static HashMap<Quad, Integer> rankPerReverseAlias = new HashMap<Quad, Integer>();    

    static ArrayList<Quad> reverseAliasedPairs = new ArrayList<Quad>();

    static String enclosingClass;

    static String enclosingInstruction;

    static String enclosedInstruction;

    static String enclosedClass;

    static String enclosedMethod;

    static String enclosingType;

    static String enclosingTypeTrimmed;

    static String enclosedTypeTrimmed;

    static String enclosedType;

    static String enclosingLineNo;

    static String enclosedLineNo;

    static SSAInstruction seedInstruction;

    static int totalNumPairs = 0;
 
    static int numPublicPairs = 0;

    // We need this to use in isAssignableFrom. Usin the full class name did not work!
    static Class ssaInvokeInstructionClass = null;

    static  class Pair<T1, T2> {

   T1 val1;
   T2 val2;

         public Pair(T1 v1, T2 v2) {
       val1 = v1;
             val2 = v2;
   }      

         public boolean equals(Pair p) {
       return (val1 == p.val1 && val2 == p.val2) || (val1.equals(p.val1) && val2.equals(p.val2));
   }
    }

    static  class Triple<T1, T2, T3> {

   T1 val1;
   T2 val2;
         T3 val3;

         public Triple(T1 v1, T2 v2, T3 v3) {
       val1 = v1;
             val2 = v2;
             val3 = v3; 
   }      
    }  

    static  class Quad {

   Object val1;
   Object val2;
         Object val3;
  Object val4; 

  public Quad(Object v1, Object v2, Object v3, Object v4) {
       val1 = v1;
             val2 = v2;
             val3 = v3; 
             val4 = v4;
   }      

        boolean sameAs(Quad q) {
      return (same((SSAInstruction)val1, (SSAInstruction)q.val1) && same((SSAInstruction)val2, (SSAInstruction)q.val2) && same((SSAInstruction)val3, (SSAInstruction)q.val3) && same((SSAInstruction)val4, (SSAInstruction)q.val4));
  }
 

    }    


   static boolean commonLockSet(OrdinalSet<? extends InstanceKey> lockset1, OrdinalSet<? extends InstanceKey> lockset2) {
        for(java.util.Iterator<? extends InstanceKey> ikeys1 = lockset1.iterator(); ikeys1.hasNext();) {
            InstanceKey is1 = ikeys1.next();
            for(java.util.Iterator<? extends InstanceKey> ikeys2 = lockset2.iterator(); ikeys2.hasNext();) {
               InstanceKey is2 = ikeys2.next();
               if (is1.toString().equals(is2.toString()) && is1.toString().indexOf("FakeRootClass")<0) {
       return true;
         } 
            }
        }       
        return false;
   }

   static String lockSetToString(OrdinalSet<? extends InstanceKey> lockset) {
       String result = "";
       for(java.util.Iterator<? extends InstanceKey> ikeys = lockset.iterator(); ikeys.hasNext();) {
            InstanceKey is = ikeys.next();
            result = result + is + " " + is.hashCode(); 
        }
       return result;
   }

   static void readReflectionInfo(String targetFile) throws Exception, IOException{
        BufferedReader bufR = new BufferedReader(new FileReader(targetFile));
        String line; 
        int no = 0;
        int lineNo = 0;
        while ((line = bufR.readLine()) != null) {
            if (line.indexOf("reflectionHint") >= 0) {
               String[] sa = line.substring(line.indexOf("=")+1, line.length()).split(";");
               if (sa.length != 5)
                throw new Exception("Expected: Reflection Hint: classname;methodname;lineno;threadClass;callsMethodsOfClass"); 
               addToSet(reflectionInfo, cha.lookupClass(TypeReference.findOrCreate(ClassLoaderReference.Application,
                                                                                    StringStuff.deployment2CanonicalTypeString(sa[4].substring(1)))), 
                    new Quad(sa[0], sa[1], sa[2], sa[3]));  
            }
        }
        bufR.close();
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

    pType = p.getProperty("pointerAnalysis"); 
    if (pType == null)
       pType = "zeroOneConCFA";
    // Format: Each line represents a separate statement specification
    // className;methodName;lineNo
    String targetFile = p.getProperty("targetFile");
    if (targetFile == null)
  throw new Exception("target file must be provided!"); 
    if (mainClass != null && entryClass != null) {
      throw new IllegalArgumentException("only specify one of mainClass or entryClass");
    }
    // use exclusions to eliminate certain library packages

    if (targetClassNames == null)
  System.out.println("WARNING: Analysis could be more efficient by specifying a semicolon separated list of target classes (excluding mainClass and entryClass) with -targetClassNames option (use / instead of . in class names)"); 


    System.out.println("building call graph...");
    configureAndCreateCallGraph(scopeFile, mainClass, entryClass); 

//    CallGraphBuilder builder = Util.makeNCFABuilder(2, options, cache, cha, scope);
//    CallGraphBuilder builder = Util.makeVanillaNCFABuilder(2, options, cache, cha, scope);


 

    pointerAnalysis = builder.getPointerAnalysis();
    heapModel = pointerAnalysis.getHeapModel();
    //System.out.println("Exploding the call graph.." + cg.getClass().getName());
                    
    icfg = ExplodedInterproceduralCFG.make(cg);

    readReflectionInfo(targetFile);
 
    for(CGNode node: icfg.getCallGraph()) { 
        //if (!isATarget(node)) continue; 
  ExplodedControlFlowGraph graph = (ExplodedControlFlowGraph)  icfg.getCFG(node);

        if (graph == null) continue; 
        IR ir = node.getIR();
        if (ir == null) continue;
        SSAInstruction[] insts = ir.getInstructions();
        for(int i=0; i < insts.length; i++) {
            SSAInstruction inst = insts[i];
            if (ssaInvokeInstructionClass == null && inst instanceof SSAInvokeInstruction) {
               ssaInvokeInstructionClass = inst.getClass();
               System.out.println("ssaInvokeInstructionClass = " + ssaInvokeInstructionClass);
            }
            instructionContext.put(inst, new Triple(i, node, graph.getBlockForInstruction(i)));
            addCallSites(node, inst);
            if (inst instanceof SSAInvokeInstruction) {
    if (((SSAInvokeInstruction)inst).getDeclaredTarget().getName().toString().indexOf("start") >= 0) {
                   System.out.println("MAY BE A REFLECTIVE THREAD START in NODE " + node);  
        HashSet<IClass> clset = getClassesCanBeCalledByReflectiveThread(((SSAInvokeInstruction)inst).getDeclaredTarget().getDeclaringClass().getName().toString());
                   for(IClass cl : clset) {
           addToSet(calledViaReflection, cl, cha.lookupClass(((SSAInvokeInstruction)inst).getDeclaredTarget().getDeclaringClass()), node, graph.getBlockForInstruction(i));
       }
          }
      }
  
  }
    }

    initLockingInstructions(targetFile);
   
    System.out.println("ALL LOCKING INSTRUCTIONS: ");
    java.util.Set<SSAInstruction> keys = lockingInstructions.keySet();
    for(SSAInstruction inst: keys) {
  System.out.println(prettyPrint(inst) + " LOCK Points To Sets\n ");
        OrdinalSet<? extends InstanceKey> lockset =   lockingInstructions.get(inst);
        for(java.util.Iterator<? extends InstanceKey> ikeys = lockset.iterator(); ikeys.hasNext();) {
            InstanceKey is = ikeys.next();
      System.out.println(is + " " + is.hashCode()); 
  }
    }

    reachabilityAnalysis();

    System.out.println("ORIGINAL ENCLOSING PAIR of LOCKING INSTRUCTIONS:");  
    assert(enclosedBy.size() == encloses.size());
    java.util.Set<SSAInstruction> e1 = enclosedBy.keySet();
    for(SSAInstruction syncInst : e1) {
        HashSet<SSAInstruction> enclosedSet = enclosedBy.get(syncInst);
        for(SSAInstruction eInst: enclosedSet) {
      System.out.println(prettyPrint((SSAInstruction)eInst) + " ENCLOSES " + prettyPrint((SSAInstruction)syncInst)); 
  } 
    }

    collectEnclosingPairs();

    HashMap<SSAInstruction, HashSet<SSAInstruction>> enclosesRegularFocus, enclosesReverseFocus;

    enclosesReverseFocus = new HashMap<SSAInstruction, HashSet<SSAInstruction>>();       
    enclosesRegularFocus =  new HashMap<SSAInstruction, HashSet<SSAInstruction>>(); 

    System.out.println("INITIAL regularFocus size=" + enclosesRegularFocus.size() + " reverseFocus size=" + enclosesReverseFocus.size());
    System.out.println("Reference point=" + enclosedClass + "," + " " + enclosedInstruction + " line " +  enclosedLineNo);

    int totalPairs = 0;
    int publicEncPairs = 0;
    System.out.println("ENCLOSING PAIR of LOCKING INSTRUCTIONS:");  
    java.util.Set<SSAInstruction> enclosing = enclosesRegular.keySet();
    for(SSAInstruction syncInst : enclosing) {
        HashSet<SSAInstruction> enclosedSet = enclosesRegular.get(syncInst);
        for(SSAInstruction eInst: enclosedSet) {
            totalPairs++;
            boolean ispb = isPublic((SSAInstruction)eInst);
            if (ispb) publicEncPairs++;
            // Filter the enclosing pair that we're interested in checking for deadlock
            if (searchDirection.equals("pre") && isRefPoint(syncInst)) {
           System.out.println(((ispb == true ) ? "[PUBLIC]" : "") + prettyPrint((SSAInstruction)syncInst) + " ENCLOSES " + prettyPrint((SSAInstruction)eInst));  
               addToSet(enclosesRegularFocus, syncInst, eInst);             
            }
  } 
    }
    System.out.println("Total number of pairs=" + totalPairs);
    System.out.println("# of Public enclosing pairs=" + publicEncPairs);

 
    totalPairs = 0;
    publicEncPairs = 0;
    System.out.println("ENCLOSING PAIR of REVERSE LOCKING INSTRUCTIONS:");  
    enclosing = enclosesReverse.keySet();
    for(SSAInstruction syncInst : enclosing) {
        HashSet<SSAInstruction> enclosedSet = enclosesReverse.get(syncInst);
        for(SSAInstruction eInst: enclosedSet) {
            totalPairs++;
            boolean ispb = isPublic((SSAInstruction)eInst);
            if (ispb) publicEncPairs++;
            // Filter the enclosing pair that we're interested in checking for deadlock
            if (searchDirection.equals("onward") && isRefPoint(syncInst)) {
               System.out.println(((ispb == true ) ? "[PUBLIC]" : "") + prettyPrint((SSAInstruction)syncInst) + " ENCLOSES " + prettyPrint((SSAInstruction)eInst)); 
               addToSet(enclosesReverseFocus, syncInst, eInst);
            }
        } 
    }
    System.out.println("Total number of pairs=" + totalPairs);
    System.out.println("# of Public enclosing pairs=" + publicEncPairs);

    if (searchDirection.equals("onward")) {
       enclosesRegularFocus = enclosesRegular;
    }
    else if  (searchDirection.equals("pre")) {
       enclosesReverseFocus =  enclosesReverse;    
    }
    else throw new Exception("Unknown search direction!");

    System.out.println("regularFocus size=" + enclosesRegularFocus.size() + " reverseFocus size=" + enclosesReverseFocus.size());
    
    computeReverseAliasedEnclosingPairs(enclosesRegularFocus, enclosesReverseFocus);

    /*System.out.println("Checking those that may run in parallel");
    rankReverseAliasedMayRunInParallel();

    printRST();*/
      
    long end = System.currentTimeMillis();
    System.out.println("done");
    System.out.println("took " + (end-start) + "ms");
    System.out.println(CallGraphStats.getStats(cg));

  }

  static boolean isRefPoint(SSAInstruction inst) {
             
      String expectedSignature = null;

      if (enclosedInstruction.indexOf("monitorenter")>=0)
         expectedSignature = enclosedClass + "," + " " + enclosedInstruction + " line " +  enclosedLineNo ;
      else {
    if (searchDirection.equals("pre"))
              expectedSignature = enclosingTypeTrimmed + "," + " " + enclosedInstruction + " line " +  enclosedLineNo ;
    else if (searchDirection.equals("onward"))
              expectedSignature = enclosedTypeTrimmed + "," + " " + enclosedInstruction + " line " +  enclosedLineNo ;
      }

      String instSignature = prettyPrint(inst);

     return (instSignature.indexOf(expectedSignature) >= 0);
  
  }

  static HashSet<IClass> getClassesCanBeCalledByReflectiveThread(String className) {
      HashSet<IClass> result = new HashSet<IClass>();
      java.util.Set<IClass> keySet = reflectionInfo.keySet();
      for(IClass key : keySet) {
    HashSet<Quad> qset = reflectionInfo.get(key);
          for(Quad q:qset) {
              System.out.println("Does " + q.val4 + " CONTAIN " + className + " ?");
        if (className.indexOf((String)q.val4) >= 0)
      result.add(key);  
    }  
      }
      return result;
  }


 
  static void addReflection(IClass cl, SSAInstruction inst) {
      if (inst instanceof SSAInvokeInstruction) {
         java.util.Set<IClass> clks = calledViaReflection.keySet();
         for(IClass cl1 : clks) {
            if (cl1.getName().toString().equals(((SSAInvokeInstruction)inst).getDeclaredTarget().getDeclaringClass().getName().toString()))  {
            HashMap<IClass, HashSet<Pair<CGNode, IExplodedBasicBlock>>> ref = calledViaReflection.get(cl1);
      java.util.Set<IClass> keySet = ref.keySet();
            for(IClass key : keySet) {
    HashSet<Pair<CGNode, IExplodedBasicBlock>> ninfoSet = ref.get(key);
    for(Pair<CGNode, IExplodedBasicBlock> p : ninfoSet) {
       addToSet(reachedByMethod, inst, p.val1);
                   HashSet<IClass> cset = new HashSet<IClass>();
                   cset.add(key);
                   addAllToMap(reachingThreadStart, inst, p.val1, p.val2, cset);
    }
      }
            }
   }
      }
  }

  static boolean notSame(HashSet<IClass> s1, HashSet<IClass> s2) {
     for(IClass c1 : s1) {
       boolean found = false;
       for(IClass c2 : s2) 
         if (c1.getName().equals(c2.getName())) {
            found = true; 
            break;
         }
      if (!found)
         return true; 
     } 

     for(IClass c2 : s2) { 
       boolean found = false;
       for(IClass c1 : s1) 
         if (c1.getName().equals(c2.getName())) {
            found = true; 
            break;
         }
      if (!found)
         return true; 
     } 
     return false;
  }


   static boolean isMethodCallingMethodOfClass(CGNode n1, CGNode n2, String className) {
    HashSet<SSAInstruction> csSet = callSites.get(n2);
    if (csSet == null) return false;
    for(SSAInstruction cs: csSet) {
       Triple<Integer, CGNode, IExplodedBasicBlock> context = instructionContext.get(cs);
       if (context.val2 == n1) {
          Iterator<CGNode> succs = cg.getSuccNodes(n2);
          while (succs.hasNext()) {
              CGNode threadRun = succs.next();
              System.out.println("SUCCESSOR=" + threadRun + " OF " + n2); 
              if (threadRun.getMethod().getSignature().indexOf(className) < 0)
                 return false;
          }
          return true;
       }
    }
    return false;
  }

  static HashSet<IExplodedBasicBlock> findBasicBlockForMethodCallingMethod(CGNode n1, CGNode n2) {
    HashSet<IExplodedBasicBlock> result = new HashSet<IExplodedBasicBlock>();
    HashSet<SSAInstruction> csSet = callSites.get(n2);
    if (csSet == null) return result;
    for(SSAInstruction cs: csSet) {
       Triple<Integer, CGNode, IExplodedBasicBlock> context = instructionContext.get(cs);
       if (context.val2.equals(n1)) // safer than == check
     result.add((IExplodedBasicBlock)context.val3);
    }
    return result;
  }


    static  boolean isPredecessor(CGNode node, IExplodedBasicBlock bb1, IExplodedBasicBlock bb2) {
        return isPredecessor(node, bb1, bb2, new HashSet<IExplodedBasicBlock>());
    }

  static  boolean isPredecessor(CGNode node, IExplodedBasicBlock bb1, IExplodedBasicBlock bb2, HashSet<IExplodedBasicBlock> visited) {
        if (visited.contains(bb1))
           return false;
        visited.add(bb1);
        if (bb1 == bb2) return true;
        ExplodedControlFlowGraph graph = (ExplodedControlFlowGraph)  icfg.getCFG(node);
        java.util.Collection<IExplodedBasicBlock> succs =graph.getNormalSuccessors(bb1);       
        for(IExplodedBasicBlock  succ : succs) {    
           if (isPredecessor(node, succ, bb2, visited))
              return true; 
        }
        return false;
  }

  static  boolean isPredecessor(CGNode node, IExplodedBasicBlock bb1, HashSet<IExplodedBasicBlock> s2, HashSet<IExplodedBasicBlock> visited) {
        if (visited.contains(bb1))
           return false;
        visited.add(bb1);
        if (s2.contains(bb1)) return true;
        ExplodedControlFlowGraph graph = (ExplodedControlFlowGraph)  icfg.getCFG(node);
        java.util.Collection<IExplodedBasicBlock> succs =graph.getNormalSuccessors(bb1);       
        for(IExplodedBasicBlock  succ : succs) {    
           if (isPredecessor(node, succ, s2, visited))
              return true; 
        }
        return false;
  }


  static  boolean isSuccessor(CGNode node, IExplodedBasicBlock bb1, HashSet<IExplodedBasicBlock> s2, HashSet<IExplodedBasicBlock> visited) {
        if (visited.contains(bb1))
           return false;
        visited.add(bb1);
        if (s2.contains(bb1)) return true;
        ExplodedControlFlowGraph graph = (ExplodedControlFlowGraph)  icfg.getCFG(node);
        java.util.Collection<IExplodedBasicBlock> preds =graph.getNormalPredecessors(bb1);       
        for(IExplodedBasicBlock  pred : preds) {    
           if (isSuccessor(node, pred, s2, visited)) 
              return true; 
        }
        return false;
  }

    /* each bb1 in s1 predecessor of some bb2 in s2 */
  static boolean allPredecessor(CGNode node, HashSet<IExplodedBasicBlock> s1, HashSet<IExplodedBasicBlock> s2) {
      for(IExplodedBasicBlock bb1 : s1) {
         if (!isPredecessor(node, bb1, s2, new HashSet<IExplodedBasicBlock>()))
            return false;  
      }           
      for(IExplodedBasicBlock bb2 : s2) {
         if (!isSuccessor(node, bb2, s1, new HashSet<IExplodedBasicBlock>()))
            return false;  
      }           
      return true; 
  }


  static void printRef() {
   System.out.println("CONTENTS OF  ReflectionInfo");
   java.util.Set<IClass> s = reflectionInfo.keySet();
   for(IClass c : s) {
     System.out.println("Methods of class =" + c.getName().toString());
     HashSet<Quad> qs = reflectionInfo.get(c);
     for(Quad q:qs) {
       System.out.println("\t " + q.val1 + " " + q.val2 + " " + q.val3 + " " + q.val4);
     }
   }
   System.out.println("CONTENTS OF calledViaReflection&&&&&&&&&&&&&&&&");
   java.util.Set<IClass> s1 = calledViaReflection.keySet();
   for(IClass cl : s1) {
      System.out.println(cl + " "  + cl.hashCode());
      HashMap<IClass, HashSet<Pair<CGNode, IExplodedBasicBlock>>> m1 = calledViaReflection.get(cl);
      java.util.Set<IClass> s2 = m1.keySet();
      for(IClass cl2 : s2) {
         System.out.println("\t" + cl2);
         HashSet<Pair<CGNode, IExplodedBasicBlock>> ns = m1.get(cl2);
         for(Pair<CGNode, IExplodedBasicBlock> p : ns) {
           System.out.println("\t\t" + p.val1.getMethod() + " " + prettyPrint(p.val2.getInstruction()));
         }
      }
   } 
   
  }


    static void printRST() {
  System.out.println("CONTENTS OF  reachingThreadStart *******************");
      java.util.Set<SSAInstruction> s1 = reachingThreadStart.keySet();
      for(SSAInstruction st: s1) {
          System.out.println(prettyPrint(st));
    HashMap<CGNode, HashMap<IExplodedBasicBlock, HashSet<IClass>>> m1 = reachingThreadStart.get(st);
          java.util.Set<CGNode> s2 = m1.keySet();
          for(CGNode n : s2) {
              System.out.println("\t" + n.getMethod());
        HashMap<IExplodedBasicBlock, HashSet<IClass>> m2 = m1.get(n);
              java.util.Set<IExplodedBasicBlock> s3 = m2.keySet();
              for(IExplodedBasicBlock bb : s3) {
                  System.out.println("\t\t" + prettyPrint(bb.getInstruction())); 
      HashSet<IClass> s4 = m2.get(bb);
                  for(IClass c : s4) {
          System.out.println("\t\t\t" + c);
      }
        }
    }
      }  
    }


    static void rankReverseAliasedMayRunInParallel() throws Exception {
        for(Quad pair : reverseAliasedPairs) {
            int mayRIPTotal = 0;
            HashMap<MethodReference, HashSet<Pair<CGNode, IExplodedBasicBlock>>> toBePropagatedToPredScore = new HashMap<MethodReference, HashSet<Pair<CGNode, IExplodedBasicBlock>>>();  
            HashSet<MethodReference> propagationSource = new HashSet<MethodReference>();
            HashMultiset<CGNode> propagationDestination = HashMultiset.create();
            printPair(pair.val1, pair.val2, pair.val3, pair.val4);
            if (!reachedByMethod.containsKey(pair.val2))
               findRunPredecessor((SSAInstruction)pair.val2);
            HashSet<CGNode> m1Set = reachedByMethod.get(pair.val2);

            if (!reachedByMethod.containsKey(pair.val4))
               findRunPredecessor((SSAInstruction)pair.val4);
            HashSet<CGNode> m2Set = reachedByMethod.get(pair.val4);

            if (m1Set == null || m2Set == null) {
                if (isPublic((SSAInstruction)pair.val2) && isPublic((SSAInstruction)pair.val4)) {
        System.out.println("RANK=1");                                    
    }
                else
                   System.out.println("NO RANKING INFO: " + ((m1Set == null) ? prettyPrint((SSAInstruction)pair.val2) + " CANNOT BE REACHED ANY METHOD!" : "" ) + 
                                                        ((m1Set == null) ? prettyPrint((SSAInstruction)pair.val4) + " CANNOT BE REACHED ANY METHOD!" : "" ));
               
               continue;
            }
            System.out.println("METHODS REACHED BY: " + prettyPrint((SSAInstruction)pair.val2));
       for(CGNode m1n : m1Set) {
       System.out.println("\t" + m1n.getMethod());
            }
            System.out.println("METHODS REACHED BY: " + prettyPrint((SSAInstruction)pair.val4));
            for(CGNode m2n : m2Set) {
             System.out.println("\t" + m2n.getMethod());
            }
            int intersection=0;
            for(CGNode n1 : m1Set) {
    //if (n1.getMethod().toString().indexOf("fakeRootMethod") >= 0) continue; 
               if (m2Set.contains(n1)) {
       intersection++;
      HashMap<IExplodedBasicBlock, HashSet<IClass>> bbMap1 = reachingThreadStart.get(pair.val2).get(n1); 
                  Set<IExplodedBasicBlock> bbSet1 = bbMap1.keySet();
                  HashMap<IExplodedBasicBlock, HashSet<IClass>> bbMap2 = reachingThreadStart.get(pair.val4).get(n1);
                  Set<IExplodedBasicBlock> bbSet2 = bbMap2.keySet();
                  for(IExplodedBasicBlock bb1 : bbSet1) {
          for(IExplodedBasicBlock bb2 : bbSet2) {
                          int mayRIP=0;
        /*if (bb1 == bb2) SKIP!!!!{
                              SSAInstruction mcall = bb1.getInstruction();
                              if (mcall instanceof SSAInvokeInstruction) {
          java.util.Set<CGNode> ns = cg.getNodes(((SSAInvokeInstruction)mcall).getDeclaredTarget());
          for(CGNode nsi : ns) {
              if (!nsi.getMethod().isPublic()) {
              addToSet(toBePropagatedToPredScore, ((SSAInvokeInstruction)mcall).getDeclaredTarget(), new Pair(n1, bb1));  
                                      System.out.println( ((SSAInvokeInstruction)mcall).getDeclaredTarget() + " score to be propagated to " + n1 + " FOR BB " + prettyPrint(bb1.getInstruction()));
              propagationSource.add(((SSAInvokeInstruction)mcall).getDeclaredTarget());
                                      propagationDestination.add(n1);
             }
          }
            }
        }
                          else { NO NEED TO PROPAGATE AS WE"RE DOING PATH SENSITIVE*/
                          if (bb1 != bb2) {
            HashSet<IClass> t1 = bbMap1.get(bb1);
                              HashSet<IClass> t2 = bbMap2.get(bb2);
                              if (t1.size() == 0 && t2.size() == 0) {
          mayRIP = ((isPublic(bb1.getInstruction()) && isPublic(bb2.getInstruction())) ? 1 : 0);
                                  
                              }
                              else if (t1.size() == 0 && t2.size() > 0) {
          if (isPredecessor(n1, bb1, bb2))
              mayRIP = -1 * t2.size();
                                  else mayRIP = t2.size() + 1; // +1 helps to differentiate from the case rank=1 due to public access points only  
            }
                              else if (t2.size() == 0 && t1.size() > 0) {
                                  if (isPredecessor(n1, bb2, bb1))
              mayRIP = -1 *t1.size();
                                  else mayRIP = t1.size() + 1; // +1 helps to differentiate from the case rank=1 due to public access points only  
            }
                              else {// t1.size() >0 && t2.size() > 0
                                  mayRIP = t1.size() * t2.size() + 1;// +1 helps to differentiate from the case rank=1 due to public access points only 
            }
                              HashMap<Triple<CGNode, IExplodedBasicBlock, IExplodedBasicBlock>, Integer> qrmap;
                              if (pairRank.containsKey(pair)) 
                                 qrmap = pairRank.get(pair);
                              else qrmap = new HashMap<Triple<CGNode, IExplodedBasicBlock, IExplodedBasicBlock>, Integer>();
                              qrmap.put(new Triple<CGNode, IExplodedBasicBlock, IExplodedBasicBlock>(n1, bb1, bb2), new Integer(mayRIP));  
                              pairRank.put(pair, qrmap);
                              System.out.println("\t RANK=" + mayRIP + " @ CONTEXT= IN METHOD " + n1.getMethod()+ "[" + prettyPrint(bb1.getInstruction()) + " && " + prettyPrint(bb2.getInstruction()) + "]");                     
                              for(IClass tcl : t1) 
          System.out.println("Thread SET1=" + tcl);
                              for(IClass tcl : t2) 
          System.out.println("Thread SET2=" + tcl); 
        } 
          }
      }
         }
      }
            if (intersection == 0) {
               if (isPublic((SSAInstruction)pair.val2) && isPublic((SSAInstruction)pair.val4)) 
        System.out.println("RANK=1");   
         else System.out.println("\t RANK=0: No common access point");   
      }
               // This needs to be iterative until all dependencies get resolved! Assuming there cannot be circular dependencies !!! 
              /*
               Set<MethodReference> mset = toBePropagatedToPredScore.keySet(); 
               while (propagationSource.size() > 0) {                        
                     for(CGNode fn : m1Set) {
             if (mset.contains(fn.getMethod())) {
                            boolean purgeSuccessors = !propagationDestination.contains(fn);
                            if (purgeSuccessors) {
                   int value = 0;
                   if (pairRank.containsKey(fn))
                value = pairRank.get(q).get(fn).get(;
                               if (value != 0) {
            HashSet<CGNode> uset = toBePropagatedToPredScore.get(fn.getMethod());
                                  for(CGNode u: uset) {
              if (!propagationSource.contains(u.getMethod())) 
          nodeRank.put(u, nodeRank.get(u) + value);
                                    propagationDestination.remove(u);
          }
              }
              propagationSource.remove(fn); 
          }
       }         
         } 
         }               
               Set<CGNode> nodes = nodeRank.keySet();
               for(CGNode node : nodes) {
       if (node.getMethod().isPublic()) 
           mayRIPTotal += nodeRank.get(node);
         }
                     
      rankPerReverseAlias.put(pair, mayRIPTotal); 
            System.out.println("RANK=" + mayRIPTotal);
           */
  }
        printRef();
    } 

    static boolean enclosedByMethod(SSAInstruction inst, CGNode node, boolean regular, HashSet<SSAInstruction> visited) throws Exception {
        if (visited.contains(inst)) return false;
        visited.add(inst);
  HashSet<SSAInstruction> set = enclosedBy.get(inst);
        if (set == null) return false;
        for(SSAInstruction einst : set) {
            //System.out.println(einst + " LOCK TYPE " + getLockType(einst) + " EXPECTED " + (regular ? enclosingType : enclosedType));
      if (einst instanceof SSAMonitorInstruction && (( SSAMonitorInstruction)einst).isMonitorEnter() &&  (regular ? enclosingType.equals(getLockType(einst)) :  enclosedType.equals(getLockType(einst)))) {

               Triple<Integer, CGNode, IExplodedBasicBlock> context = instructionContext.get(einst);
               if (((CGNode) context.val2).getMethod().getName().toString().equals(node.getMethod().getName().toString()) && ((CGNode) context.val2).getMethod().getDeclaringClass().getName().toString().equals(node.getMethod().getDeclaringClass().getName()) && ((CGNode) context.val2).getMethod().getSignature().equals(node.getMethod().getSignature()))    
            return true;  
      }
            else if (/*einst instanceof SSAInvokeInstruction && */
                    (regular ? enclosingType.equals(getLockType(einst))  :  enclosedType.equals(getLockType(einst)))) {

    if (((SSAInvokeInstruction)einst).getDeclaredTarget().getName().toString().equals(node.getMethod().getName().toString()) && ((SSAInvokeInstruction)einst).getDeclaredTarget().getDeclaringClass().getName().toString().equals(node.getMethod().getDeclaringClass().getName().toString()) && ((SSAInvokeInstruction)einst).getDeclaredTarget().getSignature().equals(node.getMethod().getSignature()))
        return true;
      }
            if (enclosedByMethod(einst, node, regular, visited))
    return true;

  }
         
  return false;
    } 

    static void transitivePredecessorCollectPath(String stopOnSeeingLockType, SSAInstruction inst, CGNode prev, CGNode cur, HashSet<CGNode> visited, HashSet<IClass> seenRunOfThreadClass/*, boolean callsRunMethod*/) throws Exception {       
        if (cur == null) return;
        System.out.println("TRANSITIVE: "  + cur.getMethod());
        if (cur.getMethod().toString().indexOf("fakeRootMethod") >=0) return;
        if (visited.contains(cur)) return;
        addReflection(cur.getMethod().getDeclaringClass(), inst);
        visited.add(cur);  
        System.out.println("PASSED..");
        if (enclosedByMethod(inst, cur, (enclosingType.indexOf(stopOnSeeingLockType) >= 0), new HashSet<SSAInstruction>())) {
            System.out.println("TERMINATED SEARCHING: COVERED BY OTHER LOCK TYPE " + stopOnSeeingLockType); 
      return; 
  }
        addToSet(reachedByMethod, inst, cur);
        HashSet<IExplodedBasicBlock> bbSet = new HashSet<IExplodedBasicBlock>();
        if (prev == null)
           bbSet.add((IExplodedBasicBlock)instructionContext.get(inst).val3);
        else
           bbSet = findBasicBlockForMethodCallingMethod(cur, prev);

  for(IExplodedBasicBlock bb : bbSet) {
      addAllToMap(reachingThreadStart, inst, cur, bb, seenRunOfThreadClass);
  }  

        java.util.Iterator<CGNode> preds ;
        if (cur.getMethod().getName().toString().indexOf("run") >= 0 && 
            (cha.isSubclassOf(cur.getMethod().getDeclaringClass(), cha.lookupClass(TypeReference.JavaLangThread)) ||   
             cha.implementsInterface(cur.getMethod().getDeclaringClass(), cha.lookupClass(TypeReference.findOrCreate(ClassLoaderReference.Application,
                                                                                                                TypeName.string2TypeName("Ljava/lang/Runnable"))))
        )) {
           seenRunOfThreadClass.add(cur.getMethod().getDeclaringClass());

           System.out.println("Trying to find start of class " + cur.getMethod().getDeclaringClass()); 
           java.util.Set<CGNode> allStartNodesOfInterest = cg.getNodes(MethodReference.findOrCreate(ClassLoaderReference.Application,"Ljava/lang/Thread","start","()V"));  
           for(CGNode nd:allStartNodesOfInterest) {
              //System.out.println("Candidate start method " + nd + "\nFOR " + cur.getMethod().getDeclaringClass().getName().toString());
              boolean ok = false;
              Iterator<CGNode> succs = cg.getSuccNodes(nd);
              while (succs.hasNext()) {
                CGNode threadRun = succs.next();
                //System.out.println("SUCCESSOR=" + threadRun.getMethod()); 
                if (threadRun.getMethod().toString().indexOf(cur.getMethod().getDeclaringClass().getName().toString()) >= 0) 
                {   
              //      ok = true; break;}   // MIGHT HAVE CAUSED MISSING SOME PATHS 
              //}  // MIGHT HAVE CAUSED MISSING SOME PATHS 
              //if (ok) { // MIGHT HAVE CAUSED MISSING SOME PATHS 
                 System.out.println("GOOD NEWS: " + nd); 
                  preds = cg.getPredNodes(nd);
                  for(;preds.hasNext();) {
                     CGNode nn = preds.next(); 
                     if (nn.toString().indexOf("Application") >= 0)
                        transitivePredecessorCollectPath(stopOnSeeingLockType, inst, nd, nn, new HashSet<CGNode>(visited), new HashSet<IClass>(seenRunOfThreadClass));
                  }
               }
              } 
           }
        }
        else {
          preds = cg.getPredNodes(cur);
          for(;preds.hasNext();) {
        
           transitivePredecessorCollectPath(stopOnSeeingLockType, inst, cur, preds.next(), new HashSet<CGNode>(visited), new HashSet<IClass>(seenRunOfThreadClass));
          } 
        }

        return;      
    }



    static void findRunPredecessor(SSAInstruction inst) throws Exception {
        Triple<Integer, CGNode, IExplodedBasicBlock> context = instructionContext.get(inst);
        CGNode node = (CGNode) context.val2;
        if (getLockType(inst).indexOf(enclosedType) >= 0)
      transitivePredecessorCollectPath(enclosingType.substring(0,enclosingType.length()-1), inst, null, node, new HashSet<CGNode>(), new HashSet<IClass>());
        else 
           transitivePredecessorCollectPath(enclosedType.substring(0,enclosedType.length()-1), inst, null, node, new HashSet<CGNode>(),  new HashSet<IClass>()); 
    }


    static boolean isFake(SSAInstruction s) {
        String st = prettyPrint(s); 
        return st.indexOf("Fake") >= 0;   
    }

    static String getCanonicalName(SSAInstruction inst1) {
        if (inst1 instanceof SSAMonitorInstruction) 
      return prettyPrint(inst1);
  else if (inst1 instanceof SSAInvokeInstruction) {
         String is1 = prettyPrint(inst1);
             String methodName1;
             if (is1.indexOf("Fake") >=0)
     methodName1 = is1.substring(is1.lastIndexOf(",")+1, is1.indexOf("Fake")).trim();
             else methodName1 =  is1.substring(is1.lastIndexOf(",")+1, is1.indexOf("line")).trim();
             return methodName1;
  }
        else return "";
    }

    static String getClassName(SSAInstruction inst1) {
  String s = prettyPrint(inst1);
        s = s.substring(s.indexOf(",") + 1, s.length());
        s = s.substring(0, s.indexOf(",")).trim();
        return s;
    }


    static boolean filterAsEnclosed(SSAInstruction inst1) {
        if (enclosedInstruction.indexOf("monitorenter") >= 0) {
            String m = prettyPrint(inst1);
      return (m.indexOf("monitorenter") >= 0 && /*m.indexOf(enclosedClass.substring(enclosedClass.lastIndexOf("/")+1,enclosedClass.length())) >= 0 && */  m.indexOf(enclosedLineNo) >= 0);    
  }
        else { 
            String m = getCanonicalName(inst1);
      if (m.indexOf(enclosedInstruction) >= 0) {
         //String c = getClassName(inst1);
               //if (c.indexOf(enclosedClass) >= 0)
       return true;
      }
  }
        return false;        

    }

    static boolean filterAsEnclosing(SSAInstruction inst1) {

        if (enclosingInstruction.indexOf("monitorenter") >= 0) {
            String m = prettyPrint(inst1);
      return (m.indexOf("monitorenter") >= 0 && /*m.indexOf(enclosingClass) >= 0 &&*/ m.indexOf(enclosingLineNo) >= 0);    
  }
        else { 
            String m = getCanonicalName(inst1);
      if (m.indexOf(enclosingInstruction) >= 0) {
         String c = getClassName(inst1);
               if (c.indexOf(enclosingClass) >= 0)
       return true;
      }
  }
        return false; 
    }
 
    static void addToReverseAliasedEnclosingPairs(Quad q) {
        if (same((SSAInstruction)q.val1,(SSAInstruction)q.val4) || same((SSAInstruction)q.val3, (SSAInstruction)q.val2)) return; 
        // Filter only desired enclosing
        //if (!filterAsEnclosed((SSAInstruction)q.val1) || !filterAsEnclosing((SSAInstruction)q.val2))
  //    return;            
        // Assume that indexed on v3 (not the seedInstruction!) 
        String name = getCanonicalName((SSAInstruction)q.val3);
  HashSet<Quad> list = revAliasedEnclPairs.remove(name);    
        if (list == null) {
      list = new HashSet<Quad>();
            list.add(q);
  }              
        else {
            Quad toBeRemoved = null;
            boolean sameFound = false;  
      for(Quad ql : list) {
    if (ql.sameAs(q)) {
                    sameFound = true;
                    toBeRemoved = ql;
        /*if (q.fakeCount() <= ql.fakeCount()) {
      toBeRemoved = ql;
      }*/
                    break;  
    }    
      }
            if (toBeRemoved != null) {
    list.remove(toBeRemoved);
                list.add(q);
      }
      else if (!sameFound)
    list.add(q);  
        }
        revAliasedEnclPairs.put(name, list);
    }

    static String getLockType(SSAInstruction inst) throws Exception {
      if (inst instanceof SSAMonitorInstruction) {
          OrdinalSet<? extends InstanceKey> lockSet = lockingInstructions.get(inst);
          for(InstanceKey ik : lockSet) {
            if (enclosedType.length() >= enclosingType.length()) {
              if (ik.toString().indexOf(enclosedType) >= 0)
                  return enclosedType;
        else if (ik.toString().indexOf(enclosingType) >= 0)
                  return enclosingType;
            }
            else {
              if (ik.toString().indexOf(enclosingType) >= 0)
                  return enclosingType;
              else if (ik.toString().indexOf(enclosedType) >= 0)
                  return enclosedType;    
            }
    }                  

          if (SUBCLASS_HANDLING && lockSet.size() > 0) {
        // Try subclasses if the lock type is other than java.lang.Object
              Triple<Integer, CGNode, IExplodedBasicBlock> context = instructionContext.get(inst);
              IR ir = context.val2.getIR();
              TypeInference ti = TypeInference.make(ir, false); 
        IClass cl = ti.getType(((SSAMonitorInstruction)inst).getRef()).getType(); 
              if (cl.getName().toString().indexOf("Ljava/lang/Object") < 0) {
              System.out.println("SUBCLASSES OF " + cl);
              java.util.Collection<IClass> subcl = getImmediateSubclasses(cl);
              for(IClass sub : subcl) {
                 // We need to append that > as enclosingType and enclosedType also have at their end.. 
     String subTypeName = sub.getName().toString() + ">";
                 System.out.println("(3) SUBTYPE NAME=" + subTypeName);
     if (subTypeName.indexOf(enclosingType) >= 0)
        return enclosingType; 
     else if (subTypeName.indexOf(enclosedType) >= 0) 
         return enclosedType;
        }
        }
    }      
          else if (SUBCLASS_HANDLING) { //if (lockSet.size() == 0) {
                  Triple<Integer, CGNode, IExplodedBasicBlock> contextInfo = instructionContext.get(inst);
                   IR ir = contextInfo.val2.getIR();
                    SSAInstruction[] insts = ir.getInstructions();
                    IBytecodeMethod method = (IBytecodeMethod)ir.getMethod();
                    int bytecodeIndex = method.getBytecodeIndex(contextInfo.val1);
                    int sourceLineNum = method.getLineNumber(bytecodeIndex);
                    for(int i=0; i < insts.length; i++) {
                       if (insts[i] != null) {
                  Triple<Integer, CGNode, IExplodedBasicBlock> contextInfo2 = instructionContext.get(insts[i]);        
                           int bi = method.getBytecodeIndex(contextInfo2.val1);
                           int sl =  method.getLineNumber(bi);
                           
                           if (sourceLineNum == sl) { 
            System.out.println(prettyPrint(insts[i]));
                              try {
             SSAGetInstruction gis = (SSAGetInstruction) insts[i];
                               String nameOfLockType = gis.getDeclaredFieldType().toString();
             System.out.println("field type=" + gis.getDeclaredFieldType()); 
                               if (nameOfLockType.indexOf(enclosingType) >= 0)
           return enclosingType;
                               else if (nameOfLockType.indexOf(enclosedType) >= 0) 
          return enclosedType;
                               // Try subclasses
                              IClass cl = cha.lookupClass(gis.getDeclaredFieldType()); 
                              if (cl.getName().toString().indexOf("Ljava/lang/Object") < 0) {
                              System.out.println("SUBCLASSES OF " + cl);
                              java.util.Collection<IClass> subcl = getImmediateSubclasses(cl);
                              for(IClass sub : subcl) {
                                // We need to append that > as enclosingType and enclosedType also have at their end.. 
                    String subTypeName = sub.getName().toString() + ">";
                                System.out.println("(4) SUBTYPE NAME=" + subTypeName);
                    if (subTypeName.indexOf(enclosingType) >= 0)
                       return enclosingType; 
                    else if (subTypeName.indexOf(enclosedType) >= 0) 
                       return enclosedType;
                        }  
            }

            }
                               catch(Exception e) {
           System.out.println("Cast failed! for " + insts[i].getClass());
                                 
             }
         }
           }
        }

    }          
  
      }
      else {//       if (inst instanceof SSAInvokeInstruction) {
          String t1 = enclosedType.substring(0, enclosedType.length()-1);
          String t2 = enclosingType.substring(0, enclosingType.length()-1);
          // May include fake class methods    
          if (t1.length() >= t2.length()) {
             if (((SSAInvokeInstruction)inst).getCallSite().getDeclaredTarget().getDeclaringClass().getName().toString().indexOf(t1) >=0)
                return enclosedType;
             else if (((SSAInvokeInstruction)inst).getCallSite().getDeclaredTarget().getDeclaringClass().getName().toString().indexOf(t2) >= 0)
                   return enclosingType;
          }
          else {
             if (((SSAInvokeInstruction)inst).getCallSite().getDeclaredTarget().getDeclaringClass().getName().toString().indexOf(t2) >=0)
                return enclosingType;
             else if (((SSAInvokeInstruction)inst).getCallSite().getDeclaredTarget().getDeclaringClass().getName().toString().indexOf(t1) >= 0)
                   return enclosedType;
          }

          if (SUBCLASS_HANDLING) {
          // try superclass
          IClass cl = cha.lookupClass(((SSAInvokeInstruction)inst).getDeclaredTarget().getDeclaringClass());
          IClass supcl = getImmediateSuperclass(cl);
          if (supcl != null) {
        if (supcl.getName().toString().indexOf(t2) >= 0) 
           return enclosingType;
              else return enclosedType;
    }   
    }
      }

      throw new Exception("Unknown lock  type!");
    }

    // Tries to handle subclassing
    static java.util.Set getPossibleNodes(SSAInstruction inst) {
        HashSet<CGNode> nodes = new HashSet<CGNode>();
  if (inst instanceof SSAInvokeInstruction) {
           java.util.Collection<IMethod> pt = cha.getPossibleTargets(((SSAInvokeInstruction)inst).getDeclaredTarget());
           for(IMethod pm : pt)  {
               CGNode n = cg.getNode(pm, Everywhere.EVERYWHERE);
         if (n != null)  
             nodes.add(n);
     } 
  } 
  return nodes; 
    }

   static boolean isPrivate(SSAInstruction is) {
      if (is instanceof SSAInvokeInstruction) {         
    java.util.Set<CGNode> mnodes = cg.getNodes(((SSAInvokeInstruction)is).getCallSite().getDeclaredTarget());
          //java.util.Set<CGNode> mnodes = getPossibleNodes(is);
          for(CGNode n: mnodes) {             
            if (n.getMethod().isSynchronized() && n.getMethod().isPrivate())  
               return true;
    }
          return false;              
      }
      return false;     
  }

   static boolean isPublic(SSAInstruction is) {
      if (is instanceof SSAInvokeInstruction) {         
    java.util.Set<CGNode> mnodes = cg.getNodes(((SSAInvokeInstruction)is).getCallSite().getDeclaredTarget());
          //java.util.Set<CGNode> mnodes = getPossibleNodes(is);
          for(CGNode n: mnodes) {             
            if (n.getMethod().isSynchronized() && n.getMethod().isPublic())  
               return true;
    }
          return false;              
      }
      return false;     
  }

    static boolean isSynchronizedMethodOfSameClass(SSAInstruction is1, SSAInstruction is2) {
      String className1 = null;
      if (is1 instanceof SSAInvokeInstruction) {
    java.util.Set<CGNode> mnodes = cg.getNodes(((SSAInvokeInstruction)is1).getCallSite().getDeclaredTarget());
    //java.util.Set<CGNode> mnodes =  getPossibleNodes(is1);
            for(CGNode n : mnodes) 
                if (n.getMethod().isSynchronized()) {
      className1 = n.getMethod().getDeclaringClass().getName().toString();
                        break;   
    }
      }
      if (className1 == null) return false;
      if (is2 instanceof SSAInvokeInstruction) {
    java.util.Set<CGNode> mnodes = cg.getNodes(((SSAInvokeInstruction)is2).getCallSite().getDeclaredTarget());
    //java.util.Set<CGNode> mnodes = getPossibleNodes(is2);
            for(CGNode n : mnodes) 
                if (n.getMethod().isSynchronized()) {
      String className2 = n.getMethod().getDeclaringClass().getName().toString();
                        if (className1.equals(className2))
          return true; 
    }
      
      }
       return false; 
     
    }

    /*
    static IField getField(CGNode node, int valueNumber) {
       IR ir = node.
     ir.getSymbolTable().getValueString(
 
     }*/

    static boolean isDesiredEnclosingLockingInstruction(SSAInstruction is) {

        System.out.println("In isDesired ***** " + is);
        if (is instanceof SSAMonitorInstruction) {
            if (((SSAMonitorInstruction)is).isMonitorEnter()) {
               int ref = ((SSAMonitorInstruction)is).getRef();
               Triple<Integer, CGNode, IExplodedBasicBlock> contextInfo = instructionContext.get(is);
               CGNode node = (CGNode)contextInfo.val2;
               // Assume that the lock is a local variable also includes this
               OrdinalSet<? extends InstanceKey> lockSet = pointerAnalysis.getPointsToSet(heapModel.getPointerKeyForLocal(node, ref));
               for(InstanceKey ik : lockSet) {
                   System.out.println("DESIRED LOCK type= " + enclosingType +" in " + ik.toString());
                   if (ik.toString().indexOf(enclosingType) >= 0 || ik.toString().indexOf(enclosedType) >= 0)
                        return true; 
               }
               if (lockSet.size() == 0) {// the lock is a field instance
       try {
                    IR ir = node.getIR();
                    SSAInstruction[] insts = ir.getInstructions();
                    IBytecodeMethod method = (IBytecodeMethod)ir.getMethod();
                    int bytecodeIndex = method.getBytecodeIndex(contextInfo.val1);
                    int sourceLineNum = method.getLineNumber(bytecodeIndex);
                    for(int i=0; i < insts.length; i++) {
                       if (insts[i] != null) {
         Triple<Integer, CGNode, IExplodedBasicBlock> contextInfo2 = instructionContext.get(insts[i]);
                           int bi = method.getBytecodeIndex(contextInfo2.val1);
                           int sl =  method.getLineNumber(bi);
                           
                           if (sourceLineNum == sl) { 
            System.out.println(prettyPrint(insts[i]));
                              try {
             SSAGetInstruction gis = (SSAGetInstruction) insts[i];
                               String nameOfLockType = gis.getDeclaredFieldType().toString();
             System.out.println("field type=" + gis.getDeclaredFieldType()); 
                               return (nameOfLockType.indexOf(enclosingType) >= 0 || nameOfLockType.indexOf(enclosedType) >= 0);
     
            }
                               catch(Exception e) {
           System.out.println("Cast failed! for " + insts[i].getClass());
                                 
             }
         }
           }
        }

       }
                   catch(InvalidClassFileException e) {
           System.out.println(e);
       }

         }
      }
            return false;                                      
  }
        else { //if (is instanceof SSAInvokeInstruction) {
            java.util.Set<CGNode> mnodes = cg.getNodes(((SSAInvokeInstruction)is).getCallSite().getDeclaredTarget());
            //java.util.Set<CGNode> mnodes = getPossibleNodes(is);
            for(CGNode n : mnodes) {
                if (n.getMethod().isSynchronized())  {
                    if (!n.getMethod().isStatic()) {
                        OrdinalSet<? extends InstanceKey> lockSet = pointerAnalysis.getPointsToSet(heapModel.getPointerKeyForLocal(n, 1));
                        for(InstanceKey ik : lockSet) {
                            //System.out.println("DESIRED LOCK type= " + enclosingType +" in " + ik.toString());
                            if (ik.toString().indexOf(enclosingType) >= 0 || ik.toString().indexOf(enclosedType) >= 0)
                                return true; 
                        }
                        return false;
                    }
                    else if (n.getMethod().getDeclaringClass().getName().toString().indexOf(enclosingType) >= 0 || 
                            n.getMethod().getDeclaringClass().getName().toString().indexOf(enclosedType) >= 0)
                        return true;
                    else return false;
                }
                else return false;
            }
            return false;
        }
      
    }


    // inst1 is from lockingInstructions and inst2 is from lockingInstructionsRev 
    private static boolean aliasedReverseLockingInstructions(SSAInstruction inst1, SSAInstruction inst2) {
        if ( inst1 instanceof SSAInvokeInstruction && ((SSAInvokeInstruction)inst1).isStatic() &&
             inst2 instanceof SSAInvokeInstruction && ((SSAInvokeInstruction)inst2).isStatic()) {
             return ((SSAInvokeInstruction)inst1).getCallSite().getDeclaredTarget().getDeclaringClass().equals(((SSAInvokeInstruction)inst2).getCallSite().getDeclaredTarget().getDeclaringClass());
         }
        else if (inst1 instanceof SSAInvokeInstruction && !((SSAInvokeInstruction)inst1).isStatic() &&
             inst2 instanceof SSAInvokeInstruction && ((SSAInvokeInstruction)inst2).isStatic()) 
            return false;
        else if (inst1 instanceof SSAInvokeInstruction && ((SSAInvokeInstruction)inst1).isStatic() &&
             inst2 instanceof SSAInvokeInstruction && !((SSAInvokeInstruction)inst2).isStatic()) 
            return false;
         if (inst1.equals(inst2)) return true; 
         OrdinalSet<? extends InstanceKey> lockSet1;
         OrdinalSet<? extends InstanceKey> lockSet2;
         // Can be null for fake class and method calls
         lockSet1 = lockingInstructions.get(inst1);  
         // Can be null for fake class and method calls 
         lockSet2 = lockingInstructions.get(inst2);
         System.out.println("Checking reverse alias for: " + prettyPrint(inst1) + " VS " + prettyPrint(inst2));
         if (commonLockSet(lockSet1, lockSet2)) {
       System.out.println("true");
             return true;
   } 
   else { 
            System.out.println("false"); 
            return false;
   }
         /*
         System.out.println(lockSet1 + " VS " + lockSet2);
         System.out.println(lockSetToString(lockSet1).equals(lockSetToString(lockSet2)));
       String is1 = prettyPrint(inst1);
             String is2 = prettyPrint(inst2);
             String methodName1;
             if (is1.indexOf("Fake") >=0)
     methodName1 = is1.substring(is1.lastIndexOf(",")+1, is1.indexOf("Fake")).trim();
             else methodName1 =  is1.substring(is1.lastIndexOf(",")+1, is1.indexOf("line")).trim();
             //System.out.println("Fake class method name=" + methodName1);
             String methodName2;
             if (is2.indexOf("Fake") >=0)
     methodName2 = is2.substring(is2.lastIndexOf(",")+1, is2.indexOf("Fake")).trim();
             else methodName2 =  is2.substring(is2.lastIndexOf(",")+1, is2.indexOf("line")).trim();
             //System.out.println("Fake class method name=" + methodName2);
       if ((is1.indexOf("Fake") >=0 && (methodName1.equals(methodName2) || isSynchronizedMethodOfSameClass(inst1, inst2))) || (is2.indexOf("Fake") >= 0 && (methodName1.equals(methodName2) || isSynchronizedMethodOfSameClass(inst1, inst2))))
     return true;       
       //System.out.println("Comparing lock sets of " + prettyPrint(inst1) + " AND " + prettyPrint(inst2)); 
       return (lockSet1 != null && lockSet2 != null && (lockSetToString(lockSet1).equals(lockSetToString(lockSet2)) || OrdinalSet.<InstanceKey>intersect((OrdinalSet<InstanceKey>)lockSet1, (OrdinalSet<InstanceKey>)lockSet2).size() > 0));*/
    }  

    private static boolean aliasedLockingInstructions(SSAInstruction inst1, SSAInstruction inst2) {
  if ( inst1 instanceof SSAInvokeInstruction && ((SSAInvokeInstruction)inst1).isStatic() &&
       inst2 instanceof SSAInvokeInstruction && ((SSAInvokeInstruction)inst2).isStatic()) {
             return ((SSAInvokeInstruction)inst1).getCallSite().getDeclaredTarget().getDeclaringClass().equals(((SSAInvokeInstruction)inst2).getCallSite().getDeclaredTarget().getDeclaringClass());
   }
  else if (inst1 instanceof SSAInvokeInstruction && !((SSAInvokeInstruction)inst1).isStatic() &&
       inst2 instanceof SSAInvokeInstruction && ((SSAInvokeInstruction)inst2).isStatic()) 
      return false;
        else if (inst1 instanceof SSAInvokeInstruction && ((SSAInvokeInstruction)inst1).isStatic() &&
       inst2 instanceof SSAInvokeInstruction && !((SSAInvokeInstruction)inst2).isStatic()) 
      return false;
         if (inst1.equals(inst2)) return true; 
         OrdinalSet<? extends InstanceKey> lockSet1;
         lockSet1 = lockingInstructions.get((SSAInstruction)inst1);   
         OrdinalSet<? extends InstanceKey> lockSet2 ;
         lockSet2 = lockingInstructions.get((SSAInstruction)inst2);
         if (lockSet1 != null && lockSet2 != null)
      return (OrdinalSet.<InstanceKey>intersect((OrdinalSet<InstanceKey>)lockSet1, (OrdinalSet<InstanceKey>)lockSet2).size() > 0); 
   else return false;

   }  


    /*
    private static void collectOuterMostEnclosingByType(SSAInstruction enclosed, SSAInstruction original, HashSet<SSAInstruction> visited, String desiredType, ArrayList<SSAInstruction> enclosingNonType,  ArrayList<SSAInstruction> enclosingDesiredType) throws Exception {
           if (visited.contains(enclosed)) return ;
           visited.add(enclosed);
           HashSet<SSAInstruction> enclosingSet = enclosedBy.get(enclosed);
           if (enclosingSet == null) { 
         if (!enclosed.equals(original))  
       enclosingNonType.add((SSAInstruction)enclosed); 
               return;
     }
           for(SSAInstruction enclosing : enclosingSet) {
               //System.out.println("IS SUPER ENCLOSING " + prettyPrint((SSAInstruction)enclosing) + " of type " + (reverseMode == true ? enclosedType : enclosingType));
               //System.out.println("(ORIGINAL=" + prettyPrint((SSAInstruction)original) + ")");
         if (!getLockType((SSAInstruction)enclosing).equals(desiredType))  {
       //System.out.println("NO!");
       collectOuterMostEnclosingByType((SSAInstruction)enclosing, original, visited, desiredType, enclosingNonType, enclosingDesiredType);
               }
               else {
       ArrayList<SSAInstruction> aliasList = new ArrayList<SSAInstruction>();
       findOutMostAlias((SSAInstruction)enclosing,desiredType, new HashSet<SSAInstruction>(), aliasList);   
       enclosingDesiredType.addAll(aliasList);
         }
     }

    }

    */

    private static boolean printPair(Object enclosed1, Object enclosing1, Object enclosed2, Object enclosing2) {
        //System.out.println("printPair????");
  if (same((SSAInstruction)enclosed1,(SSAInstruction)enclosing2) || same((SSAInstruction)enclosed2, (SSAInstruction)enclosing1)) return false;
        totalNumPairs++;
        if (isPublic((SSAInstruction)enclosing1) && isPublic((SSAInstruction)enclosing2)) {
            System.out.print("[PUBLIC] ");         
            numPublicPairs++;        
  }
  System.out.println("REVERSE ALIASED LOCKING PAIRS:\n" + "\t" +  prettyPrint((SSAInstruction)enclosing1) + " {{{ " + prettyPrint((SSAInstruction)enclosed1) + " }}}");  
        System.out.println("\t" + prettyPrint((SSAInstruction)enclosing2) + " {{{ " + prettyPrint((SSAInstruction)enclosed2) + " }}}");        
        return true;
    }


    private static boolean empty(ArrayList<SSAInstruction> list) {
  return list.size() == 0;
    }

    /*    
    private static void processReverseAliasedPair(SSAInstruction enclosed1, SSAInstruction enclosing1, SSAInstruction enclosed2, SSAInstruction enclosing2) throws Exception {
  ArrayList<SSAInstruction> superEnclosingDesType1 = new ArrayList<SSAInstruction>();
  ArrayList<SSAInstruction> superEnclosingDesType2 = new ArrayList<SSAInstruction>(); 
  ArrayList<SSAInstruction> superEnclosingNotDesType1 = new ArrayList<SSAInstruction>();
  ArrayList<SSAInstruction> superEnclosingNotDesType2 = new ArrayList<SSAInstruction>();        
        collectOuterMostEnclosingByType(enclosing1, enclosing1, new HashSet<SSAInstruction>(), enclosedType, superEnclosingNotDesType1, superEnclosingDesType1);
        collectOuterMostEnclosingByType(enclosing2, enclosing2, new HashSet<SSAInstruction>(), enclosingType, superEnclosingNotDesType2, superEnclosingDesType2);

        totalNumReverseAliasedPairs++; 
        if ((!empty(superEnclosingDesType1) && empty(superEnclosingNotDesType1) && empty(superEnclosingDesType2)) ||
      (!empty(superEnclosingDesType2) && empty(superEnclosingNotDesType2) && empty(superEnclosingDesType1))) {
            // do not report
            numNotReportedReverseAliasedPairs++;
  }
        else if (!empty(superEnclosingDesType1) && !empty(superEnclosingDesType2)) {
      // report cross product
             for(SSAInstruction super1 :  superEnclosingDesType1) {
     for(SSAInstruction super2 : superEnclosingDesType2) {
         if (printPair(enclosing1, super1, enclosing2, super2)) {
                        numCrossProductReverseAliasedPairs++;
                        if (isPublic((SSAInstruction)super1) && isPublic((SSAInstruction)super2)) 
                            numPublicCrossProductReverseAliasedPairs++;
         }
     }        
      }  

      if (! empty(superEnclosingNotDesType1) && !empty(superEnclosingNotDesType2)) {
    // report original as well
                if (printPair(enclosed1, enclosing1, enclosed2, enclosing2)) {
                   if (isPublic((SSAInstruction)enclosing1) && isPublic((SSAInstruction)enclosing2)) 
                       numPublicReverseAliasedPairs++;        
    }
      }
  }
        else {
      // report original
      if (printPair(enclosed1, enclosing1, enclosed2, enclosing2)) {
               if (isPublic((SSAInstruction)enclosing1) && isPublic((SSAInstruction)enclosing2)) 
                       numPublicReverseAliasedPairs++;
      }
  }
    }


    static void findOutMostAlias(SSAInstruction enclosing, String desiredType, HashSet<SSAInstruction> visited, ArrayList<SSAInstruction> list) throws Exception {
  if (visited.contains(enclosing)) {
           return;
        }
        visited.add(enclosing); 
        ArrayList<SSAInstruction> l = new  ArrayList<SSAInstruction> (); 
        HashSet<SSAInstruction> rs = enclosedBy.get(enclosing);
        for(SSAInstruction r : rs) {
     HashSet<SSAInstruction> v = new HashSet<SSAInstruction>();
           v.add(enclosing);            
           findOutMostAlias((SSAInstruction)r, desiredType, v, l);
  }
        if (l.size() == 0 && getLockType(enclosing).equals(desiredType))
     list.add(enclosing);
   }
    */

    static void exploreEnclosed(SSAInstruction enclosing, String desiredType, ArrayList<SSAInstruction> list, HashSet<SSAInstruction> visited) throws Exception {
  if (visited.contains(enclosing)) return;
        visited.add(enclosing);
        if (getLockType(enclosing).equals(desiredType)) {
      list.add(enclosing);
            return;
  }
        HashSet<SSAInstruction> enclosedSet = encloses.get(enclosing);
        if (enclosedSet == null) return;
        for(SSAInstruction enclosed : enclosedSet) {
      exploreEnclosed((SSAInstruction)enclosed, desiredType, list, visited);
  }           
        
    }
 
   
    private static void collectEnclosingPairs() throws Exception {

       //Clean up self cycles first!

       HashSet<Pair<Object,Object>> edecRemove = new HashSet<Pair<Object,Object>>();
       java.util.Set<SSAInstruction> edS = enclosedBy.keySet();
       for(SSAInstruction ed : edS) {
          HashSet<SSAInstruction> ecS = enclosedBy.get(ed);
          for(SSAInstruction ec : ecS) {
             if (ed.equals(ec)) 
                edecRemove.add(new Pair(ed, ec));
          } 
       }      
       for(Pair<Object,Object> pr : edecRemove) {
     removeFromSet(enclosedBy, (SSAInstruction)pr.val1, (SSAInstruction)pr.val2); 
     removeFromSet(encloses,(SSAInstruction) pr.val2 , (SSAInstruction)pr.val1);   
       }


       java.util.Set<SSAInstruction> enclosingSet = encloses.keySet();
       java.util.Set<SSAInstruction> allEnclosedSet = enclosedBy.keySet();
       for(SSAInstruction enclosing : enclosingSet) {
     if (/*(!allEnclosedSet.contains(enclosing) || !isPrivate((SSAInstruction)enclosing)) &&*/ getLockType((SSAInstruction)enclosing).equals(enclosingType)) {
        HashSet<SSAInstruction> enclosedSet = encloses.get(enclosing);
              ArrayList<SSAInstruction> list = new ArrayList<SSAInstruction>();  
              for(SSAInstruction enclosed : enclosedSet) {                  
                  exploreEnclosed((SSAInstruction)enclosed, enclosedType, list, new HashSet<SSAInstruction>());
        }
              for(SSAInstruction enc : list) {
         addToSet(enclosesRegular, enclosing, enc);
                     addToSet(enclosedByRegular, enc, enclosing);  
        }
    }
       }

       enclosingSet = encloses.keySet();
       for(SSAInstruction enclosing : enclosingSet) {
     if (/*(!allEnclosedSet.contains(enclosing) || !isPrivate((SSAInstruction)enclosing)) && */ getLockType((SSAInstruction)enclosing).equals(enclosedType)) {
        HashSet<SSAInstruction> enclosedSet = encloses.get(enclosing);
              ArrayList<SSAInstruction> list = new ArrayList<SSAInstruction>();  
              for(SSAInstruction enclosed : enclosedSet) {  
                 exploreEnclosed((SSAInstruction)enclosed, enclosingType, list, new HashSet<SSAInstruction>());
        }
              for(SSAInstruction enc : list) {
      addToSet(enclosesReverse, enclosing, enc); 
                  addToSet(enclosedByReverse, enc, enclosing);
        }  
    }
       }



       /*
          java.util.Set<SSAInstruction> enclosedSet = enclosedBy.keySet();
          for(SSAInstruction enclosed : enclosedSet) {
        HashSet<SSAInstruction> enclosingSet = enclosedBy.get(enclosed);
              for(SSAInstruction enclosing : enclosingSet) {
                  String type1 = getLockType((SSAInstruction)enclosed);  
                  String type2 = getLockType((SSAInstruction)enclosing);
                  if (!type1.equals(type2)) {
                      ArrayList<SSAInstruction> outMostAlias = new  ArrayList<SSAInstruction>();
                      findOutMostAlias((SSAInstruction)enclosing, type2, new HashSet<SSAInstruction>(), outMostAlias);
                      for(SSAInstruction alias : outMostAlias) {
        if (type1.equals(enclosedType))
            addToSet(enclosedByRegular, enclosed, alias);
                          else 
                              addToSet(enclosedByReverse, enclosed, alias);  
          } 
      }
        }
    }
       */

    }
     
    
    /*
    private static void computeAliasedEnclosingPairs() {
       java.util.Set<SSAInstruction> enclosedSet = enclosedBy.keySet();
       for(SSAInstruction enclosed1 : enclosedSet) {
           OrdinalSet<? extends InstanceKey> lockSet1 = lockingInstructions.get((SSAInstruction)enclosed1);         
           for(SSAInstruction enclosed2 : enclosedSet) { 
               boolean enclosedSame = (enclosed1 == enclosed2);
               OrdinalSet<? extends InstanceKey> lockSet2 = lockingInstructions.get((SSAInstruction)enclosed2);
               if (aliasedLockingInstructions((SSAInstruction)enclosed1, (SSAInstruction)enclosed2)) {
             HashSet<SSAInstruction> enclosingSet1 = enclosedBy.get(enclosed1);
                   HashSet<SSAInstruction> enclosingSet2 = enclosedBy.get(enclosed2);
                   for(SSAInstruction enclosing1 : enclosingSet1) {                        
                       for(SSAInstruction enclosing2 : enclosingSet2) {
                           boolean enclosingSame = (enclosing1 == enclosing2); 
         if ((!enclosedSame || ! enclosingSame) && aliasedLockingInstructions((SSAInstruction)enclosing1, (SSAInstruction)enclosing2)) {
             System.out.println("ALIASED LOCKING PAIRS:\n" + "\t" +  prettyPrint((SSAInstruction)enclosing1) + " {{{ " + prettyPrint((SSAInstruction)enclosed1) + " }}}");  
                               System.out.println("\t" + prettyPrint((SSAInstruction)enclosing2) + " {{{ " + prettyPrint((SSAInstruction)enclosed2) + " }}}"); 
         }                               
           }
   
       }
         }
     }
       }
    }

*/

    private static boolean same(SSAInstruction inst1, SSAInstruction inst2) {
        String is1 = prettyPrint(inst1);
        String is2 = prettyPrint(inst2);  
        if ((inst1 instanceof SSAMonitorInstruction && inst2 instanceof SSAMonitorInstruction)  ||
           (inst1 instanceof SSAInvokeInstruction && inst2 instanceof SSAInvokeInstruction))             
          return is1.equals(is2); 
        //if (inst1 instanceof SSAMonitorInstruction && inst2 instanceof SSAMonitorInstruction) 
   //   return inst1.equals(inst2);
  //else if (inst1 instanceof SSAInvokeInstruction && inst2 instanceof SSAInvokeInstruction) {
      //   String is1 = prettyPrint(inst1);
            // String is2 = prettyPrint(inst2);
             //return is1.equals(is2);
             /*
             String methodName1;
             if (is1.indexOf("Fake") >=0)
     methodName1 = is1.substring(is1.lastIndexOf(",")+1, is1.indexOf("Fake")).trim();
             else methodName1 =  is1.substring(is1.lastIndexOf(",")+1, is1.indexOf("line")).trim();
             //System.out.println("Fake class method name=" + methodName1);
             String methodName2;
             if (is2.indexOf("Fake") >=0)
     methodName2 = is2.substring(is2.lastIndexOf(",")+1, is2.indexOf("Fake")).trim();
             else methodName2 =  is2.substring(is2.lastIndexOf(",")+1, is2.indexOf("line")).trim();
             if (methodName1.equals(methodName2) && (is1.indexOf("Fake") >=0 || is2.indexOf("Fake") >=0))
     return true;
             else return is1.equals(is2);        
       */ 
  //}
        else return false;
    }


    private static void computeReverseAliasedEnclosingPairs(HashMap<SSAInstruction, HashSet<SSAInstruction>> enclosesRegular, HashMap<SSAInstruction, HashSet<SSAInstruction>> enclosesReverse) throws Exception {

       java.util.Set<SSAInstruction> enclosingSet1 = enclosesRegular.keySet();     
       for(SSAInstruction enclosing1 : enclosingSet1) {
           java.util.Set<SSAInstruction> enclosingSet2 = enclosesReverse.keySet();
           for(SSAInstruction enclosing2 : enclosingSet2) { 
               HashSet<SSAInstruction> enclosedSet1 = enclosesRegular.get(enclosing1); 
               for(SSAInstruction enclosed1 : enclosedSet1) {                     
                   HashSet<SSAInstruction> enclosedSet2 = enclosesReverse.get(enclosing2);   
                   for(SSAInstruction enclosed2 : enclosedSet2) {
         if (aliasedReverseLockingInstructions((SSAInstruction)enclosing1, (SSAInstruction)enclosed2) && aliasedReverseLockingInstructions((SSAInstruction)enclosed1, (SSAInstruction)enclosing2)) {
                             // indexed on enclosed2 (v3)
                             
                                 addToReverseAliasedEnclosingPairs(new Quad(enclosed1, enclosing1, enclosed2, enclosing2));    
                 //printPair(enclosed1, enclosing1, enclosed2, enclosing2);          
           }                              
       }
   
         }
     }
       }
       //System.out.println("Total number of aliased pairs=" +  totalNumPairs);
       //System.out.println("Number of pairs with public entries=" + numPublicPairs);

       System.out.println("REDUCED REVERSE ALIAS PAIRS"); 
       int num = 0;
       java.util.Set<String> keys = revAliasedEnclPairs.keySet();
       for(String encldName : keys) {
     HashSet<Quad> list = revAliasedEnclPairs.get(encldName);
           num += list.size();  
     for(Quad rq : list) {
         if (printPair(rq.val1, rq.val2, rq.val3, rq.val4))
                   reverseAliasedPairs.add(rq); 
     }
       }
       System.out.println("Total number of aliased pairs=" + num); 
    } 

    

    private static boolean isAnEntryClass(String name) {
      String[] entryClassName = entryClass.split(";");
      for(int i=0; i < entryClassName.length; i++)
         if (name.indexOf(entryClassName[i]) >= 0)
            return true;
      return false;
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

    private static void reachabilityAnalysis() throws InvalidClassFileException {
       HashSet<SSAInstruction> visitedInst = new HashSet<SSAInstruction>(); 
       NumberedEdgeManager<CGNode> edgeM = ((ExplicitCallGraph)cg).getEdgeManager();   
       ArrayList<SSAInstruction> workList = new ArrayList<SSAInstruction>();
       java.util.Set<SSAInstruction> lis = lockingInstructions.keySet();
       for(SSAInstruction li : lis) {
              workList.add(li);     
       }   
       System.out.println("worklist size=" + workList.size());
       while (workList.size() > 0) {       
          Object currentObj =  workList.remove(0);
          if (currentObj instanceof SSAInstruction)
              handle(visitedInst, workList, (SSAInstruction)currentObj);
       }
    }


    // Inter-procedural control-flow analysis to find enclosing locks
    // Also considers immediate superclass method callsites going backward on the inter-procedural control-flow graph 
    static void handle(HashSet<SSAInstruction> visitedInst, ArrayList<SSAInstruction> workList, SSAInstruction current) throws InvalidClassFileException {        
        if (visitedInst.contains(current)) { 
     //System.out.println("Skipping " + prettyPrint(current)); 
           return;
  }
        visitedInst.add(current);
        HashSet<IExplodedBasicBlock> visited = new HashSet<IExplodedBasicBlock>(); 
        Triple<Integer, CGNode, IExplodedBasicBlock> contextInfo = instructionContext.get(current);
        int instIndex = ((Integer)contextInfo.val1).intValue();
        CGNode node = (CGNode)contextInfo.val2;
        IExplodedBasicBlock bb =  (IExplodedBasicBlock)contextInfo.val3;
        ExplodedControlFlowGraph graph = (ExplodedControlFlowGraph)  icfg.getCFG(node);
        java.util.Collection<IExplodedBasicBlock> preds =graph.getNormalPredecessors(bb); 
        boolean foundEnclosing = false;
  for(IExplodedBasicBlock  pred : preds) {
            if (explorePredecessors(visited, graph, node, current, pred, 0))
                foundEnclosing = true;           
  }


        if (!foundEnclosing) {
            System.out.println("Could not find the enclosing sync for " + prettyPrint(current));
            /*HashSet<SSAInstruction> curR = reachesLocking.get(current);
            if (curR != null)
               for(SSAInstruction o : curR )      
                  System.out.println(prettyPrint((SSAInstruction)o));
            */
            System.out.println("adding call sites of this method:");     
            HashSet<SSAInstruction> csites = callSites.get(node); 
            if (csites == null)
    csites = new  HashSet<SSAInstruction>();

            if (SUBCLASS_HANDLING) {

            IClass cl = getImmediateSuperclass(node.getMethod().getDeclaringClass());
            System.out.println("Super class :" + cl);
            if (cl != null && cl.getName().toString().indexOf("Ljava/lang/Object") < 0) {
    // if superclass is not java.lang.Object then consider superclass call sites as well
      //System.out.println("Signature " +  node.getMethod().getSignature());
            String signature = node.getMethod().getSignature();
            signature = signature.substring(signature.indexOf("("));  
      MethodReference mr = MethodReference.findOrCreate(ClassLoaderReference.Application, StringStuff.deployment2CanonicalTypeString(cl.getName().toString()),
        node.getMethod().getName().toString(),signature);
            if (mr != null) {
    System.out.println("Super class method call: " + mr);
                      java.util.Set<CGNode> mnodes = cg.getNodes(mr);
                      for(CGNode m : mnodes) {
        for(CGNode n : cg) {
            java.util.Iterator<CallSiteReference> supcs = cg.getPossibleSites(n, m);
            while(supcs.hasNext()) {
                                 CallSiteReference csrf = supcs.next();
         SSAInstruction minst = getInvokeInstructionAtPC(n.getIR(), csrf.getProgramCounter());
                                 if (minst != null) {
                                    System.out.println("Super class method callsite: " + minst);
                                    csites.add(minst); 
         }
            }                      
        }
          }
       }
      }
      }
    //}
            if (csites != null) {
                for(SSAInstruction csins: csites) {
                    System.out.println("Call site for "  + node.getMethod().getName() + " (Instruction " + prettyPrint((SSAInstruction)csins) + " )");
                    if (node.getMethod().isSynchronized() && isDesiredEnclosingLockingInstruction((SSAInstruction)csins)) {
                        //System.out.println("Updating enclosedby");
                        if (lockingInstructions.containsKey(current)) {
                           //System.out.println("Enclosed : " + prettyPrint((SSAInstruction)current)); 
                           addToSet(enclosedBy, current, csins);
                           addToSet(encloses, csins, current);
      }
                        else {//transitive
                            //System.out.println("transitive");              
                            HashSet<SSAInstruction> cr = reachesLocking.get(current);
                            for(SSAInstruction o : cr ) {
                                //System.out.println("candidate enclosed " + prettyPrint((SSAInstruction)o));  
                                if (lockingInstructions.containsKey(o)) { 
                                    //System.out.println("Enclosed : " + prettyPrint((SSAInstruction)o));                        
                                    addToSet(enclosedBy, o, csins);      
                                    addToSet(encloses, csins, o);
        }                       
                            }
                        }
                        workList.add(csins);
                    }
        else {
                      //System.out.println("Updating reaches locking");
                      boolean toBeHandledAgain = false;
                      if (!lockingInstructions.containsKey(current)) {
                            //System.out.println("Adding this call site to INDIRECT reachesLocking");
                            HashSet<SSAInstruction> cr = reachesLocking.get(current);
                            for(SSAInstruction o : cr ) {     
                                   //System.out.println(prettyPrint((SSAInstruction)o));                         
                                   if (addToSet(reachesLocking, csins, o))
               toBeHandledAgain = true;     
                            }  
                      }
                      else {
                          //System.out.println("Adding " + prettyPrint((SSAInstruction)current) + " site to reachesLocking");
                          if (addToSet(reachesLocking, csins, current))
                             toBeHandledAgain = true;
                      }
                      workList.add(csins);
                      if (toBeHandledAgain) 
        visitedInst.remove(csins);      
        }


               }
            }
        }        
      
    }

    static boolean explorePredecessors(HashSet<IExplodedBasicBlock> visited, ExplodedControlFlowGraph graph, CGNode node, SSAInstruction orig, IExplodedBasicBlock pred, int monitorExitSeen) {

  if (visited.contains(pred)) return false;
            visited.add(pred);

            if (pred != null) {

            SSAInstruction pinst = pred.getInstruction();
            if (lockingInstructions.containsKey(orig))
               addToSet(reachesLocking, pinst, orig);
            else {
                HashSet<SSAInstruction> or = reachesLocking.get(orig);
                for(SSAInstruction o: or) {
                   addToSet(reachesLocking, pinst, o);
                }
            }


                   if (pinst instanceof SSAMonitorInstruction) {
                       SSAMonitorInstruction mi = (SSAMonitorInstruction) pinst;
                       if (mi.isMonitorEnter()) { 
                          if (monitorExitSeen > 0) 
                              monitorExitSeen--;
                          else { 
                              /*             
                              if (!lockingInstructions.containsKey(mi)) {
                                  //add to worklist and lockingInstructions 
                                  workList.add(mi);
                                  saveMonitorEnter(node, mi, null, reverseMode);           
                              }
                              */
                              if (lockingInstructions.containsKey(orig) && isDesiredEnclosingLockingInstruction(mi)) {
                                  addToSet(enclosedBy, orig, mi);
                                  addToSet(encloses, mi, orig);
                                  return true;
                              }
                              else if (!lockingInstructions.containsKey(orig) && isDesiredEnclosingLockingInstruction(mi)) { 
                                  // found the transitive enclosing, record it
                                  HashSet<SSAInstruction> syncInsts = reachesLocking.get(orig);
                                  for(SSAInstruction syncInst: syncInsts) {
              if (lockingInstructions.containsKey(syncInst)) {  
                                             addToSet(enclosedBy, syncInst, mi);
                                             addToSet(encloses, mi, syncInst);
              }
                                      
                                  }
                                  return true;
                              }    
                          }
                       }
                       else monitorExitSeen++;
                   }    


                   if (pred.isEntryBlock()) {
                     
                       return false;
       }
                   else {
                       java.util.Collection<IExplodedBasicBlock> preds =graph.getNormalPredecessors(pred);     
                       boolean foundEnclosing = false;           
                 for(IExplodedBasicBlock pr: preds) {
                           System.out.println(node);
         if (explorePredecessors(visited, graph, node, orig, pr, monitorExitSeen))
             foundEnclosing = true;
                        }
                       return foundEnclosing;
       }

      }
   
            return false;
    }

    private static String prettyPrint(SSAInstruction inst) {
        //if (inst instanceof SSAInvokeInstruction)
  //  return inst.toString();
        Triple<Integer, CGNode, IExplodedBasicBlock> contextInfo = instructionContext.get(inst);
        int instIndex = ((Integer)contextInfo.val1).intValue();
        CGNode node = (CGNode)contextInfo.val2;        
        String instSt = inst.toString();
        int pos = instSt.indexOf("(");
        if (pos >= 0)
           instSt = instSt.substring(0,pos); 
        return instSt + " " + prettyPrint(node.getIR(), instIndex);  
    }

    private static SSAInstruction getInvokeInstructionAtPC(IR ir, int pc) throws InvalidClassFileException {
      try {
      IBytecodeMethod method = (IBytecodeMethod)ir.getMethod(); 
      SSAInstruction[] insts = ir.getInstructions(); 
      for(int i=0; i<insts.length; i++) {

    if (method.getBytecodeIndex(i) == pc && insts[i] instanceof SSAInvokeInstruction)
        return insts[i];
      }
      }       
      catch(InvalidClassFileException e) { }
      catch(ClassCastException e) {}

      return null; 
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


    private static void removeFromSet(HashMap<SSAInstruction, HashSet<SSAInstruction>> oneToMany, SSAInstruction key, SSAInstruction value) {
        HashSet<SSAInstruction> set; 
  if (oneToMany.containsKey(key)) { 
      set  = (HashSet<SSAInstruction>)oneToMany.remove(key);
            set.remove(value); 
            oneToMany.put(key, set);
  }
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

    private static void addAllToSet( HashMap<IExplodedBasicBlock, HashSet<IClass>> oneToMany, IExplodedBasicBlock key, HashSet<IClass> value) {
        HashSet<IClass> set; 
  if (oneToMany.containsKey(key)) 
      set  = (HashSet<IClass>) oneToMany.remove(key);
  else 
      set  = new HashSet<IClass>();
        set.addAll(value);
        oneToMany.put(key, set); 
    }


    private static void addAllToMap(HashMap<SSAInstruction, HashMap<CGNode, HashMap<IExplodedBasicBlock, HashSet<IClass>>>> oneToMany, SSAInstruction inst, CGNode node, IExplodedBasicBlock bb, HashSet<IClass> threadClassSet) {
        
       // DEBUG CODE SECTION BEGIN
       for(IClass th: threadClassSet) {
          if (th.getName().toString().indexOf("HeartBeat") >= 0)
          {    
              System.out.println("WOW Adding " + th + " TO  " + prettyPrint(inst) + " IN " + node + " AT " + prettyPrint(bb.getInstruction()) ); 
              break;
          }
       }


       // DEBUG CODE SECTION END
        //System.out.println("ADDALL: " + "inst=" + inst + " node=" + node + " bb=" + bb );
        HashMap<CGNode, HashMap<IExplodedBasicBlock, HashSet<IClass>>> nodeMap;
  HashMap<IExplodedBasicBlock, HashSet<IClass>> bbMap;
        if (oneToMany.containsKey(inst)) {
      nodeMap = oneToMany.remove(inst);
            if (nodeMap.containsKey(node)) {
    bbMap = nodeMap.remove(node);
      }
      else {
    bbMap = new HashMap<IExplodedBasicBlock, HashSet<IClass>>();
      }            
  }
        else {
      nodeMap = new HashMap<CGNode, HashMap<IExplodedBasicBlock, HashSet<IClass>>>();
            bbMap = new HashMap<IExplodedBasicBlock, HashSet<IClass>>();
  } 
        addAllToSet(bbMap, bb, threadClassSet);
        nodeMap.put(node, bbMap);
        oneToMany.put(inst, nodeMap);
    }

    private static boolean addToSet(HashMap<MethodReference, HashSet<CGNode>> oneToMany, MethodReference key, CGNode value) {
        HashSet<CGNode> set; 
        if (oneToMany.containsKey(key)) 
            set  = oneToMany.remove(key);
        else 
            set  = new HashSet<CGNode>();
        boolean result = !set.contains(value);
        set.add(value);
        oneToMany.put(key, set);
        return result;
  }


    private static boolean addToSet(HashMap<SSAInstruction, HashSet<Quad>> oneToMany, SSAInstruction key, Quad value) {
        HashSet<Quad> set; 
        if (oneToMany.containsKey(key)) 
            set  = oneToMany.remove(key);
        else 
            set  = new HashSet<Quad>();
        boolean result = !set.contains(value);
        set.add(value);
        oneToMany.put(key, set);
        return result;
  }

    private static boolean addToSet(HashMap<SSAInstruction, HashSet<SSAInstruction>> oneToMany, SSAInstruction key, SSAInstruction value) {
        HashSet<SSAInstruction> set; 
  if (oneToMany.containsKey(key)) 
      set  = oneToMany.remove(key);
  else 
      set  = new HashSet<SSAInstruction>();
        boolean result = !set.contains(value);
        set.add(value);
        oneToMany.put(key, set);
        return result;
  }

    private static boolean addToSet(HashMap<SSAInstruction, HashSet<CGNode>> oneToMany, SSAInstruction key, CGNode value) {
        HashSet<CGNode> set; 
        if (oneToMany.containsKey(key)) 
            set  = oneToMany.remove(key);
        else 
            set  = new HashSet<CGNode>();
        boolean result = !set.contains(value);
        set.add(value);
        oneToMany.put(key, set);
        return result;
  }


    private static void addToSet(HashMap<IClass, HashSet<Quad>> oneToMany, IClass cl, Quad q) {
        HashSet<Quad> qset;
        if (oneToMany.containsKey(cl))
      qset = oneToMany.remove(cl);
        else {
            qset = new  HashSet<Quad>();
  }
        qset.add(q);
        oneToMany.put(cl, qset);
    }

    private static void addToSet(HashMap<IClass, HashMap<IClass, HashSet<Pair<CGNode, IExplodedBasicBlock>>>> oneToMany, IClass cl, IClass thcl, CGNode node, IExplodedBasicBlock bb) {
  HashMap<IClass, HashSet<Pair<CGNode, IExplodedBasicBlock>>> map;
        if (oneToMany.containsKey(cl))
      map = oneToMany.remove(cl);
        else {
            map = new HashMap<IClass, HashSet<Pair<CGNode, IExplodedBasicBlock>>>();
  }
        oneToMany.put(cl, map);
        HashSet<Pair<CGNode, IExplodedBasicBlock>> pset;
        if (map.containsKey(thcl)) 
      pset = map.remove(thcl);
        else {
           pset = new HashSet<Pair<CGNode, IExplodedBasicBlock>>();
  }
        map.put(thcl, pset);
        pset.add(new Pair<CGNode, IExplodedBasicBlock>(node, bb));
    }

    static void saveLockTypeAs(boolean enclosed, SSAInstruction inst) {
       OrdinalSet<? extends InstanceKey> lockSet = lockingInstructions.get(inst);
       for(InstanceKey ik : lockSet) {
          String iks  = ik.toString();
          int i = iks.indexOf("NEW");
          int j = iks.indexOf("@");
          String type = iks.substring(i, j-1);
          if ((enclosed == true) ? (enclosedType == null) : (enclosingType == null)) {
             if (enclosed) 
                enclosedType = iks;
             else enclosingType = iks;
             break;      
          }
          else break;
       }
        
    }



    // lockType == null means mi will be added to lockingInstructions
    private static void saveMonitorEnter(CGNode node, SSAMonitorInstruction mi) {        
       if (mi.isMonitorEnter()) {
               boolean added = false;
               int ref = mi.getRef();
               // Assume that ref is a local variable value number
               OrdinalSet<? extends InstanceKey> lockSet = pointerAnalysis.getPointsToSet(heapModel.getPointerKeyForLocal(node, ref));   
               for(InstanceKey ik  : lockSet) {
                  System.out.println(ik + " VS " + ik.getConcreteType());
      if (ik.toString().indexOf(enclosedType) >= 0 || ik.toString().indexOf(enclosingType) >= 0) {
                     lockingInstructions.put(mi, lockSet);
                     added = true;
                     break;
                  }
               }
         if (SUBCLASS_HANDLING && !added && lockSet.size() > 0) { 
      // try subclasses if the lock type is other than java.lang.Object
                  Triple<Integer, CGNode, IExplodedBasicBlock> context = instructionContext.get(mi);
                  IR ir = context.val2.getIR();
                  TypeInference ti = TypeInference.make(ir, false); 
      IClass cl = (IClass)ti.getType(mi.getRef()).getType(); 
                  if (cl.getName().toString().indexOf("Ljava/lang/Object") < 0) {
                     java.util.Collection<IClass> subcl = getImmediateSubclasses(cl);
                     System.out.println("SUBCLASSES OF " + cl);
                     for(IClass sub : subcl) {
                       // We need to append that > as enclosingType and enclosedType also have at their end.. 
           String subTypeName = sub.getName().toString() + ">";
                       System.out.println("(1) SUBTYPE NAME=" + subTypeName);
           if (subTypeName.indexOf(enclosingType) >= 0 || subTypeName.indexOf(enclosedType) >= 0) 
              lockingInstructions.put(mi, lockSet);
               }
             }
                   
         }              
       
               if (SUBCLASS_HANDLING && lockSet.size() == 0) {// the lock is a field instance
       try {
                    IR ir = node.getIR();
                    SSAInstruction[] insts = ir.getInstructions();
                    IBytecodeMethod method = (IBytecodeMethod)ir.getMethod();
                    Triple<Integer, CGNode, IExplodedBasicBlock> contextInfo = instructionContext.get(mi);
                    int bytecodeIndex = method.getBytecodeIndex(contextInfo.val1);
                    int sourceLineNum = method.getLineNumber(bytecodeIndex);
                    for(int i=0; i < insts.length; i++) {
                       if (insts[i] != null) {
         Triple<Integer, CGNode, IExplodedBasicBlock> contextInfo2 = instructionContext.get(insts[i]);
                           int bi = method.getBytecodeIndex(contextInfo2.val1);
                           int sl =  method.getLineNumber(bi);
                           
                           if (sourceLineNum == sl) { 
             System.out.println("FIELD ACCESS " + prettyPrint(insts[i]));
                              try {
             SSAGetInstruction gis = (SSAGetInstruction) insts[i];
                               String nameOfLockType = gis.getDeclaredFieldType().toString();
                               IClass baseLockType = cha.lookupClass(gis.getDeclaredFieldType());
                               java.util.Collection<IClass> subcl = getImmediateSubclasses(baseLockType);
                               //System.out.println("POTENTIAL LOCK TARGETS : " + cha.getNumberOfImmediateSubclasses(baseLockType));
                               boolean subtype = false;
                               if (baseLockType.getName().toString().indexOf("Ljava/lang/Object") < 0) {
                               for(IClass sub : subcl) {
                                   // We need to append that > as enclosingType and enclosedType also have at their end.. 
           String subTypeName = sub.getName().toString() + ">";
                                   //System.out.println("(2) SUBTYPE NAME=" + subTypeName);
           if (subTypeName.indexOf(enclosingType) >= 0 || subTypeName.indexOf(enclosedType) >= 0) {
               subtype = true;
               //System.out.println("SUPER TYPE OF LOCK! " + sub.getName());
           }
             }
             }
                               if (subtype || nameOfLockType.indexOf(enclosingType) >= 0 || nameOfLockType.indexOf(enclosedType) >= 0) {

                               IClass cl = node.getMethod().getDeclaringClass();
                               IField f = cl.getField(gis.getDeclaredField().getName());
                               if (f.isStatic())
                                  lockSet = pointerAnalysis.getPointsToSet(heapModel.getPointerKeyForStaticField(f));  
                               else if (!node.getMethod().isStatic()){
                                   OrdinalSet<? extends InstanceKey> thisLockSet = pointerAnalysis.getPointsToSet(heapModel.getPointerKeyForLocal(node, 1));  
                                  
                                  lockSet = OrdinalSet.<InstanceKey>empty();                                    
                                   for(InstanceKey ik  : thisLockSet) {
                                       //System.out.println("OBJECTS POINTED BY THIS " + ik);
               OrdinalSet.<InstanceKey>unify((OrdinalSet<InstanceKey>)lockSet, (OrdinalSet<InstanceKey>)pointerAnalysis.getPointsToSet(heapModel.getPointerKeyForInstanceField(ik,f)));
                                       //System.out.println("FIELD KEYS: " + heapModel.getPointerKeyForInstanceField(ik,f));
                                       //System.out.println("FIELD OBJECTS: " + pointerAnalysis.getPointsToSet(heapModel.getPointerKeyForInstanceField(ik,f)));
           }
                                   for(InstanceKey ik  : lockSet) {
                                       System.out.println(ik + " !VS! " + ik.getConcreteType());
           }

             } 
                               //System.out.println("LOCK TYPE " + nameOfLockType);

                                  lockingInstructions.put(mi, lockSet);
             }
            }
                               catch(Exception e) {
           System.out.println("Cast failed! for " + insts[i].getClass());
                                 
             }
         }
           }
        }

       }
                   catch(InvalidClassFileException e) {
           System.out.println(e);
       }

         }
         }


                    //System.out.println(mi + "(" + prettyPrint(mi) + ") referencing lock v" + ref);
    }
       
    private static IClass getImmediateSuperclass(IClass cl) {
        java.util.Iterator<IClass> clIt = cha.iterator();
  while(clIt.hasNext()) {
     IClass supcl = clIt.next();
           System.out.println("Is " + cl + "subclass of " + supcl);
     if (cha.isSubclassOf(cl, supcl) && !cl.equals(supcl)) {
              System.out.println("yes!"); 
       return supcl;     
           }
  }
        return null;
    }

    private static ArrayList<IClass> getImmediateSubclasses(IClass cl) {
  ArrayList<IClass> subcllist = new ArrayList<IClass>();
         java.util.Iterator<IClass> clIt = cha.iterator();
  while(clIt.hasNext()) {
     IClass subcl = clIt.next();
     if (cha.isSubclassOf(subcl, cl) && !subcl.equals(cl)) 
         subcllist.add(subcl);
  }
        return subcllist;      
    }

    // lockType == null means is will be added to lockingInstructions
    private static void saveSyncMethodCall(CGNode node, SSAInvokeInstruction is) {
        //System.out.println("Saving sync method call..");
  java.util.Set<CGNode> mnodes = cg.getNodes(is.getCallSite().getDeclaredTarget());
  //java.util.Set<CGNode> mnodes = getPossibleNodes(is);  
            boolean sync = false;
            OrdinalSet<? extends InstanceKey> lockSet = OrdinalSet.<InstanceKey>empty();
            for(CGNode n : mnodes) {
                if (n.getMethod().isSynchronized())  {
                    //System.out.println(is + "(" + prettyPrint(is) + ") referencing this/class"); 
                    //System.out.println(n.getMethod().toString() + " is synchronized");
                    if (!n.getMethod().isStatic()) {

      lockSet = OrdinalSet.<InstanceKey>unify((OrdinalSet<InstanceKey>)lockSet,(OrdinalSet<InstanceKey>)pointerAnalysis.getPointsToSet(heapModel.getPointerKeyForLocal(n, 1)));
        } 
        // for static methods the lock set is null!
                    sync = true;// assumes in every context 
        if (!lockingMethods.contains(n)) {
                  lockingMethods.add(n); 
                        //System.out.println("Synchronized method node " + n);
        }
    }
                //addToSet(callSites, n, inst); 

      } 
      boolean added = false;
            if (sync) {

                   for(InstanceKey ik  : lockSet) {
           if (ik.toString().indexOf(enclosedType) >= 0 || ik.toString().indexOf(enclosingType) >= 0) {        
         lockingInstructions.put(is, lockSet);
                           added = true;
                          break;
                      }
                   }
      }
      // superclass method may happen not to be synchronized
       if (SUBCLASS_HANDLING && !added) {
           // Try subclasses
           IClass baseLockType = cha.lookupClass(is.getDeclaredTarget().getDeclaringClass());
                       if (baseLockType != null) {
                       java.util.Collection<IClass> subcl = getImmediateSubclasses(baseLockType);
                       boolean subtype = false;
                       if (baseLockType.getName().toString().indexOf("Ljava/lang/Object") < 0) {
                          for(IClass sub : subcl) {
                             // We need to append that > as enclosingType and enclosedType also have at their end..
                              String signature = is.getDeclaredTarget().getSignature();
                              signature = signature.substring(signature.indexOf("("));  
            //System.out.println(signature);
                              MethodReference mref = MethodReference.findOrCreate(ClassLoaderReference.Application, StringStuff.deployment2CanonicalTypeString(baseLockType.getName().toString()), is.getDeclaredTarget().getName().toString(),signature);
            java.util.Set<IMethod> sm = cha.getPossibleTargets(sub, mref);
            for(IMethod m: sm) { 
          if (m != null && !m.isSynchronized()) continue;
           String subTypeName = sub.getName().toString() + ">";
                             //System.out.println("(SYNC METHOD) SUBTYPE NAME=" + subTypeName);
           if (subTypeName.indexOf(enclosingType) >= 0 || subTypeName.indexOf(enclosedType) >= 0) {
               subtype = true;
                                       lockingInstructions.put(is, lockSet);
                                       break;
               //System.out.println("SUPER TYPE OF LOCK! " + sub.getName());
           }
            }
        }
           }
                      }
       }
            
    }


    static void checkFakeAndAdd(SSAInstruction inst, OrdinalSet<? extends InstanceKey> lockSet) {
        java.util.Set<SSAInstruction> linstSet = lockingInstructions.keySet();
  if (isFake(inst)) {     
      for(SSAInstruction linst : linstSet) {
    if (same(inst, (SSAInstruction)linst))
        return;
      }
            lockingInstructions.put(inst, lockSet); 
  }
        else {
            Object l = null;
      for(SSAInstruction linst : linstSet) 
    if (isFake((SSAInstruction)linst) && same(inst, (SSAInstruction)linst)) {
        l = linst;
                    break;           
    }
            lockingInstructions.remove(l);
            lockingInstructions.put(inst, lockSet);
  }
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

    private static void checkSaveLockingInstruction(CGNode node, SSAInstruction inst) {
        if (inst == null) return;
        if (inst instanceof SSAMonitorInstruction) {
      saveMonitorEnter(node, (SSAMonitorInstruction)inst);
  }
        else if (inst instanceof SSAInvokeInstruction || ssaInvokeInstructionClass.isAssignableFrom(inst.getClass()) ){
            saveSyncMethodCall(node, (SSAInvokeInstruction)inst);
  }
    }
 



    private static void findSaveLockingInstructionInMethodOfClassAtLine(String className, String methodName, int lineNo, String lockType) throws InvalidClassFileException {
        System.out.println("Searching for instruction " + className + "." + methodName + " at line " + lineNo);
        for(CGNode node: icfg.getCallGraph()) { 
      if (node.getMethod().getDeclaringClass().getName().toString().indexOf(className) >= 0) {    
    //System.out.println("Candidate class=" + node.getMethod().getDeclaringClass().getName().toString());           
                //System.out.println("Is " + node.getMethod().getName().toString() + " what we're looking for?");
                if (node.getMethod().getName().toString().indexOf(methodName) >= 0) {
                    System.out.println("Candidate node=" + node + "candidate method=" + node.getMethod().getName().toString());
                    IR ir = node.getIR();
                    if (ir == null) continue;
                    SSAInstruction[] insts = ir.getInstructions();
                    for(int i=0; i < insts.length; i++) {
                       IBytecodeMethod method = (IBytecodeMethod)ir.getMethod();
                       int bytecodeIndex = method.getBytecodeIndex(i);
                       int sourceLineNum = method.getLineNumber(bytecodeIndex);
                       System.out.println("Line no=" + sourceLineNum);
                       if (insts[i] != null) {
              System.out.println(prettyPrint(insts[i]));
                           System.out.println("sourceLineNum=" + sourceLineNum + " " + insts[i].getClass().getName());
                           try {
             SSAGetInstruction gis = (SSAGetInstruction) insts[i];
         System.out.println("field type=" + gis.getDeclaredFieldType()); 
         }
                           catch(Exception e) {
                               System.out.println("Cast failed! for " + insts[i].getClass());
         }
           }
                       if (sourceLineNum == lineNo) {
                           seedInstruction = insts[i];

         checkSaveLockingInstruction(node, insts[i]);
                           // same line may hold multiple instructions
                           // so keep looking

                           if (insts[i] instanceof SSAInvokeInstruction)
                              break;
                       }
        }  
         }
      }
  }
        // Add other locking instructions with the same lock type

        return ;
    }

    static void addLockingInstructions() {
       for(CGNode node: icfg.getCallGraph()) { 
           //if (!isATarget(node)) continue; 
           ExplodedControlFlowGraph graph = (ExplodedControlFlowGraph)  icfg.getCFG(node);

           if (graph == null) continue; 
           IR ir = node.getIR();
           if (ir == null) continue;
           SSAInstruction[] insts = ir.getInstructions();
           for(int i=0; i < insts.length; i++) {
              SSAInstruction inst = insts[i];
              checkSaveLockingInstruction(node, inst);
           }
       }   
    }

    private static void initLockingInstructions(String targetFile) throws Exception, IOException, InvalidClassFileException {
  BufferedReader bufR = new BufferedReader(new FileReader(targetFile));
        String line; 
        int no = 0;
        int lineNo = 0;
        while ((line = bufR.readLine()) != null) {
            no++;
            if (line.indexOf("//") >= 0) continue;
            if (line.indexOf("refPoint") >= 0) {
                String[] sa = line.substring(line.indexOf("=")+1, line.length()).split(";");
                if (sa.length != 7)
                    throw new Exception("Expected: pre/onward;classname;methodname(caller);methodname(callee)/monitorenterlineNo;lockType1;lockType2");
                searchDirection = sa[0]; 
                if (sa[0].equals("pre") && sa[0].equals("onward") && sa[0].equals("mixed"))
                   throw new Exception("Direction can be pre, mixed, or onward");
                enclosedClass = sa[1];  
                enclosingClass = sa[1];
                enclosedMethod = sa[2];
                enclosedInstruction = sa[3];
                enclosingInstruction = sa[3];
                lineNo = Integer.parseInt(sa[4]);
                enclosedLineNo = sa[4];
                enclosingLineNo = sa[4];
                // since substring search is done, adding > ensures we get the right locking instructions 
                if (sa[0].equals("onward")) {
                   enclosedType = sa[5] + ">";
                   enclosedTypeTrimmed = sa[5];
                   enclosingType = sa[6] + ">";
                   enclosingTypeTrimmed = sa[6];                   
    }
                else if (sa[0].equals("pre")) {
                   enclosingType = sa[5] + ">";
                   enclosingTypeTrimmed = sa[5];
                   enclosedType = sa[6] + ">";
                   enclosedTypeTrimmed = sa[6];
    }
            }
            else throw new Exception("text not recognized at line " + no + " in file "  + targetFile);
        }              
        System.out.println("enclosedClass=" + enclosedClass);
        System.out.println("enclosedMethod=" + enclosedMethod);
        System.out.println("enclosingInstruction=" + enclosingInstruction);   
        System.out.println("enclosedLineNo=" + lineNo);
        System.out.println("enclosedType=" + enclosedType);
        System.out.println("enclosingType=" + enclosingType); 
  findSaveLockingInstructionInMethodOfClassAtLine(enclosedClass, enclosedMethod, lineNo, enclosedType);        
        bufR.close();
        addLockingInstructions();
    }

    private static void configureAndCreateCallGraph(String scopeFile, String mainClass, String entryClass) throws IOException, ClassHierarchyException, CallGraphBuilderCancelException  {
    File exclusionsFile = null;
    AnalysisScope scope = AnalysisScopeReader.readJavaScope(scopeFile, exclusionsFile, CheckPatch.class.getClassLoader()); 
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
    for (IMethod m : klass.getDeclaredMethods()) {
      System.out.println("Adding method " + m + " as an entry point");
      //if (m.isPublic()) {
        result.add(new DefaultEntrypoint(m, cha));
      //}
    }
    return result;
  }
}