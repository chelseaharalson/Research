package mycode_locks;

/*******************************************************************************
 * Copyright (c) 2008 IBM Corporation.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     IBM Corporation - initial API and implementation
 *******************************************************************************/


import java.io.File;
import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Iterator;
import java.util.Properties;
import java.util.HashSet;


import com.ibm.wala.classLoader.IBytecodeMethod;
import com.ibm.wala.classLoader.IClass;
import com.ibm.wala.classLoader.IMethod;
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
import com.ibm.wala.shrikeCT.InvalidClassFileException; 
import com.ibm.wala.ssa.IR;
import com.ibm.wala.ssa.SSACFG;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.ssa.SSAMonitorInstruction;
import com.ibm.wala.ssa.SSAInvokeInstruction;
import com.ibm.wala.ssa.analysis.ExplodedControlFlowGraph;
import com.ibm.wala.ssa.analysis.IExplodedBasicBlock;
import com.ibm.wala.types.ClassLoaderReference;
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


import java.util.HashMap;
/**
 * Driver that constructs a call graph for an application specified via a scope file.  
 * Useful for getting some code to copy-paste.    
 */
public class FindLockingPair {

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

    static String enclosingClass;

    static String enclosingInstruction;

    static String enclosedInstruction;

    static String enclosedClass;

    static String enclosedMethod;

    static String enclosingType;

    static String enclosingTypeTrimmed;

    static String enclosedType;

    static String enclosedTypeTrimmed;

    static String enclosingLineNo;

    static String enclosedLineNo;

    static SSAInstruction seedInstruction;

    static int totalNumPairs = 0;
 
    static int numPublicPairs = 0;

    static ArrayList<SSAInstruction> referencePoints = new ArrayList<SSAInstruction>();

    static String searchDirection = " ";

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

   Object val1;
   Object val2;
         Object val3;

         public Triple(Object v1, Object v2, Object v3) {
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

   static String lockSetToString(OrdinalSet<? extends InstanceKey> lockset) {
       String result = "";
       for(java.util.Iterator<? extends InstanceKey> ikeys = lockset.iterator(); ikeys.hasNext();) {
            InstanceKey is = ikeys.next();
            result = result + is + " " + is.hashCode(); 
        }
       return result;
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


 
    for(CGNode node: icfg.getCallGraph()) { 
        if (!isATarget(node)) continue; 
  ExplodedControlFlowGraph graph = (ExplodedControlFlowGraph)  icfg.getCFG(node);

        if (graph == null) continue; 
        IR ir = node.getIR();
        if (ir == null) continue;
        SSAInstruction[] insts = ir.getInstructions();
        for(int i=0; i < insts.length; i++) {
            SSAInstruction inst = insts[i];
            instructionContext.put(inst, new Triple(i, node, graph.getBlockForInstruction(i)));
            addCallSites(node, inst);
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

   for(SSAInstruction refPoint : referencePoints) { 
       Triple<Integer, CGNode, IExplodedBasicBlock> contextInfo = instructionContext.get(refPoint);
       HashSet<Pair<SSAInstruction, SSAInstruction>> pairs = new HashSet<Pair<SSAInstruction, SSAInstruction>>();
       if (searchDirection.equals("pre"))
          findPairPreFromInstruction(refPoint, pairs, (CGNode)contextInfo.val2, enclosingType, enclosedType, new HashSet<SSAInstruction>(), 0);
       else if (searchDirection.equals("mixed")) {
          HashSet<SSAInstruction> preInsts = new HashSet<SSAInstruction>();
          findEnclosing(refPoint, preInsts, (CGNode)contextInfo.val2, enclosingType, new HashSet<SSAInstruction>(), 0); 
          for(SSAInstruction pre : preInsts) 
             findEnclosedInMethodFrom(pre, pairs, (CGNode)contextInfo.val2,  (IExplodedBasicBlock)contextInfo.val3, enclosedType, new HashSet<SSAInstruction>());           
       }
       else if (searchDirection.equals("onward")) {
          findPairInMethod(refPoint, pairs, (CGNode)contextInfo.val2, enclosingType, enclosedType, new HashSet<SSAInstruction>()); 
       }
       System.out.println("Locking pairs:");
       for(Pair<SSAInstruction, SSAInstruction> pair : pairs) {
          System.out.println(prettyPrint(pair.val1) + " {{{ " + prettyPrint(pair.val2) + " }}}");
       }           
    }
            
    long end = System.currentTimeMillis();
    System.out.println("done");
    System.out.println("took " + (end-start) + "ms");
    System.out.println(CallGraphStats.getStats(cg));


  }

  


    static void findPairPreFromInstruction(SSAInstruction refPoint, HashSet<Pair<SSAInstruction, SSAInstruction>> set, CGNode node, String lockType1, String lockType2, HashSet<SSAInstruction> visited, int monitorExitSeen) {
        if (refPoint == null) { 
      //System.out.println("CALLSITES for " + node.getMethod());
              HashSet<SSAInstruction> csites = callSites.get(node);
              if (csites == null) return;
              for(SSAInstruction csite : csites) {            
               Triple<Integer, CGNode, IExplodedBasicBlock>  contextInfo2 = instructionContext.get(csite);
               if (node.getMethod().isSynchronized()) {
       String lt = getPossibleLock(csite);
       //System.out.println("LOCK TYPE " + lt + " VERSUS " + lockType2);
                  if (lt != null && lt.equals(lockType2)) { 
                     findEnclosingFrom(csite, set, (CGNode)contextInfo2.val2, (IExplodedBasicBlock) contextInfo2.val3, lockType1, visited, 0);
                  }  
               }
               else findPairPreFromInstruction(csite, set, (CGNode)contextInfo2.val2, lockType1, lockType2, visited, 0);
        } 
 
           return;
  }
        if (visited.contains(refPoint)) { 
            //System.out.println("ALREADY VISITED!");
            return;
        }
        //System.out.println("PAIR PRE: " + prettyPrint(refPoint) + " NODE " + node); 
        visited.add(refPoint); 
        Triple<Integer, CGNode, IExplodedBasicBlock> contextInfo = instructionContext.get(refPoint);
        ExplodedControlFlowGraph graph = (ExplodedControlFlowGraph)  icfg.getCFG(node);   
        if (refPoint instanceof SSAMonitorInstruction) {
            if (((SSAMonitorInstruction)refPoint).isMonitorEnter()) {        
                if (monitorExitSeen > 0)
                    monitorExitSeen--;
                else {                 
                   String lt = getPossibleLock(refPoint);  
                   System.out.println("LOCK TYPE " + lt + " VERSUS " + lockType2);
                   if (lt != null && lt.equals(lockType2)) {
                     java.util.Collection<IExplodedBasicBlock> preds = graph.getNormalPredecessors((IExplodedBasicBlock)contextInfo.val3);
                     for(IExplodedBasicBlock pred : preds) {    
                        findEnclosingFrom(refPoint, set, node, pred, lockType1, visited, monitorExitSeen);
                     }
                     return;
                   }
               }
            }
            else monitorExitSeen++;
        }
        java.util.Collection<IExplodedBasicBlock> preds = graph.getNormalPredecessors((IExplodedBasicBlock)contextInfo.val3);
        for(IExplodedBasicBlock pred : preds) {    
           findPairPreFromInstruction(pred.getInstruction(), set, node, lockType1, lockType2, visited, monitorExitSeen);
        }
           
        
    }


    static void findEnclosingFrom(SSAInstruction enclosed, HashSet<Pair<SSAInstruction,SSAInstruction>> set, CGNode node, IExplodedBasicBlock bb, String lockType, HashSet<SSAInstruction> visited, int monitorExitSeen) {
        if (bb == null) return;
        SSAInstruction refPoint = bb.getInstruction(); 
        if (refPoint == null) {   
           HashSet<SSAInstruction> csites = callSites.get(node); 
           if (csites == null) return;
           for(SSAInstruction csite : csites) {            
               Triple<Integer, CGNode, IExplodedBasicBlock> contextInfo2 = instructionContext.get(csite); 
               if (node.getMethod().isSynchronized()) {
                  String lt = getPossibleLock(csite);  
                  if (lt != null && lt.equals(lockType)) { 
                      set.add(new Pair(csite, enclosed));
                  }  
               }
               else findEnclosingFrom(enclosed, set, (CGNode)contextInfo2.val2, (IExplodedBasicBlock)contextInfo2.val3, lockType, visited, 0);
           }  
           return;
        }
        if (visited.contains(refPoint)) return;
        //System.out.println("PAIR ENCLOSED: " + prettyPrint(enclosed) + " PRE: " + prettyPrint(refPoint)); 
        visited.add(refPoint); 
        Triple<Integer, CGNode, IExplodedBasicBlock> contextInfo = instructionContext.get(refPoint);
        ExplodedControlFlowGraph graph = (ExplodedControlFlowGraph)  icfg.getCFG(node);    
        if (refPoint instanceof SSAMonitorInstruction) {
            if (((SSAMonitorInstruction)refPoint).isMonitorEnter()) {        
                if (monitorExitSeen > 0)
                    monitorExitSeen--;
                else {
                   String lt = getPossibleLock(refPoint);  
                   if (lt != null && lt.equals(lockType)) {
                       set.add(new Pair(refPoint, enclosed));                  
                       return;
                   }
               }
            }
            else monitorExitSeen++;
        }
        java.util.Collection<IExplodedBasicBlock> preds = graph.getNormalPredecessors((IExplodedBasicBlock)contextInfo.val3);
        for(IExplodedBasicBlock pred : preds) {    
              findEnclosingFrom(enclosed, set, node, pred, lockType, visited, monitorExitSeen);
        }
    }



    static void findEnclosing(SSAInstruction refPoint, HashSet<SSAInstruction> set, CGNode node, String lockType, HashSet<SSAInstruction> visited, int monitorExitSeen) {
        if (refPoint == null);
        if (visited.contains(refPoint)) return;
        visited.add(refPoint); 
        Triple<Integer, CGNode, IExplodedBasicBlock> contextInfo = instructionContext.get(refPoint);
        ExplodedControlFlowGraph graph = (ExplodedControlFlowGraph)  icfg.getCFG(node);   
        if (refPoint instanceof SSAMonitorInstruction) {
      if (((SSAMonitorInstruction)refPoint).isMonitorEnter()) {        
    if (monitorExitSeen > 0)
        monitorExitSeen--;
                else {
             String lt = getPossibleLock(refPoint);  
                   if (lt != null && lt.indexOf(">") >= 0)  
                lt = lt.substring(0, lt.indexOf(">"));
                   if (lt != null && lt.equals(lockType)) {
           set.add(refPoint);                  
                       return;
                   }
         }
      }
            else monitorExitSeen++;
  }
        if (((IExplodedBasicBlock)contextInfo.val3).isEntryBlock()) {
     HashSet<SSAInstruction> csites = callSites.get(node); 
           if (csites == null) return;
           for(SSAInstruction csite : csites) {            
         if (node.getMethod().isSynchronized()) {
            String lt = getPossibleLock(csite);  
                  if (lt != null && lt.indexOf(">") >= 0)  
               lt = lt.substring(0, lt.indexOf(">"));
                  if (lt != null && lt.equals(lockType)) { 
          set.add(csite);
      }  
         }
         else findEnclosing(csite, set, (CGNode)contextInfo.val2, lockType, visited, 0);
     }  
  }        
        else {
           java.util.Collection<IExplodedBasicBlock> preds = graph.getNormalPredecessors((IExplodedBasicBlock)contextInfo.val3);
           for(IExplodedBasicBlock pred : preds) {    
              findEnclosing(pred.getInstruction(), set, node, lockType, visited, monitorExitSeen);
           }
        }
    }
    
    static void findAccessMethodInst(SSAInvokeInstruction is) {
      java.util.Set<CGNode> mnodes = cg.getNodes(is.getCallSite().getDeclaredTarget());
      
      for (CGNode node: mnodes) {
        //System.out.println("Find access: " + node);
        if (node.getMethod().toString().contains("access$")) {
          System.out.println("Find access NODE: " + node);
          IR ir = node.getIR();
          if (ir == null) continue;
          SSAInstruction[] insts = ir.getInstructions();
          for(int i=0; i < insts.length; i++) {
             SSAInstruction inst = insts[i];
             if (inst != null) {
               System.out.println("Find Access Method Inst: " + inst);
             }
             /*if (inst instanceof SSAInvokeInstruction) {
               System.out.println("Find Access Method Inst: " + inst);
             }*/
          }
        }
      }  
   }

    static void findPairInMethod(SSAInstruction refPoint, HashSet<Pair<SSAInstruction, SSAInstruction>> set, CGNode node, String lockType1, String lockType2, HashSet<SSAInstruction> visited) { 
        if (refPoint == null) return;
        if (visited.contains(refPoint)) return;
        visited.add(refPoint); 
        System.out.println("FIND_PAIR " + prettyPrint(refPoint)); 
        Triple<Integer, CGNode, IExplodedBasicBlock> contextInfo = instructionContext.get(refPoint);
        ExplodedControlFlowGraph graph = (ExplodedControlFlowGraph)  icfg.getCFG(node);   
        
        //System.out.println("REF POINT: " + refPoint);
        //System.out.println("Lock Type: " + lockType1);
        
        if (refPoint instanceof SSAMonitorInstruction) {
          if (((SSAMonitorInstruction)refPoint).isMonitorEnter()) {
             String lt = getPossibleLock(refPoint);  
             //System.out.println("LT!!!!!!! " + lt);
             if (lt != null && lt.indexOf(">") >= 0)  
                lt = lt.substring(0, lt.indexOf(">"));
                   if (lt != null && lt.equals(lockType1)) {               
                     java.util.Collection<IExplodedBasicBlock> succB = graph.getNormalSuccessors((IExplodedBasicBlock)contextInfo.val3); 
                      for(IExplodedBasicBlock succ : succB) 
                        findEnclosedInMethodFrom(refPoint, set, node, succ, lockType2, visited);
                   }  
          }       
        }       
        else if (refPoint instanceof SSAInvokeInstruction) {
           java.util.Set<CGNode> nodes = cg.getNodes(((SSAInvokeInstruction)refPoint).getDeclaredTarget()); 
           String lt = getPossibleLock(refPoint);
           
           SSAInvokeInstruction refPt = (SSAInvokeInstruction) refPoint;
           findAccessMethodInst(refPt);
           //System.out.println("LT!!!!!!! " + lt);
                 if (lt != null && lt.indexOf(">") >= 0)  
                   lt = lt.substring(0, lt.indexOf(">"));
                 if (lt != null && lt.equals(lockType1)) {  
                    for(CGNode mnode : nodes) {
                       ExplodedControlFlowGraph mgraph = (ExplodedControlFlowGraph)  icfg.getCFG(mnode);
                       //System.out.println("Mnodes1: " + mnode);
                       findEnclosedInMethodFrom(refPoint, set, mnode, mgraph.entry(), lockType2, visited);  
                    }
                  }
                 else {
                      for(CGNode mnode : nodes) {
                       ExplodedControlFlowGraph mgraph = (ExplodedControlFlowGraph)  icfg.getCFG(mnode);
                       //System.out.println("Mnodes2: " + mnode);
                       findPairInMethod(mgraph.entry().getInstruction(), set, mnode, lockType1, lockType2, visited);
                      }         
                 }
        }
        java.util.Collection<IExplodedBasicBlock> succB = graph.getNormalSuccessors((IExplodedBasicBlock)contextInfo.val3); 
        for(IExplodedBasicBlock succ : succB) 
          findPairInMethod(succ.getInstruction(), set, node, lockType1, lockType2, visited); 
    }

    static void findEnclosedInMethodFrom(SSAInstruction enclosing, HashSet<Pair<SSAInstruction, SSAInstruction>> set, CGNode node,  IExplodedBasicBlock bb, String lockType, HashSet<SSAInstruction> visited) {
        if (bb == null) return;
        SSAInstruction refPoint = bb.getInstruction();
        if (refPoint == null) return;
        if (visited.contains(refPoint)) return;
        visited.add(refPoint); 
        System.out.println("FIND_ENCLOSED " + prettyPrint(refPoint)); 
        Triple<Integer, CGNode, IExplodedBasicBlock> contextInfo = instructionContext.get(refPoint);
        ExplodedControlFlowGraph graph = (ExplodedControlFlowGraph)  icfg.getCFG(node);    
        if (refPoint instanceof SSAMonitorInstruction) {
      if (((SSAMonitorInstruction)refPoint).isMonitorEnter()) {
         String lt = getPossibleLock(refPoint);  
               if (lt != null && lt.indexOf(">") >= 0)  
            lt = lt.substring(0, lt.indexOf(">"));
               if (lt != null && lt.equals(lockType)) {               
       set.add(new Pair(enclosing, refPoint)); 
         }  
      }       
  }       
  else if (refPoint instanceof SSAInvokeInstruction) {
     java.util.Set<CGNode> nodes = cg.getNodes(((SSAInvokeInstruction)refPoint).getDeclaredTarget()); 
     String lt = getPossibleLock(refPoint);
           if (lt != null && lt.indexOf(">") >= 0)  
         lt = lt.substring(0, lt.indexOf(">"));
           if (lt != null && lt.equals(lockType)) {  
              set.add(new Pair(enclosing, refPoint)); 
            }
      else {
                for(CGNode mnode : nodes) {
                 ExplodedControlFlowGraph mgraph = (ExplodedControlFlowGraph)  icfg.getCFG(mnode);
     findEnclosedInMethodFrom(enclosing, set, mnode,  mgraph.entry(), lockType, visited);
    }              
      }
  }
        java.util.Collection<IExplodedBasicBlock> succB = graph.getNormalSuccessors((IExplodedBasicBlock)contextInfo.val3); 
        for(IExplodedBasicBlock succ : succB) 
      findEnclosedInMethodFrom(enclosing, set, node, succ, lockType, visited);           
         
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
        if (!filterAsEnclosed((SSAInstruction)q.val1) || !filterAsEnclosing((SSAInstruction)q.val2))
      return;            
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

    static String getPossibleLock(SSAInstruction inst)  {
      if (inst instanceof SSAInvokeInstruction) {
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
      }
      else if (inst instanceof SSAMonitorInstruction) {
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
      } 
      return null;
    }

    static String getLockType(SSAInstruction inst) throws Exception {
      if (inst instanceof SSAInvokeInstruction) {
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
      }
      else if (inst instanceof SSAMonitorInstruction) {
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

    static boolean isDesiredEnclosingLockingInstruction(SSAInstruction is) {


        if (is instanceof SSAInvokeInstruction) {
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
        else if (is instanceof SSAMonitorInstruction) {
            if (((SSAMonitorInstruction)is).isMonitorEnter()) {
               int ref = ((SSAMonitorInstruction)is).getRef();
               Triple<Integer, CGNode, IExplodedBasicBlock> contextInfo = instructionContext.get(is);
               CGNode node = (CGNode)contextInfo.val2;
               OrdinalSet<? extends InstanceKey> lockSet = pointerAnalysis.getPointsToSet(heapModel.getPointerKeyForLocal(node, ref));
               for(InstanceKey ik : lockSet) {
                   //System.out.println("DESIRED LOCK type= " + enclosingType +" in " + ik.toString());
                   if (ik.toString().indexOf(enclosingType) >= 0 || ik.toString().indexOf(enclosedType) >= 0)
                        return true; 
               }
               return false;
           } 
           else return false;
        }
        else return false;
      
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
            return (lockSet1 != null && lockSet2 != null && (lockSetToString(lockSet1).equals(lockSetToString(lockSet2)) || OrdinalSet.<InstanceKey>intersect((OrdinalSet<InstanceKey>)lockSet1, (OrdinalSet<InstanceKey>)lockSet2).size() > 0));
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
            System.out.println("printPair????");
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


    private static void computeReverseAliasedEnclosingPairs() throws Exception {

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
         printPair(rq.val1, rq.val2, rq.val3, rq.val4); 
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

    private static void reachabilityAnalysis() {
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

    static void findClosestPredecessor(SSAInstruction pivot, String targetLockType, ArrayList<SSAInstruction> result) throws Exception {
       Triple<Integer, CGNode, IExplodedBasicBlock> contextInfo = instructionContext.get(pivot);      
       explorePredecessor(enclosingType, new HashSet<IExplodedBasicBlock>(), (ExplodedControlFlowGraph)icfg.getCFG((CGNode)contextInfo.val2), (CGNode)contextInfo.val2, (IExplodedBasicBlock) contextInfo.val3, result, true, 0);
    }

    static boolean explorePredecessor(String targetLockType, HashSet<IExplodedBasicBlock> visited, ExplodedControlFlowGraph graph, CGNode node, IExplodedBasicBlock  pred, ArrayList<SSAInstruction> result, boolean skip, int monitorExitSeen) throws Exception {
      if (visited.contains(pred))
         return false;
      visited.add(pred);
      SSAInstruction predI = pred.getInstruction();
      System.out.println("Checking predecessor " + prettyPrint(predI));
      if (predI instanceof SSAMonitorInstruction){
         if (((SSAMonitorInstruction)predI).isMonitorEnter()) {
            if (monitorExitSeen > 0)
               monitorExitSeen--;
            else if (!skip) {
               String lt = getLockType(predI);
               if (lt != null && lt.equals(targetLockType)) {
                  System.out.println("Found a MONITORENTER " + prettyPrint(predI));
                  result.add(predI);
                  return true;
               }
            }
         }
         else monitorExitSeen++;
      }
    
      java.util.Collection<IExplodedBasicBlock> preds =graph.getNormalPredecessors(pred);         
      boolean foundEnclosing = false;           
      for(IExplodedBasicBlock pr: preds) 
         if (explorePredecessor(targetLockType, visited, graph, node, pr, result, false, monitorExitSeen))
            foundEnclosing = true;
 
      if (!foundEnclosing && pred.isEntryBlock()) {
         // FIND THE CALL SITE
         System.out.println("Looking for call sites of node " + node);
         HashSet<SSAInstruction> csites = callSites.get(node);
         if (csites != null) {
            for(SSAInstruction csins: csites) {
               System.out.println("Call site for "  + node.getMethod().getName() + " (Instruction " + prettyPrint((SSAInstruction)csins) + " )");
              if (node.getMethod().isSynchronized() && node.getMethod().getDeclaringClass().getName().toString().indexOf(targetLockType) >= 0) { 
                 result.add(csins);
                 foundEnclosing = true;
              }
              else {
                Triple<Integer, CGNode, IExplodedBasicBlock> ci = instructionContext.get(csins);
                if (explorePredecessor(targetLockType, visited, graph, (CGNode)ci.val2, (IExplodedBasicBlock)ci.val3, result, false, monitorExitSeen))
                   foundEnclosing = true;
              }
            }
         }
        return foundEnclosing;
      } 
      else return foundEnclosing;      
    }  

    static void findClosestSuccessor(SSAInstruction pivot, String targetLockType, ArrayList<SSAInstruction> result) throws Exception {
       Triple<Integer, CGNode, IExplodedBasicBlock> contextInfo = instructionContext.get(pivot);      
       exploreSuccessor(enclosedType, new HashSet<IExplodedBasicBlock>(), (ExplodedControlFlowGraph)icfg.getCFG((CGNode)contextInfo.val2), (CGNode)contextInfo.val2, (IExplodedBasicBlock) contextInfo.val3, result);
    }

    static void exploreSuccessor(String targetLockType, HashSet<IExplodedBasicBlock> visited, ExplodedControlFlowGraph graph, CGNode node, IExplodedBasicBlock  next, ArrayList<SSAInstruction> result) throws Exception {
      if (visited.contains(next))
         return;
      visited.add(next);
      SSAInstruction nextI = next.getInstruction(); 
      if (nextI instanceof SSAMonitorInstruction) {
         if (((SSAMonitorInstruction)nextI).isMonitorEnter()) {
            String lt = getLockType(nextI);
            if (lt != null && lt.equals(targetLockType)) {
               result.add(nextI);
               return;
            }
         }

      }
      else if (nextI instanceof SSAInvokeInstruction) {
    System.out.println("Following a method .."); 
         java.util.Set<CGNode> mnodes = cg.getNodes(((SSAInvokeInstruction)nextI).getCallSite().getDeclaredTarget());  
         for(CGNode n : mnodes) {
       System.out.println("    node = " + n);
            if (n.getMethod().isSynchronized()) {
    System.out.println("synchronized!");
               if (n.getMethod().getDeclaringClass().getName().toString().indexOf(targetLockType) >= 0) {
                  result.add(nextI);
                  return;  
               }
               else {
                  SSAInstruction[] insts = n.getIR().getInstructions();
                  Triple<Integer, CGNode, IExplodedBasicBlock> contextInfo = instructionContext.get(insts[0]); 
                  exploreSuccessor(targetLockType, visited, (ExplodedControlFlowGraph)  icfg.getCFG(n), n,  (IExplodedBasicBlock)contextInfo.val3, result); 
               }
            }   
   }
         return;
      }
      java.util.Collection<IExplodedBasicBlock> succB = graph.getNormalSuccessors(next); 
      for(IExplodedBasicBlock succ : succB) {
             exploreSuccessor(targetLockType, visited, graph, node, succ, result); 
      }  

      
    }

    // Intr--procedural control-flow analysis to find enclosing locks
    static void handle(HashSet<SSAInstruction> visitedInst, ArrayList<SSAInstruction> workList, SSAInstruction current) {        
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
                 for(IExplodedBasicBlock pr: preds) 
         if (explorePredecessors(visited, graph, node, orig, pr, monitorExitSeen))
             foundEnclosing = true;
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
                    int ref = mi.getRef();
                    OrdinalSet<? extends InstanceKey> lockSet = pointerAnalysis.getPointsToSet(heapModel.getPointerKeyForLocal(node, ref));
                       for(InstanceKey ik  : lockSet) {
         if (ik.toString().indexOf(enclosedType) >= 0 || ik.toString().indexOf(enclosingType) >= 0) {
                              lockingInstructions.put(mi, lockSet);
                             break;
                          }
                       }

                    //System.out.println(mi + "(" + prettyPrint(mi) + ") referencing lock v" + ref);
    }        
    }

    // lockType == null means is will be added to lockingInstructions
    private static void saveSyncMethodCall(CGNode node, SSAInvokeInstruction is) {
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
            if (sync) {
                   for(InstanceKey ik  : lockSet) {
           if (ik.toString().indexOf(enclosedType) >= 0 || ik.toString().indexOf(enclosingType) >= 0) {        
         lockingInstructions.put(is, lockSet);
                          break;
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
        if (inst instanceof SSAMonitorInstruction) {
      saveMonitorEnter(node, (SSAMonitorInstruction)inst);
  }
        else if (inst instanceof SSAInvokeInstruction) {
            saveSyncMethodCall(node, (SSAInvokeInstruction)inst);
  }
    }
 



    private static void findReferencePointInMethodOfClassAtLine(String className, String methodName, int lineNo) throws InvalidClassFileException {
        boolean seen = false;
        System.out.println("Searching for instruction " + className + "." + methodName + " at line " + lineNo);
        for(CGNode node: icfg.getCallGraph()) { 
      if (node.getMethod().getDeclaringClass().getName().toString().indexOf(className) >= 0) {    
    //System.out.println("Candidate class=" + node.getMethod().getDeclaringClass().getName().toString());           
                //System.out.println("Is " + node.getMethod().getName().toString() + " what we're looking for?");
                if (node.getMethod().getName().toString().indexOf(methodName) >= 0) {
                    System.out.println("Candidate method=" + node.getMethod().getName().toString());
                    ExplodedControlFlowGraph graph = (ExplodedControlFlowGraph)  icfg.getCFG(node);
                    IR ir = node.getIR();
                    if (ir == null) continue;
                    SSAInstruction[] insts = ir.getInstructions();
                    for(int i=0; i < insts.length; i++) {
                       IBytecodeMethod method = (IBytecodeMethod)ir.getMethod();
                       int bytecodeIndex = method.getBytecodeIndex(i);
                       int sourceLineNum = method.getLineNumber(bytecodeIndex);
                       if (sourceLineNum == lineNo) {
                           referencePoints.add(insts[i]);
                           System.out.println("found reference point = " + insts[i]);
                           seen = true;
                       }
                       else if (seen && sourceLineNum != lineNo)
                           break;
        }  
         }
      }
  }
        // Add other locking instructions with the same lock type

        return ;
    }

    static void addLockingInstructions() {
       for(CGNode node: icfg.getCallGraph()) { 
           if (!isATarget(node)) continue; 
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
                enclosedMethod = sa[2];
                enclosedInstruction = sa[3];
                lineNo = Integer.parseInt(sa[4]);
                enclosedLineNo = sa[4];
                // since substring search is done, adding > ensures we get the right locking instructions 
                enclosingType = sa[5] + ">";
                enclosingTypeTrimmed = sa[5];
                enclosedType = sa[6] + ">";
                enclosedTypeTrimmed = sa[6];
      }
            else throw new Exception("text not recognized at line " + no + " in file "  + targetFile);
  }        
        System.out.println("enclosedClass=" + enclosedClass);
        System.out.println("enclosedMethod=" + enclosedMethod);
        System.out.println("enclosingInstruction=" + enclosingInstruction);   
        System.out.println("enclosedLineNo=" + lineNo);
        System.out.println("enclosedType=" + enclosedType);
        System.out.println("enclosingType=" + enclosingType);   
  findReferencePointInMethodOfClassAtLine(enclosedClass, enclosedMethod, lineNo);        
        bufR.close();
        addLockingInstructions();
    }

    private static void configureAndCreateCallGraph(String scopeFile, String mainClass, String entryClass) throws IOException, ClassHierarchyException, CallGraphBuilderCancelException  {
    File exclusionsFile = null;
    AnalysisScope scope = AnalysisScopeReader.readJavaScope(scopeFile, exclusionsFile, AliasedLockOrder.class.getClassLoader()); 
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