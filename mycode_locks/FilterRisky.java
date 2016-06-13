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

import mycode_locks.CheckPatch.Quad;

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

public class FilterRisky {
  
  static class Double<T1, T2> {
    T1 val1;
    T2 val2;

     public Double(T1 v1, T2 v2) {
         val1 = v1;
         val2 = v2; 
     }  
   }
  
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
    
    static class Quad<T1, T2, T3, T4> {
      T1 val1;
      T2 val2;
      T3 val3;
      T4 val4;

       public Quad(T1 v1, T2 v2, T3 v3, T4 v4) {
           val1 = v1;
           val2 = v2;
           val3 = v3; 
           val4 = v4;
       }      
    }
    
    static class Quint<T1, T2, T3, T4, T5> {
      T1 val1;
      T2 val2;
      T3 val3;
      T4 val4;
      T5 val5;

       public Quint(T1 v1, T2 v2, T3 v3, T4 v4, T5 v5) {
           val1 = v1;
           val2 = v2;
           val3 = v3; 
           val4 = v4;
           val5 = v5;
       }  
    }
       
       static class Hex<T1, T2, T3, T4, T5, T6> {
         T1 val1;
         T2 val2;
         T3 val3;
         T4 val4;
         T5 val5;
         T6 val6;

          public Hex(T1 v1, T2 v2, T3 v3, T4 v4, T5 v5, T6 v6) {
              val1 = v1;
              val2 = v2;
              val3 = v3; 
              val4 = v4;
              val5 = v5;
              val6 = v6;
          }
       }
       
       static class Sev<T1, T2, T3, T4, T5, T6, T7> {
         T1 val1;
         T2 val2;
         T3 val3;
         T4 val4;
         T5 val5;
         T6 val6;
         T7 val7;

          public Sev(T1 v1, T2 v2, T3 v3, T4 v4, T5 v5, T6 v6, T7 v7) {
              val1 = v1;
              val2 = v2;
              val3 = v3; 
              val4 = v4;
              val5 = v5;
              val6 = v6;
              val7 = v7;
          }
       }
       
       static class Eight<T1, T2, T3, T4, T5, T6, T7, T8> {
         T1 val1;
         T2 val2;
         T3 val3;
         T4 val4;
         T5 val5;
         T6 val6;
         T7 val7;
         T8 val8;

          public Eight(T1 v1, T2 v2, T3 v3, T4 v4, T5 v5, T6 v6, T7 v7, T8 v8) {
              val1 = v1;
              val2 = v2;
              val3 = v3; 
              val4 = v4;
              val5 = v5;
              val6 = v6;
              val7 = v7;
              val8 = v8;
          }
       }

    static HashMap<Integer, Double<String,String>> oldVersionLineNumSYNC = new HashMap<Integer, Double<String,String>>();
    static HashMap<Integer, Double<String,String>> newVersionLineNumSYNC = new HashMap<Integer, Double<String,String>>();
    static HashMap<Integer, Double<String,String>> newVersionLineNumMETHODS = new HashMap<Integer, Double<String,String>>();
    static HashMap<Integer, Double<String,String>> newVersionLineNumMETHODSTYPE6 = new HashMap<Integer, Double<String,String>>();
    static HashMap<Integer, Double<String,String>> newVersionLineNumMETHODSTYPE7 = new HashMap<Integer, Double<String,String>>();
    
    static HashMap<Integer, Sev<String,String,String,String,String,String,Integer>> oldLineMethodClass = new HashMap<Integer, Sev<String,String,String,String,String,String,Integer>>();
    static HashMap<Integer, Sev<String,String,String,Integer,String,String,String>> newLineMethodClass = new HashMap<Integer, Sev<String,String,String,Integer,String,String,String>>();
    static HashMap<Integer, Sev<String,String,String,Integer,String,String,String>> newLineMethodClass4Ca = new HashMap<Integer, Sev<String,String,String,Integer,String,String,String>>();
    static HashMap<Integer, Sev<String,String,String,String,String,String,Integer>> newLineMethodClassTYPE4 = new HashMap<Integer, Sev<String,String,String,String,String,String,Integer>>();
    static HashMap<Integer, Sev<String,String,String,Integer,String,String,String>> newLineMethodClassTYPE4C = new HashMap<Integer, Sev<String,String,String,Integer,String,String,String>>();
    static HashMap<Integer, Eight<String,String,String,Integer,String,String,String,String>> newLineMethodClassTYPE4CC = new HashMap<Integer, Eight<String,String,String,Integer,String,String,String,String>>();
    static HashMap<Integer, Sev<String,String,String,Integer,String,String,String>> newLineMethodClassTYPE6mon = new HashMap<Integer, Sev<String,String,String,Integer,String,String,String>>();
    static HashMap<Integer, Eight<String,String,String,Integer,String,String,String,String>> newLineMethodClassTYPE6meth = new HashMap<Integer, Eight<String,String,String,Integer,String,String,String,String>>();
    static HashMap<Integer, Eight<String,String,String,Integer,String,String,String,String>> newLineMethodClassTYPE7 = new HashMap<Integer, Eight<String,String,String,Integer,String,String,String,String>>();
    
    static HashMap<Integer, Double<String, String>> watchlistInfo = new HashMap<Integer, Double<String, String>>();
    
    static ArrayList<String> generated = new ArrayList<String>();
    static ArrayList<String> nodeClasses = new ArrayList<String>();
    
    static String diffFile;
    static String watchList;
    
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
    
    // maps instructions to <cgnode,basicblock>
    static HashMap<SSAInstruction, Triple<Integer, CGNode, IExplodedBasicBlock>> instructionContextOld = new  HashMap<SSAInstruction, Triple<Integer, CGNode, IExplodedBasicBlock>>();
    static HashMap<SSAInstruction, Triple<Integer, CGNode, IExplodedBasicBlock>> instructionContextNew = new  HashMap<SSAInstruction, Triple<Integer, CGNode, IExplodedBasicBlock>>();
    //  CGNode => HashSet<SSAInstruction>
    //static HashMap<CGNode, HashSet<SSAInstruction>> callSites = new HashMap<CGNode, HashSet<SSAInstruction>>();
    static HashMap<CGNode, HashSet<SSAInstruction>> callSitesOld = new HashMap<CGNode, HashSet<SSAInstruction>>();
    static HashMap<CGNode, HashSet<SSAInstruction>> callSitesNew = new HashMap<CGNode, HashSet<SSAInstruction>>();
    static HashMap<CGNode, HashSet<CGNode>> callSitesForInvokeForOld = new HashMap<CGNode, HashSet<CGNode>>();
    static HashMap<CGNode, HashSet<CGNode>> callSitesForInvokeForNew = new HashMap<CGNode, HashSet<CGNode>>();
    
    static ArrayList<IClass> entryClasses = new  ArrayList<IClass>();
    
    static Integer key1 = 0;
    static Integer key2 = 0;
    static Integer key3 = 0;
    static Integer key4 = 0;
    static Integer key5 = 0;
    static Integer key6 = 0;
    static Integer key7 = 0;
    static Integer key8 = 0;
    static Integer key9 = 0;
    
    private static final String FILEPATH = "/home/chelsea/FilterRiskyTargetFiles/target";
    private static final String FILEPATH2 = "/home/chelsea/FilterRiskyTargetFiles/analysis";
    static String fileContent = "";
    static String fc = "";
    
    
    public static void main(String[] args) throws Exception, IOException, ClassHierarchyException, IllegalArgumentException, CallGraphBuilderCancelException, InvalidClassFileException {
      long start = System.currentTimeMillis();
      Properties p = CommandLine.parse(args);
      diffFile = p.getProperty("diffFile");
      watchList = p.getProperty("watchList");
      String scopeFileOldVersion = p.getProperty("scopeFileOldVersion");
      String scopeFileNewVersion = p.getProperty("scopeFileNewVersion");
      entryClass = p.getProperty("entryClass");
      mainClass = p.getProperty("mainClass");
      targetClassNames = p.getProperty("targetClassNames");
      
      if (diffFile == null) {
        throw new Exception("Diff file must be provided!"); 
      }
      if (watchList == null) {
        throw new Exception("Watch list must be provided!"); 
      }
      
      HashMap<Integer, Double<String,String>> diffOld = filterOldVersionSYNC(diffFile);
      HashMap<Integer, Double<String,String>> diffNewMethods = filterNewVersionMETHODS(diffFile);
      HashMap<Integer, Double<String,String>> diffNewSync = filterNewVersionSYNC(diffFile);
      HashMap<Integer, Double<String,String>> diffType6 = filterTYPE6(diffFile);
      HashMap<Integer, Double<String,String>> diffType7 = filterTYPE7(diffFile);
      
      /*for(Map.Entry<Integer, Double<String,String>> entry : diffOld.entrySet()) {
        System.out.println("Filter Old Version Sync: " + entry.getValue().val1);
      }*/
      
      /*for(Map.Entry<Integer, Double<String,String>> entry : diffNewSync.entrySet()) {
        System.out.println("Filter New Version Sync: " + entry.getValue().val1);
      }*/
      
      /*for(Map.Entry<Integer, Double<String,String>> entry : diffNewMethods.entrySet()) {
        System.out.println("Filter New Version Sync Methods: " + entry.getValue().val1);
      }*/
      
      /*for(Map.Entry<Integer, Double<String,String>> entry : diffType7.entrySet()) {
        System.out.println("Filter New Version Type 7: " + entry.getValue().val1 + "  line: " + entry.getKey() + "   " + entry.getValue().val2);
      }*/
      
      //String[] type = parseWatchList(watchList);
      //String T1 = type[0];
      //String T2 = type[1];
      
      readWatchlistInfo(watchList);
      //System.out.println("@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@ WATCH LIST: " + watchlistInfo);
      /*for (Integer i : watchlistInfo.keySet()) {
        Double<String,String> wl = watchlistInfo.get(i);
        System.out.println(wl.val1 + ";" + wl.val2);
      }*/

      pType = p.getProperty("pointerAnalysis"); 
      if (pType == null)
         pType = "zeroOneConCFA";

      if (mainClass != null && entryClass != null) {
        throw new IllegalArgumentException("only specify one of mainClass or entryClass");
      }
      // use exclusions to eliminate certain library packages

      if (targetClassNames == null)
        System.out.println("WARNING: Analysis could be more efficient by specifying a semicolon separated list of target classes (excluding mainClass and entryClass) with -targetClassNames option (use / instead of . in class names)"); 


      System.out.println("Building call graph on old version...");
      configureAndCreateCallGraph(scopeFileOldVersion, mainClass, entryClass); 

      //      CallGraphBuilder builder = Util.makeNCFABuilder(2, options, cache, cha, scope);
      //      CallGraphBuilder builder = Util.makeVanillaNCFABuilder(2, options, cache, cha, scope);

      pointerAnalysis = builder.getPointerAnalysis();
      heapModel = pointerAnalysis.getHeapModel();
      //System.out.println("Exploding the call graph.." + cg.getClass().getName());
                      
      icfg = ExplodedInterproceduralCFG.make(cg);

      for(CGNode node: icfg.getCallGraph()) {
         if (!isATarget(node)) continue;
         ExplodedControlFlowGraph graph = (ExplodedControlFlowGraph) icfg.getCFG(node);
         
         if (graph == null) continue; 
         IR ir = node.getIR();
         
         if (ir == null) continue;
         SSAInstruction[] insts = ir.getInstructions();
         for(int i=0; i < insts.length; i++) {
             SSAInstruction inst = insts[i];
             instructionContextOld.put(inst, new Triple<Integer, CGNode, IExplodedBasicBlock>(i, node, graph.getBlockForInstruction(i)));
             addCallSitesOld(node, inst);
             if (inst instanceof SSAInvokeInstruction) {
               java.util.Set<CGNode> nodes = cg.getNodes(((SSAInvokeInstruction)inst).getDeclaredTarget());
               for(CGNode targetnode : nodes) {
                 addCallSitesForInvokeOld(targetnode, node);                
               }
             }
         }
         
         for(Map.Entry<Integer, Double<String,String>> entry : oldVersionLineNumSYNC.entrySet()) {
           SSAInstruction in = findMonitorInstr(node, entry.getKey(), false);
           if (in != null) {
             //System.out.println("INST!!!!!!!!!!!!!!!!!!!!!! " + in);
             for(Integer i : watchlistInfo.keySet()) {
               Double<String,String> wl = watchlistInfo.get(i);
               String T1 = wl.val1;
               String T2 = wl.val2;
               checkTypeMonitor(in, T1, T2, entry.getKey(), entry.getValue().val2, false);
             }
           }
         }
      }
      
      for(Integer i: oldLineMethodClass.keySet()) {
          Sev<String,String,String,String,String,String,Integer> oMCL = oldLineMethodClass.get(i);
          String methodName = oMCL.val1;
          String className = oMCL.val2;
          String lockType = oMCL.val3;
          String stmt = oMCL.val4;
          String T1 = oMCL.val5;
          String T2 = oMCL.val6;
          Integer lineNum = oMCL.val7;
          //int lineNum = i;
          if (lockType == "type1") {
            generateTargetFile123("onward", className, methodName, lineNum, T2, T1, "1", stmt);
          }
      }
      
      
      // Call graph on new scope file
      System.out.println("Building call graph on new version...");
      configureAndCreateCallGraph(scopeFileNewVersion, mainClass, entryClass);
      
      pointerAnalysis = builder.getPointerAnalysis();
      heapModel = pointerAnalysis.getHeapModel();
      //System.out.println("Exploding the call graph.." + cg.getClass().getName());
                      
      icfg = ExplodedInterproceduralCFG.make(cg);
      ArrayList<SSAInstruction> methodInstr = new ArrayList<SSAInstruction>();
      ArrayList<SSAInstruction> methodInstrT6 = new ArrayList<SSAInstruction>();

      for(CGNode node: icfg.getCallGraph()) {
         if (!isATarget(node)) continue;
         ExplodedControlFlowGraph graph = (ExplodedControlFlowGraph) icfg.getCFG(node);
         
         if (graph == null) continue; 
         IR ir = node.getIR();
         
         if (ir == null) continue;
         SSAInstruction[] insts = ir.getInstructions();
         for(int i=0; i < insts.length; i++) {
             SSAInstruction inst = insts[i];
             instructionContextNew.put(inst, new Triple<Integer, CGNode, IExplodedBasicBlock>(i, node, graph.getBlockForInstruction(i)));
             addCallSitesNew(node, inst);
             if (inst instanceof SSAInvokeInstruction) {
               java.util.Set<CGNode> nodes = cg.getNodes(((SSAInvokeInstruction)inst).getDeclaredTarget());
               for(CGNode targetnode : nodes) {
                 //if (targetnode.toString().indexOf("< Application") >= 0) System.out.println("TARGET: " + targetnode);
                 addCallSitesForInvokeNew(targetnode, node);     
                 //addCallSitesInvokeNew(targetnode, node);
               }
             }
         }
         
         //HashSet<CGNode> n = callSitesForInvokeForNew.get(node);
         //if (n != null && n.toString().indexOf("< Application,") >= 0) System.out.println(n);
         
         for(Map.Entry<Integer, Double<String,String>> entry : newVersionLineNumSYNC.entrySet()) {
           SSAInstruction in = findMonitorInstr(node, entry.getKey(), true);
           if (in != null) {
             //System.out.println("INST!!!!!!!!!!!!!!!!!!!!!! " + prettyPrint(in) + "   " + entry.getKey());
             for(Integer i : watchlistInfo.keySet()) {
               Double<String,String> wl = watchlistInfo.get(i);
               String T1 = wl.val1;
               String T2 = wl.val2;
               checkTypeMonitor(in, T1, T2, entry.getKey(), entry.getValue().val2, true);
             }
           }
         }
         
         for(Map.Entry<Integer, Double<String,String>> entry : newVersionLineNumMETHODS.entrySet()) {
           for(Integer i : watchlistInfo.keySet()) {
             Double<String,String> wl = watchlistInfo.get(i);
             String T1 = wl.val1;
             String T2 = wl.val2;
             //System.out.println("KEY: " + entry.getKey() + "   VALUE: " + entry.getValue());
             checkLineNoAndInstr(node, entry.getValue().val1, entry.getKey(), T1, T2, entry.getValue().val2);
             
             //SSAInstruction instr = findInstr(node, entry.getValue(), entry.getKey());
             SSAInstruction instr = findCallToInstr(node, entry.getValue().val1);
             if (instr != null) {
               //System.out.println("Found instruction new version!!!! " + prettyPrint(instr));
               methodInstr.add(instr);
               int subgraphHeight = 4;
               collectAllReachableInSubGraph(instr, methodInstr, subgraphHeight, T1, T2, entry.getKey(), entry.getValue().val2);
             }
           }
         }
         
         for (Map.Entry<Integer, Double<String,String>> entry : newVersionLineNumMETHODSTYPE6.entrySet()) {
             SSAInstruction instr = findInstr(node, entry.getValue().val1);
             if (instr != null) {
               //System.out.println("Found instruction new version!!!! " + prettyPrint(instr));
               methodInstrT6.add(instr);
               int subgraphHeight = 4;
               //System.out.println(entry.getValue().val2);
               for(Integer i : watchlistInfo.keySet()) {
                 Double<String,String> wl = watchlistInfo.get(i);
                 String T1 = wl.val1;
                 String T2 = wl.val2;
                 collectAllReachableInSubGraphType6(instr, methodInstrT6, subgraphHeight, T1, T2, entry.getValue().val2);
               }
             }
          }
      }
      
      /*for (Integer i : newVersionLineNumMETHODSTYPE7.keySet()) {
        Double<String,String> oMCL = newVersionLineNumMETHODSTYPE7.get(i);
        System.out.println("GOING IN HERE!!!!!!!!!!!!!!!!!!!!!!!!!!!!!");
        System.out.println(oMCL.val1 + "  @@@@@@@@@@@@@@@  " + oMCL.val2);
      }*/
      
      for(CGNode node: icfg.getCallGraph()) {
          if (!isATarget(node)) continue;
          ExplodedControlFlowGraph graph = (ExplodedControlFlowGraph) icfg.getCFG(node);
          
          if (graph == null) continue; 
          for (Map.Entry<Integer, Double<String,String>> entry : newVersionLineNumMETHODSTYPE7.entrySet()) {
            CGNode rNode = findNode(node, entry.getValue().val1);
            for(Integer i : watchlistInfo.keySet()) {
              Double<String,String> wl = watchlistInfo.get(i);
              String T1 = wl.val1;
              String T2 = wl.val2;
              //System.out.println("EXPLORING CALL SITES");
              if (rNode != null) exploreCallSites(rNode, T1, T2, entry.getValue().val2);
            }
         }
      }
      
      for(Integer i: newLineMethodClass.keySet()) {
        Sev<String,String,String,Integer,String,String,String> oMCL = newLineMethodClass.get(i);
        String methodName = oMCL.val1;
        String className = oMCL.val2;
        String lockType = oMCL.val3;
        Integer lineNum = oMCL.val4;
        String stmt = oMCL.val5;
        String T1 = oMCL.val6;
        String T2 = oMCL.val7;
        if (lockType == "type1") {
          generateTargetFile123("pre", className, methodName, lineNum, T2, T1, "3", stmt);
        }
        else if (lockType == "type2") {
          generateTargetFile123("onward", className, methodName, lineNum, T2, T1, "2", stmt);
        }
      }
      
      for(Integer i: newLineMethodClass4Ca.keySet()) {
        Sev<String,String,String,Integer,String,String,String> oMCL = newLineMethodClass4Ca.get(i);
        String methodName = oMCL.val1;
        String className = oMCL.val2;
        String lockType = oMCL.val3;
        Integer lineNum = oMCL.val4;
        String stmt = oMCL.val5;
        String T1 = oMCL.val6;
        String T2 = oMCL.val7;
        if (lockType == "type1") {
          generateTargetFile123("pre", className, methodName, lineNum, T2, T1, "4A (3)", stmt);
        }
        else if (lockType == "type2") {
          generateTargetFile123("onward", className, methodName, lineNum, T2, T1, "4A (2)", stmt);
        }
      }
      
      for(Integer i: newLineMethodClassTYPE6mon.keySet()) {
        Sev<String,String,String,Integer,String,String,String> oMCL = newLineMethodClassTYPE6mon.get(i);
        String methodName = oMCL.val1;
        String className = oMCL.val2;
        String lockType = oMCL.val3;
        Integer lineNum = oMCL.val4;
        String stmt = oMCL.val5;
        String T1 = oMCL.val6;
        String T2 = oMCL.val7;
        if (lockType == "type1") {
          System.out.println("Not of correct lock type! " + lineNum);
        }
        else if (lockType == "type2") {
          //System.out.println("Type 6: Monitor: T2");
          generateTargetFile123("onward", className, methodName, lineNum, T2, T1, "6", stmt);
        }
      }
      
      for(Integer i: newLineMethodClassTYPE6meth.keySet()) {
        Eight<String,String,String,Integer,String,String,String,String> oMCL = newLineMethodClassTYPE6meth.get(i);
        String methodCall = oMCL.val1;
        String className = oMCL.val2;
        String lockType = oMCL.val3;
        Integer lineNum = oMCL.val4;
        String origMethod = oMCL.val5;
        String stmt = oMCL.val6;
        String T1 = oMCL.val7;
        String T2 = oMCL.val8;
        if (lockType == "type1") {
          System.out.println("Not of correct lock type!");
        }
        else if (lockType == "type2") {
          //System.out.println("Type 6: Method: T2");
          generateTargetFileType4("onward", className, methodCall, origMethod, lineNum, T2, T1, "6", stmt);
        }
      }
      
      for(Integer i: newLineMethodClassTYPE7.keySet()) {
        Eight<String,String,String,Integer,String,String,String,String> oMCL = newLineMethodClassTYPE7.get(i);
        String callSitesMethod = oMCL.val1;
        String className = oMCL.val2;
        String lockType = oMCL.val3;
        Integer lineNum = oMCL.val4;
        String origMethod = oMCL.val5;
        String stmt = oMCL.val6;
        String T1 = oMCL.val7;
        String T2 = oMCL.val8;
        if (lockType == "type1") {
          System.out.println("Not of correct lock type!");
        }
        else if (lockType == "type2") {
          generateTargetFileType4("onward", className, callSitesMethod, origMethod, lineNum, T2, T1, "7", stmt);
        }
      }
      
      
      for(Integer i : newLineMethodClassTYPE4.keySet()) {
          Sev<String, String, String, String, String, String, Integer> oMCL = newLineMethodClassTYPE4.get(i);
          String methodCall = oMCL.val1;
          String className = oMCL.val2;
          String lockType = oMCL.val3;
          String stmt = oMCL.val4;
          String T1 = oMCL.val5;
          String T2 = oMCL.val6;
          Integer lineNum = oMCL.val7;
          //int lineNum = i;
          String origMethod = "";
          for(Map.Entry<Integer, Double<String,String>> entry : newVersionLineNumMETHODS.entrySet()) {
            //System.out.println(className + "  " + lineNum);
            //System.out.println(entry.getKey() + "   " + lineNum);
            if (entry.getKey().equals(lineNum)) {
                origMethod = entry.getValue().val1;
                if (lockType == "type1") {
                  generateTargetFileType4("pre", className, methodCall, origMethod, lineNum, T2, T1, "4B", stmt);
                }
                else if (lockType == "type2") {
                  //System.out.println("NEWLINE TYPE 4");
                  generateTargetFileType4("onward", className, methodCall, origMethod, lineNum, T2, T1, "4A", stmt);
                }
            }
          }
      }
      
      for(Integer i : newLineMethodClassTYPE4C.keySet()) {
        Sev<String, String, String, Integer, String, String, String> oMCL = newLineMethodClassTYPE4C.get(i);
        String methodCall = oMCL.val1;
        String className = oMCL.val2;
        String lockType = oMCL.val3;
        Integer lineNum = oMCL.val4;
        String origMethod = "";
        String stmt = oMCL.val5;
        String T1 = oMCL.val6;
        String T2 = oMCL.val7;
        for(Map.Entry<Integer, Double<String,String>> entry : newVersionLineNumMETHODS.entrySet()) {
          //System.out.println(entry.getKey() + "   " + lineNum);
          if (entry.getKey().equals(lineNum)) {
              origMethod = entry.getValue().val1;
              stmt = entry.getValue().val2;
              if (lockType == "type1") {
                generateTargetFileType4("pre", className, methodCall, origMethod, lineNum, T2, T1, "4C (4b)", stmt);
              }
              else if (lockType == "type2") {
                generateTargetFileType4("onward", className, methodCall, origMethod, lineNum, T2, T1, "4C (4a)", stmt);
              }
          }
        }
    }
      
      for(Integer i : newLineMethodClassTYPE4CC.keySet()) {
        Eight<String, String, String, Integer, String, String, String, String> oMCL = newLineMethodClassTYPE4CC.get(i);
        String methodCall = oMCL.val1;
        String className = oMCL.val2;
        String lockType = oMCL.val3;
        Integer lineNum = oMCL.val4;
        String origMethod = oMCL.val5;
        String stmt = oMCL.val6;
        String T1 = oMCL.val7;
        String T2 = oMCL.val8;
        if (lockType == "type1") {
          generateTargetFileType4("pre", className, methodCall, origMethod, lineNum, T2, T1, "4C (4c)", stmt);
        }
        else if (lockType == "type2") {
          //System.out.println(origMethod + "      " + methodCall);
          generateTargetFileType4("onward", className, methodCall, origMethod, lineNum, T2, T1, "4C (4c)", stmt);
        }
      }
      
      //System.out.println(fileContent);
      System.out.println(fc);
      generateFile(fileContent, FILEPATH);
      generateFile(fc, FILEPATH2);
      
      
      long end = System.currentTimeMillis();
      System.out.println("done");
      System.out.println("took " + (end-start) + "ms");
      System.out.println(CallGraphStats.getStats(cg));
    }
    
    public static HashMap<Integer, Double<String,String>> filterOldVersionSYNC(String fname) {
      Integer startNumOldVer = 0;
      String method = "";
      int count = 0;
      String a = "";
      BufferedReader br = null;
         try {
             String currentLine;
             br = new BufferedReader(new FileReader(fname));
             while ((currentLine = br.readLine()) != null) {
                 if (currentLine.indexOf("@@") >= 0) {
                   startNumOldVer = Integer.parseInt(currentLine.substring(currentLine.indexOf("-") + 1, currentLine.indexOf(",")));
                   count = 0;
                 }
                 if (currentLine.startsWith("   ") || currentLine.startsWith(" ")) {
                     count++;
                 }
                 if (currentLine.startsWith("-") || (currentLine.startsWith("!"))) {
                   if (currentLine.contains("synchronized")) {
                     final Pattern patternCond = Pattern.compile("(?!synchronized)\\(([^\\)]+)\\)");
                     final Matcher matcherCond = patternCond.matcher(currentLine);
                     while (matcherCond.find()) {
                       String mc = matcherCond.group().trim();
                       method = mc.substring(1,mc.length()-1);
                       int lineNum = startNumOldVer+count;
                       a = currentLine + " at line " + lineNum;
                       oldVersionLineNumSYNC.put(startNumOldVer+count, new Double<String,String>(method,a));
                     }
                   }
                   count++;
                 }
             }
             //System.out.println(oldVersionLineNumSYNC);
         } catch (IOException e) {
             e.printStackTrace();
         } finally {
             try {
                 if (br != null)br.close();
             } catch (IOException ex) {
                 ex.printStackTrace();
             }
         }
     return oldVersionLineNumSYNC;
    }
    
    public static HashMap<Integer, Double<String,String>> filterNewVersionSYNC(String fname) {
     Integer startNumNewVer = 0;
     String method = "";
     int count = 0;
     String a = "";
     BufferedReader br = null;
        try {
            String currentLine;
            br = new BufferedReader(new FileReader(fname));
            while ((currentLine = br.readLine()) != null) {
                if (currentLine.indexOf("@@") >= 0) {
                    startNumNewVer = Integer.parseInt(currentLine.substring(currentLine.indexOf("+") + 1, currentLine.indexOf(",", currentLine.indexOf(",") + 1)));
                    count = 0;
                }
                if (currentLine.startsWith("   ") || currentLine.startsWith(" ")) {
                    count++;
                }
                if (currentLine.startsWith("+") || (currentLine.startsWith("!"))) {
                  if (currentLine.contains("synchronized")) {
                    final Pattern patternCond = Pattern.compile("(?!synchronized)\\(([^\\)]+)\\)");
                    final Matcher matcherCond = patternCond.matcher(currentLine);
                    while (matcherCond.find()) {
                      String mc = matcherCond.group().trim();
                      method = mc.substring(1,mc.length()-1);
                      int lineNum = startNumNewVer+count;
                      a = currentLine + " at line " + lineNum;
                      newVersionLineNumSYNC.put(startNumNewVer+count, new Double<String,String>(method,a));
                      newVersionLineNumMETHODSTYPE7.put(startNumNewVer+count, new Double<String,String>(method,a));
                    }
                  }
                  count++;
                }
            }
            //System.out.println(newVersionLineNumSYNC);
        } catch (IOException e) {
            e.printStackTrace();
        } finally {
            try {
                if (br != null)br.close();
            } catch (IOException ex) {
                ex.printStackTrace();
            }
        }
    return newVersionLineNumSYNC;
   }
    
    public static HashMap<Integer, Double<String,String>> filterNewVersionMETHODS(String fname) {
      Integer startNumNewVer = 0;
      int count = 0;
      BufferedReader br = null;
      String a = "";
         try {
             String currentLine;
             br = new BufferedReader(new FileReader(fname));
             while ((currentLine = br.readLine()) != null) {
                 if (currentLine.indexOf("@@") >= 0) {
                     startNumNewVer = Integer.parseInt(currentLine.substring(currentLine.indexOf("+") + 1, currentLine.indexOf(",", currentLine.indexOf(",") + 1)));
                     count = 0;
                 }
                 if (currentLine.startsWith("   ") || currentLine.startsWith(" ")) {
                     count++;
                 }
                 if (currentLine.startsWith("+") || (currentLine.startsWith("!"))) {
                   
                   if (currentLine.contains("(")) {
                     final Pattern patternCond = Pattern.compile("([\\s\\n\\r]*[\\w]+)[\\s\\n\\r]*(?=\\(.*\\))");
                     final Matcher matcherCond = patternCond.matcher(currentLine);
                     while (matcherCond.find()) {
                       String mc = matcherCond.group().trim();
                       if ( !(mc.contains("if")) && !(mc.contains("while")) && !(mc.contains("for")) ) {
                         //System.out.println(mc);
                         int lineNum = startNumNewVer+count;
                         a = currentLine + " at line " + lineNum;
                         //System.out.println(a);
                         newVersionLineNumMETHODS.put(startNumNewVer+count, new Double<String,String>(mc,a));
                         //newVersionStatements.put(startNumNewVer+count, currentLine);
                       }
                     }
                   }
                    count++;
                 }
             }
             //System.out.println(newVersionLineNumMETHODS);
         } catch (IOException e) {
             e.printStackTrace();
         } finally {
             try {
                 if (br != null)br.close();
             } catch (IOException ex) {
                 ex.printStackTrace();
             }
         }
     return newVersionLineNumMETHODS;
    }
    
    public static HashMap<Integer, Double<String,String>> filterTYPE6(String fname) {
      Integer startNumNewVer = 0;
      String method = "";
      int count = 0;
      int rc = 0;
      String a = "";
      BufferedReader br = null;
         try {
             String currentLine;
             String trimLine = null;
             String methodLine = "";
             br = new BufferedReader(new FileReader(fname));
             while ((currentLine = br.readLine()) != null) {
                 if (currentLine.indexOf("@@") >= 0) {
                     startNumNewVer = Integer.parseInt(currentLine.substring(currentLine.indexOf("+") + 1, currentLine.indexOf(",", currentLine.indexOf(",") + 1)));
                     count = 0;
                 }
                 if (currentLine.startsWith("   ") || currentLine.startsWith(" ") || currentLine.startsWith("+ ") || currentLine.startsWith("! ")) {
                     count++;
                 }
                 if (currentLine.startsWith("-") && currentLine.contains("synchronized")) {
                   final Pattern patternCond = Pattern.compile("([\\s\\n\\r]*[\\w]+)[\\s\\n\\r].*(?!\\(.*\\))");
                   final Matcher matcherCond = patternCond.matcher(currentLine);
                   while (matcherCond.find()) {
                     String mc = matcherCond.group().trim();
                     if (mc.contains("synchronized")) {
                       trimLine = mc.replace("synchronized", "").trim();
                     }
                     //System.out.println(trimLine);
                   }
                 }
                 if (trimLine != null && currentLine.startsWith("+") && currentLine.contains(trimLine)) {
                   final Pattern patternCond = Pattern.compile("([\\s\\n\\r]*[\\w]+)[\\s\\n\\r].*(?!\\(.*\\))");
                   final Matcher matcherCond = patternCond.matcher(currentLine);
                   while (matcherCond.find()) {
                     String mc = matcherCond.group().trim();
                     methodLine = mc;
                     rc = startNumNewVer + count-1;
                     //System.out.println(methodLine);
                   }
                 }
                 if (trimLine != null && trimLine.equals(methodLine)) {
                   //System.out.println(trimLine);
                   //System.out.println(methodLine);
                   //System.out.println(currentLine);
                   final Pattern pat = Pattern.compile("([\\s\\n\\r]*[\\w]+)[\\s\\n\\r]*(?=\\(.*\\))");
                   final Matcher mat = pat.matcher(methodLine);
                   mat.find();
                   method = mat.group().trim();
                   a = currentLine + " at line " + rc;
                   //System.out.println(a + "    " + method);
                   newVersionLineNumMETHODSTYPE6.put(rc, new Double<String,String>(method,a));
                   break;
                 }
             }
             //System.out.println(newVersionLineNumMETHODSTYPE6);
         } catch (IOException e) {
             e.printStackTrace();
         } finally {
             try {
                 if (br != null)br.close();
             } catch (IOException ex) {
                 ex.printStackTrace();
             }
         }
     return newVersionLineNumMETHODSTYPE6;
    }
    
    public static HashMap<Integer, Double<String,String>> filterTYPE7(String fname) {
      Integer startNumNewVer = 0;
      String method = "";
      int count = 0;
      int rc = 0;
      String a = "";
      BufferedReader br = null;
         try {
             String currentLine;
             ArrayList<String> prevLines = new ArrayList<String>();
             String previousLine = "";
             String trimLine = "";
             String methodLine = "";
             br = new BufferedReader(new FileReader(fname));
             while ((currentLine = br.readLine()) != null) {
                 if (currentLine.indexOf("@@") >= 0) {
                     startNumNewVer = Integer.parseInt(currentLine.substring(currentLine.indexOf("+") + 1, currentLine.indexOf(",", currentLine.indexOf(",") + 1)));
                     count = 0;
                 }
                 if (currentLine.startsWith("   ") || currentLine.startsWith(" ") || currentLine.startsWith("+ ") || currentLine.startsWith("! ")) {
                     //int rc = startNumNewVer + count;
                     //System.out.println(currentLine + "    " + rc);
                     count++;
                 }
                 if (currentLine.startsWith("- ")) {
                   previousLine = currentLine;
                   //rc = startNumNewVer + count;
                   //System.out.println(previousLine + "    :    " + rc);
                   prevLines.add(previousLine);
                   //System.out.println(prevLines.toString());
                 }
                 if (currentLine.startsWith("+ ") && currentLine.contains("synchronized")) {
                   final Pattern pattern = Pattern.compile("([\\s\\n\\r]*[\\w]+)[\\s\\n\\r].*(?!\\(.*\\))");
                   final Matcher matcher = pattern.matcher(currentLine);
                   
                   while (matcher.find()) {
                     String mc = matcher.group().trim();
                     if (mc.contains("synchronized")) {
                       trimLine = mc.replace("synchronized", "").trim();
                       rc = startNumNewVer + count - 1;
                     }
                     //System.out.println("TRIM LINE: " + trimLine);
                   }
                 }
                 for (String s : prevLines) {
                   //System.out.println(s);
                   if (!trimLine.equals("") && s.startsWith("- ") && s.contains(trimLine)) {
                     //System.out.println(s);
                     //System.out.println(trimLine);
                     final Pattern pattern = Pattern.compile("([\\s\\n\\r]*[\\w]+)[\\s\\n\\r].*(?!\\(.*\\))");
                     final Matcher mat = pattern.matcher(s);
                     mat.find();
                     methodLine = mat.group().trim();
                     //System.out.println("METHOD LINE: " + methodLine);
                     //rc = startNumNewVer + count-1;
                   }
                 }
                 if (trimLine.equals(methodLine) && !trimLine.equals("")) {
                   //System.out.println(trimLine);
                   //System.out.println(methodLine);
                   final Pattern pat = Pattern.compile("([\\s\\n\\r]*[\\w]+)[\\s\\n\\r]*(?=\\(.*\\))");
                   final Matcher mat = pat.matcher(methodLine);
                   mat.find();
                   method = mat.group().trim();
                   a = currentLine + " at line " + rc;
                   //System.out.println(a + "    " + method);
                   newVersionLineNumMETHODSTYPE7.put(rc, new Double<String,String>(method,a));
                   break;
                 }
             }
             //System.out.println(newVersionLineNumMETHODSTYPE7);
         } catch (IOException e) {
             e.printStackTrace();
         } finally {
             try {
                 if (br != null)br.close();
             } catch (IOException ex) {
                 ex.printStackTrace();
             }
         }
     return newVersionLineNumMETHODSTYPE7;
    }
    
    public static void generateTargetFile123(String type, String className, String methodName, int lineNum, String T2, String T1, String record) {
      // classname;methodname;lineno;threadClass;callsMethodsOfClass
      String targetType123 = "";
      targetType123 = "refPoint=" + type + ";" + className + ";" + methodName + ";monitorenter;" + lineNum + ";" + T2 + ";" + T1;
      if (!generated.contains(targetType123)) {
        generated.add(targetType123);
        //System.out.println(targetType123 + "    type 1,2,3");
        fileContent = fileContent + targetType123 + "\n";
        fc = fc + targetType123 + " ---- TYPE " + record + "\n";
        //System.out.println(fileContent);
        //generateFile(targetType123, FILEPATH);
      }
    }
    
    public static void generateTargetFile123(String type, String className, String methodName, int lineNum, String T2, String T1, String record, String statement) {
      // classname;methodname;lineno;threadClass;callsMethodsOfClass
      String targetType123 = "";
      targetType123 = "refPoint=" + type + ";" + className + ";" + methodName + ";monitorenter;" + lineNum + ";" + T2 + ";" + T1;
      if (!generated.contains(targetType123)) {
        generated.add(targetType123);
        //System.out.println(targetType123 + "    type 1,2,3");
        fileContent = fileContent + targetType123 + "\n";
        fc = fc + targetType123 + " ---- TYPE " + record + "    " + statement + "\n";
        //System.out.println(fileContent);
        //generateFile(targetType123, FILEPATH);
      }
    }
    
    
    public static void generateTargetFileType4(String type, String className, String methodName, String origMethod, int lineNum, String T2, String T1, String record) {
      // classname;methodname;lineno;threadClass;callsMethodsOfClass
      //refPoint=onward;Lorg/apache/hadoop/dfs/FSNamesystem$SafeModeMonitor;run;leave;3993;Lorg/apache/hadoop/dfs/FSNamesystem$SafeModeInfo;Lorg/apache/hadoop/dfs/FSNamesystem
      String targetType4 = "";
      targetType4 = "refPoint=" + type + ";" + className + ";" + methodName + ";" + origMethod + ";" + lineNum + ";" + T2 + ";" + T1;
      if (!generated.contains(targetType4)) {
        generated.add(targetType4);
        //System.out.println(targetType4 + "      type4");
        fileContent = fileContent + targetType4 + "\n";
        fc = fc + targetType4 + " ---- TYPE " + record + "\n";
        //System.out.println(fileContent);
        //generateFile(targetType4, FILEPATH);
      }
    }
    
    public static void generateTargetFileType4(String type, String className, String methodName, String origMethod, int lineNum, String T2, String T1, String record, String statement) {
      // classname;methodname;lineno;threadClass;callsMethodsOfClass
      //refPoint=onward;Lorg/apache/hadoop/dfs/FSNamesystem$SafeModeMonitor;run;leave;3993;Lorg/apache/hadoop/dfs/FSNamesystem$SafeModeInfo;Lorg/apache/hadoop/dfs/FSNamesystem
      String targetType4 = "";
      targetType4 = "refPoint=" + type + ";" + className + ";" + methodName + ";" + origMethod + ";" + lineNum + ";" + T2 + ";" + T1;
      if (!generated.contains(targetType4)) {
        generated.add(targetType4);
        //System.out.println(targetType4 + "      type4");
        fileContent = fileContent + targetType4 + "\n";
        fc = fc + targetType4 + " ---- TYPE "+ record + "    " + statement + "\n";
        //System.out.println(fileContent);
        //generateFile(targetType4, FILEPATH);
      }
    }
    
    public static void generateFile(String content, String filePath) {
      String fn = "";
      long millis = System.currentTimeMillis();
      fn = "_" + millis;
      
      int randomInt = 0;
      Random randomGenerator = new Random();
      for (int idx = 1; idx <= 10; ++idx) {
        randomInt = randomGenerator.nextInt(100);
      }
      
      PrintWriter writer;
      try {
        writer = new PrintWriter(filePath + randomInt + fn + ".txt", "UTF-8");
        writer.println(content);
        writer.close();
      } catch (FileNotFoundException e1) {
        // TODO Auto-generated catch block
        e1.printStackTrace();
      } catch (UnsupportedEncodingException e1) {
        // TODO Auto-generated catch block
        e1.printStackTrace();
      }
    }
    
    public static String[] parseWatchList(String fname) {
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
    
    private static void addCallSitesOld(CGNode node, SSAInstruction inst) {
      if (inst instanceof SSAInvokeInstruction) {
                java.util.Set<CGNode> mnodes = cg.getNodes(((SSAInvokeInstruction)inst).getCallSite().getDeclaredTarget());
                OrdinalSet<? extends InstanceKey> lockSet = OrdinalSet.<InstanceKey>empty();
                //java.util.Set<CGNode> mnodes = getPossibleNodes(inst); 
                for(CGNode n : mnodes) 
                   addToSetOld(callSitesOld, n, inst);         
      }
    }
    
    private static void addCallSitesNew(CGNode node, SSAInstruction inst) {
      if (inst instanceof SSAInvokeInstruction) {
                java.util.Set<CGNode> mnodes = cg.getNodes(((SSAInvokeInstruction)inst).getCallSite().getDeclaredTarget());
                OrdinalSet<? extends InstanceKey> lockSet = OrdinalSet.<InstanceKey>empty();
                //java.util.Set<CGNode> mnodes = getPossibleNodes(inst); 
                for(CGNode n : mnodes) 
                   addToSetOld(callSitesNew, n, inst);         
      }
    }
    
    private static void addCallSitesForInvokeNew(CGNode targetNode, CGNode node) {
        HashSet<CGNode> callsites = callSitesForInvokeForNew.remove(targetNode);
        if (callsites == null) callsites = new HashSet<CGNode>();
        if (node.toString().indexOf("fakeRootMethod") >= 0)  {
          
        }
        else {
          callsites.add(node);
        }
        //if (targetNode.toString().indexOf("Node: < Application,") >= 0) System.out.println("ADD CALL SITES : " + targetNode + "    " + callsites);
        callSitesForInvokeForNew.put(targetNode, callsites);
    }
    
    private static void addCallSitesForInvokeOld(CGNode targetNode, CGNode node) {
      HashSet<CGNode> callsites = callSitesForInvokeForOld.remove(targetNode);
      if (callsites == null) callsites = new HashSet<CGNode>();
      callsites.add(node);
      callSitesForInvokeForOld.put(targetNode, callsites);
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
    
    public static void checkTypeMonitor(SSAInstruction is, String T1, String T2, int lineNum, String currentLine, boolean isNewVersion) throws InvalidClassFileException {
      String type = "";
      if (is instanceof SSAMonitorInstruction) {
        if (((SSAMonitorInstruction)is).isMonitorEnter()) {
           int ref = ((SSAMonitorInstruction)is).getRef();
           Triple<Integer, CGNode, IExplodedBasicBlock> contextInfo = null;
           if (isNewVersion == false) {
             contextInfo = instructionContextOld.get(is);
           }
           else if (isNewVersion == true) {
             //System.out.println("TRUE!!!" + prettyPrint(is));
             contextInfo = instructionContextNew.get(is);
           }
           int instIndex = contextInfo.val1.intValue();
           CGNode node = contextInfo.val2;
           IBytecodeMethod method = (IBytecodeMethod)node.getIR().getMethod();
           IClass decclass =  method.getDeclaringClass();
           int bytecodeIndex = method.getBytecodeIndex(instIndex);
           int sourceLineNum = method.getLineNumber(bytecodeIndex);
           String cl = decclass.getName().toString();
           String m = method.toString();
           int firstComma = m.indexOf(",");
           int secondComma = m.indexOf(",",firstComma+1);
           String methCall = m.substring(secondComma+2, m.indexOf("("));
           // Assume that the lock is a local variable also includes this
           //System.out.println("LOCKSET NODE: " + node);
           //if (is != null) System.out.println(prettyPrint(is) + "      " + ref);
           OrdinalSet<? extends InstanceKey> lockSet = pointerAnalysis.getPointsToSet(heapModel.getPointerKeyForLocal(node, ref));
           //OrdinalSet<? extends InstanceKey> lockSet = pointerAnalysis.getPointsToSet(heapModel.getPointerKeyForLocal(node, 1));
           if (lockSet.size() == 0) {  // the lock is a field
                     try {
                      IR ir = node.getIR();
                      SSAInstruction[] insts = ir.getInstructions();
                      for(int i=0; i < insts.length; i++) {
                         if (insts[i] != null) {
                             Triple<Integer, CGNode, IExplodedBasicBlock> contextInfo2 = instructionContextNew.get(insts[i]);
                             int bi = method.getBytecodeIndex(contextInfo2.val1);
                             int sl =  method.getLineNumber(bi);

                             if (sourceLineNum == sl) {
                                 //System.out.println("FIELD ACCESS " + prettyPrint(insts[i]));
                                 SSAGetInstruction gis = (SSAGetInstruction) insts[i];
                                 String nameOfLockType = gis.getDeclaredFieldType().toString();
                                 IClass baseLockType = cha.lookupClass(gis.getDeclaredFieldType());
                                 //System.out.println("BASE LOCK TYPE: " + baseLockType + "  " + prettyPrint(gis) + "  " + prettyPrint(is));
                                 if (baseLockType.toString().indexOf("<Application," + T1 + ">") >= 0) {
                                   type = "type1";
                                   break;
                                 }
                                 else if (baseLockType.toString().indexOf("<Application," + T2 + ">") >= 0) {
                                   type = "type2";
                                   break;
                                 }
                            }
                        }
                     }
                  }
                  catch(Exception e) { System.out.println(e);}
             }
             else if (sourceLineNum == lineNum) {
               //System.out.println(lockSet);
               for(InstanceKey ik : lockSet) {
                   //System.out.println(ik + " VS " + ik.getConcreteType());
                   if (ik.toString().indexOf("NEW <Application," + T1 + ">") >= 0) {
                         type = "type1";
                         break;
                   }
                   else if (ik.toString().indexOf("NEW <Application," + T2 + ">") >= 0) {
                         type = "type2";
                         break;
                   }
               }
               if (type == "") {
                 return;
               }
             }
           
           if (isNewVersion == false) {
             key9 = key9 + 1;
             oldLineMethodClass.put(key9, new Sev<String, String, String, String, String, String, Integer>(methCall, cl, type, currentLine, T1, T2, lineNum));
           }
           else if (isNewVersion == true) {
             //System.out.println("Putting in newLineMethodClass: " + methCall + " in class " + cl + " as type " + type + " at line " + lineNum);
             key3 = key3 + 1;
             newLineMethodClass.put(key3, new Sev<String, String, String, Integer, String, String, String>(methCall, cl, type, lineNum, currentLine, T1, T2));
           }
        }
      }
    }
    
    public static SSAInstruction findMonitorInstr(CGNode n, int lineNum, boolean isNewVersion) {
      if (targetClassNames != null && targetClassNames.indexOf(n.getMethod().getDeclaringClass().getName().toString()) < 0) {
        return null;  
      }

      IR ir = n.getIR();
      if (ir == null) {
        return null;
      }
      
      for (Iterator<SSAInstruction> it = ir.iterateAllInstructions(); it.hasNext();) {
        SSAInstruction inst = it.next();
        if (inst instanceof SSAMonitorInstruction) {
            int sourceLineNum = 0;
            Triple<Integer, CGNode, IExplodedBasicBlock> contextInfo = null;
            if (isNewVersion == false) {
              contextInfo = instructionContextOld.get(inst);
            }
            else if (isNewVersion == true) {
              contextInfo = instructionContextNew.get(inst);
            }
            int instIndex = contextInfo.val1.intValue();
            CGNode node = contextInfo.val2;       
            
            try {
              IBytecodeMethod method = (IBytecodeMethod)n.getIR().getMethod();
              IClass decclass =  method.getDeclaringClass();
              int bytecodeIndex = method.getBytecodeIndex(instIndex);
              sourceLineNum = method.getLineNumber(bytecodeIndex);
              
              if (lineNum == sourceLineNum) {
                return inst;
              }
            }
            catch(InvalidClassFileException e) { }
            catch(ClassCastException e) {}
        }       
      }
      //Assertions.UNREACHABLE("failed to find call to " + methodName + " in " + n);
      return null;
    }
    
    public static CGNode findNode(CGNode n, String methodName) {
      CGNode returnNode;
      if (targetClassNames != null && targetClassNames.indexOf(n.getMethod().getDeclaringClass().getName().toString()) < 0) {
        return null;  
      }

      IR ir = n.getIR();
      if (ir == null) {
        return null;
      }
      
      if (n.getMethod().getName().toString().equals(methodName)) {
        returnNode = n;
        //System.out.println(returnNode);
        //System.out.println(returnNode.getMethod().getDeclaringClass().getName());
        return returnNode;
      }
      //Assertions.UNREACHABLE("failed to find call to " + methodName + " in " + n);
      return null;
    }
    
    public static void extractOrigNodeInfo(CGNode n, String methodName) {
      CGNode returnNode;
      if (targetClassNames != null && targetClassNames.indexOf(n.getMethod().getDeclaringClass().getName().toString()) < 0) {
        return;  
      }

      IR ir = n.getIR();
      if (ir == null) {
        return;
      }
      
      String threadClass = "";
      String generalClass = "";
      String mName = "";
      String sp = "";
      if (n.getMethod().getName().toString().equals(methodName)) {
        returnNode = n;
        mName = methodName;
        threadClass = returnNode.getMethod().getDeclaringClass().getName().toString();
        if (threadClass.contains("$")) {
          int sub = threadClass.indexOf("$");
          generalClass = threadClass.substring(0,sub);
        }
        else {
          generalClass = threadClass;
        }
        sp = mName + ":" + threadClass + ":" + generalClass;
        if (!nodeClasses.contains(sp)) {
          //System.out.println("Adding: " + sp);
          nodeClasses.add(sp);
        }
        //System.out.println(returnNode.getMethod().getName());
        //System.out.println(returnNode.getMethod().getDeclaringClass().getName());
        //System.out.println(returnNode.getMethod().getDeclaringClass().getName().getClassName());
        //return returnNode;
      }
      //Assertions.UNREACHABLE("failed to find call to " + methodName + " in " + n);
    }
    
    public static SSAInstruction findInstr(CGNode n, String methodName) {
      /*if (targetClassNames != null && targetClassNames.indexOf(n.getMethod().getDeclaringClass().getName().toString()) < 0) {
        return null;  
      }
      
      IR ir = n.getIR();
      if (ir == null) return null;

      if (n.getMethod().getName().toString().equals(methodName)) {
      //if (n.getMethod().toString().indexOf("Application") >=0) {
        SSAInstruction[] insts = ir.getInstructions();
        for(int i=0; i < insts.length; i++) {
            try {
              IBytecodeMethod method = (IBytecodeMethod)ir.getMethod();
              int bytecodeIndex = method.getBytecodeIndex(i);
              int sourceLineNum = method.getLineNumber(bytecodeIndex);
              //System.out.println(sourceLineNum);
              //if (insts[i] != null) System.out.println(prettyPrint(insts[i]));
              //if (insts[i] != null) System.out.println(sourceLineNum + "   " + lineNum + "    " +  n.toString() + "    " + prettyPrint(insts[i]));
              //if (sourceLineNum == lineNum) {
                  if (insts[i] != null) System.out.println(sourceLineNum + "   " +  n.toString() + "    " + prettyPrint(insts[i]));
                  return insts[i];
              //}
            } catch (InvalidClassFileException e) {
              e.printStackTrace();
            }
            catch(ClassCastException e) {
              System.out.println("Fake class and method");
            }
        }
       }*/
      
      
      
      if (targetClassNames != null && targetClassNames.indexOf(n.getMethod().getDeclaringClass().getName().toString()) < 0) {
        return null;  
      }

      IR ir = n.getIR();
      if (ir == null) {
        return null;
      }
      
      if (n.getMethod().getName().toString().equals(methodName)) {
        for (Iterator<SSAInstruction> it = ir.iterateAllInstructions(); it.hasNext();) {
          SSAInstruction inst = it.next();
          //if (inst instanceof SSAAbstractInvokeInstruction) {
              int sourceLineNum = 0;
              Triple<Integer, CGNode, IExplodedBasicBlock> contextInfo = instructionContextNew.get(inst);
              int instIndex = contextInfo.val1.intValue();

              try {
                IBytecodeMethod method = (IBytecodeMethod)n.getIR().getMethod();
                IClass decclass =  method.getDeclaringClass();
                int bytecodeIndex = method.getBytecodeIndex(instIndex);
                sourceLineNum = method.getLineNumber(bytecodeIndex);
                //System.out.println("FINDINSTR: " + prettyPrint(inst));
                return inst;
              }
              catch(InvalidClassFileException e) { }
              catch(ClassCastException e) {}
          //}       
        }
      }
      //Assertions.UNREACHABLE("failed to find call to " + methodName + " in " + n);
      return null;
    }
    
    public static SSAInstruction findCallToInstr(CGNode n, String methodName) {
       if (targetClassNames != null && targetClassNames.indexOf(n.getMethod().getDeclaringClass().getName().toString()) < 0) {
         return null;  
       }

       IR ir = n.getIR();
       if (ir == null) {
         return null;
       }
       for (Iterator<SSAInstruction> it = ir.iterateAllInstructions(); it.hasNext();) {
           SSAInstruction s = it.next();
           if (s instanceof SSAAbstractInvokeInstruction) {
             SSAAbstractInvokeInstruction call = (SSAAbstractInvokeInstruction) s;
             //if (n.getMethod().toString().indexOf("Lorg/apache/hadoop/mapred/TaskTracker") >= 0) System.out.println("CALL TO INSTR: " + prettyPrint(s));
             if (call.getCallSite().getDeclaredTarget().getName().toString().equals(methodName)) {
               //System.out.println("FIND NODE: " + n);
               //System.out.println("CALL TO INSTR: " + prettyPrint(s));
               return s;
             }
           }
       }
       //Assertions.UNREACHABLE("failed to find call to " + methodName + " in " + n);
       return null;
     }

    private static void checkLineNoAndInstr(CGNode n, String methodName, int lineNum, String T1, String T2, String currentLine) {
      String type = "";
      if (targetClassNames != null && targetClassNames.indexOf(n.getMethod().getDeclaringClass().getName().toString()) < 0) {
        return;  
      }

      IR ir = n.getIR();
      if (ir == null) {
        return;
      }
      
      for (Iterator<SSAInstruction> it = ir.iterateAllInstructions(); it.hasNext();) {
          SSAInstruction inst = it.next();
          if (inst instanceof SSAAbstractInvokeInstruction) {
            SSAAbstractInvokeInstruction call = (SSAAbstractInvokeInstruction) inst;
            //System.out.println("Checking: " + methodName + "     " + call.getDeclaredTarget().getName().toString());
            if (call.getDeclaredTarget().getName().toString().equals(methodName)) {
              int sourceLineNum = 0;
              Triple<Integer, CGNode, IExplodedBasicBlock> contextInfo = instructionContextNew.get(inst);
              int instIndex = contextInfo.val1.intValue();
              CGNode node = contextInfo.val2; 
              
              String instSt = inst.toString();
              int pos = instSt.indexOf("(");
              if (pos >= 0)
                 instSt = instSt.substring(0,pos); 

              String result = "";
              
              try {
                IBytecodeMethod method = (IBytecodeMethod)node.getIR().getMethod();
                IClass decclass =  method.getDeclaringClass();
                int bytecodeIndex = method.getBytecodeIndex(instIndex);
                sourceLineNum = method.getLineNumber(bytecodeIndex);   
                result = "line " + sourceLineNum + " in " + (decclass.getSourceFileName() == null ? decclass.getName() : decclass.getSourceFileName());
                //System.out.println(result);
                String cl = decclass.getName().toString();
                //System.out.println("Checking: " + methodName);
                /*if (methodName.indexOf("fail") >= 0) {
                  System.out.println("Checking: " + methodName);
                }*/
                if (sourceLineNum == lineNum) {
                  /*System.out.println("INST: " + inst);
                  System.out.println("CALL: " + call.getDeclaredTarget().getName().toString());
                  System.out.println("METHOD NAME: " + methodName);
                  System.out.println("NODE!!!!!!!!!!!!!!!!!!!!!!!!! " + node);*/
                  
                  java.util.Set<CGNode> setCG = cg.getNodes(call.getDeclaredTarget());
                  for (CGNode no : setCG) {
                    String m = method.toString();
                    int firstComma = m.indexOf(",");
                    int secondComma = m.indexOf(",",firstComma+1);
                    String methCall = m.substring(secondComma+2, m.indexOf("("));
                    // CHECK HERE - CAM
                    if (no.getMethod().isSynchronized()) {
                        OrdinalSet<? extends InstanceKey> lockSet = pointerAnalysis.getPointsToSet(heapModel.getPointerKeyForLocal(no, 1));
                        //System.out.println("LOCKSET SYNC: " + lockSet);
                        for(InstanceKey ik : lockSet) {
                            if (ik.toString().indexOf("NEW <Application," + T1 + ">") >= 0) {
                                  //System.out.println(no.getMethod() + "  is  " + T1);
                                  type = "type1";
                                  break;
                            }
                            else if (ik.toString().indexOf("NEW <Application," + T2 + ">") >= 0) {
                                  //System.out.println(no.getMethod() + "  is  " + T2);
                                  type = "type2";
                                  break;
                            }
                        }
                        
                        if (type == "") {
                          return;
                        }
                        key8 = key8 + 1;
                        newLineMethodClassTYPE4.put(key8, new Sev<String, String, String, String, String, String, Integer>(methCall, cl, type, currentLine, T1, T2, lineNum));
                    }
                  }
                  
                }
              }
              catch(InvalidClassFileException e) {
                 System.out.println(e);
              }
              catch(ClassCastException e) {
                result = "Fake class and method";
              }
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
    
    private static void exploreSuccessors(ArrayList<SSAInstruction> list, CGNode node, int depth, String T1, String T2, int lineNum, String currentLine) {
      try {
      String type = "";
      IR ir = node.getIR();
      SSAInstruction[] insts = ir.getInstructions();
      for(int i = 0; i < insts.length; i++) {
        if (i == insts.length - 1) 
          list.add(insts[i]);
        if (depth > 0) {
          // If synch(o)
          if (insts[i] instanceof SSAMonitorInstruction) {
            SSAInstruction in = insts[i];
            if (in != null && (((SSAMonitorInstruction)in).isMonitorEnter()) ) {
              int ref = ((SSAMonitorInstruction)in).getRef();
              IBytecodeMethod method = (IBytecodeMethod)node.getIR().getMethod();
              IClass decclass =  method.getDeclaringClass();
              int bytecodeIndex = method.getBytecodeIndex(i);
              int sourceLineNum = method.getLineNumber(bytecodeIndex);
              if (sourceLineNum == lineNum) {
                String cl = decclass.getName().toString();
                String m = method.toString();
                int firstComma = m.indexOf(",");
                int secondComma = m.indexOf(",",firstComma+1);
                String methCall = m.substring(secondComma+2, m.indexOf("("));

                // Assume that the lock is a local variable also includes this
                OrdinalSet<? extends InstanceKey> lockSet = pointerAnalysis.getPointsToSet(heapModel.getPointerKeyForLocal(node, ref));
                for(InstanceKey ik : lockSet) {
                    if (ik.toString().indexOf("NEW <Application," + T1 + ">") >= 0) {
                          type = "type1";
                          break;
                    }
                    else if (ik.toString().indexOf("NEW <Application," + T2 + ">") >= 0) {
                          type = "type2";
                          break;
                    }
                 }
                if (type == "") {
                  return;
                }

                System.out.println("Adding: " + methCall + " Source Line Num: " + sourceLineNum);
                key2 = key2 + 1;
                newLineMethodClass4Ca.put(key2, new Sev<String, String, String, Integer, String, String, String>(methCall, cl, type, sourceLineNum, currentLine, T1, T2));
              }
            }
          }
          // If method is sync
          else if (insts[i] instanceof SSAInvokeInstruction && isInDesiredClass((SSAInvokeInstruction)insts[i])) {
               MethodReference mr = ((SSAInvokeInstruction)insts[i]).getDeclaredTarget();
               java.util.Set<CGNode> nodes = cg.getNodes(mr);
               for(CGNode succ : nodes) {
                 if (succ.toString().indexOf("Application") >= 0 /*&& succ.toString().indexOf("<init>") < 0*/) {   
                       //System.out.println("SUCC: " + succ);
                       IBytecodeMethod origMethod = (IBytecodeMethod)node.getIR().getMethod();
                       String OM = origMethod.toString();
                       int firstCom = OM.indexOf(",");
                       int secondCom = OM.indexOf(",",firstCom+1);
                       String methCall = OM.substring(secondCom+2, OM.indexOf("("));
                       int bytecodeIndexORIG = origMethod.getBytecodeIndex(i);
                       int sourceLineNumORIG = origMethod.getLineNumber(bytecodeIndexORIG);
                       //System.out.println("ORIG METHOD: " + ORIGmeth);
                       
                       IBytecodeMethod method = (IBytecodeMethod)succ.getIR().getMethod();
                       IClass decclass =  method.getDeclaringClass();
                       IR succIR = succ.getIR();
                       SSAInstruction[] instsSUCC = succIR.getInstructions();
                       for(int j=0; j < instsSUCC.length; j++) {
                           int bytecodeIndex = method.getBytecodeIndex(j);
                           int sourceLineNum = method.getLineNumber(bytecodeIndex);
                           String cl = decclass.getName().toString();
                           String m = method.toString();
                           int firstComma = m.indexOf(",");
                           int secondComma = m.indexOf(",",firstComma+1);
                           String ORIGmeth = m.substring(secondComma+2, m.indexOf("("));
                           //System.out.println("METHOD CALL: " + methCall);
                           if (sourceLineNum == lineNum) {
                             //System.out.println("METH CALL : " + methCall);
                             //System.out.println("CLASS: " + decclass.getName().toString());
                             if (succ.getMethod().isSynchronized()) {
                               OrdinalSet<? extends InstanceKey> lockSet = pointerAnalysis.getPointsToSet(heapModel.getPointerKeyForLocal(succ, 1));
                               //System.out.println("LOCKSET SYNC: " + lockSet);
                               for(InstanceKey ik : lockSet) {
                                   if (ik.toString().indexOf("NEW <Application," + T1 + ">") >= 0) {
                                         type = "type1";
                                         break;
                                   }
                                   else if (ik.toString().indexOf("NEW <Application," + T2 + ">") >= 0) {
                                         type = "type2";
                                         break;
                                   }
                               }
                               if (type == "") {
                                 return;
                               }
                               key1 = key1 + 1;
                               newLineMethodClassTYPE4C.put(key1, new Sev<String, String, String, Integer, String, String, String>(methCall, cl, type, lineNum, currentLine, T1, T2));
                             }
                           }
                           // else if m is not synch:
                           // in method body of m!
                           // m3;  m  ; L3
                           else if (!(succ.getMethod().isSynchronized()) && (succ.getMethod().toString().indexOf("<init>") < 0) && (succ.getMethod().toString().indexOf("access$") < 0)
                               && (node.getMethod().toString().indexOf("<init>") < 0) && (node.getMethod().toString().indexOf("access$") < 0)
                               ) {
                             //System.out.println(succ.getMethod().toString() + " NOT SYNC " + prettyPrint(insts[i]));
                             OrdinalSet<? extends InstanceKey> lockSet = pointerAnalysis.getPointsToSet(heapModel.getPointerKeyForLocal(succ, 1));
                             //System.out.println("LOCKSET SYNC: " + lockSet);
                             for(InstanceKey ik : lockSet) {
                                 if (ik.toString().indexOf("NEW <Application," + T1 + ">") >= 0) {
                                       type = "type1";
                                       break;
                                 }
                                 else if (ik.toString().indexOf("NEW <Application," + T2 + ">") >= 0) {
                                       type = "type2";
                                       break;
                                 }
                             }
                             if (type == "") {
                               return;
                             }
                             //System.out.println("ADDING TYPE 4CC: " + methCall + " from " + ORIGmeth + " " + prettyPrint(insts[i]) + "  type: " + type + "  line " + sourceLineNumORIG);
                             key4 = key4 + 1;
                             newLineMethodClassTYPE4CC.put(key4, new Eight<String, String, String, Integer, String, String, String, String>(methCall, cl, type, sourceLineNumORIG, ORIGmeth, currentLine, T1, T2));
                           }
                        }
                       }
                       // Method is not sync, so explore succ
                       else if (!(succ.getMethod().isSynchronized())) {
                         exploreSuccessors(list, succ, depth--, T1, T2, lineNum, currentLine);
                       }
               }
          }
        }
      }
      }
      catch(InvalidClassFileException e) {
        System.out.println(e);
     }
     catch(ClassCastException e) {
        //System.out.println(e);
       String result = "Fake class";
     }
    }
    
    private static void exploreSuccessorsTYPE6(ArrayList<SSAInstruction> list, CGNode node, int depth, String T1, String T2, String currentLine) throws InvalidClassFileException {
      String type = "";
      IR ir = node.getIR();
      SSAInstruction[] insts = ir.getInstructions();
      for(int i = 0; i < insts.length; i++) {
        if (i == insts.length - 1) 
          list.add(insts[i]);
        if (depth > 0) {
          // If synch(o)
          if (insts[i] instanceof SSAMonitorInstruction) {
            SSAInstruction in = insts[i];
            if (in != null && (((SSAMonitorInstruction)in).isMonitorEnter()) ) {
              //System.out.println("MONITOR INST-----------------------------------: " + prettyPrint(in));
              int ref = ((SSAMonitorInstruction)in).getRef();
              IBytecodeMethod method = (IBytecodeMethod)node.getIR().getMethod();
              IClass decclass =  method.getDeclaringClass();
              int bytecodeIndex = method.getBytecodeIndex(i);
              int sourceLineNum = method.getLineNumber(bytecodeIndex);
              String cl = decclass.getName().toString();
              String m = method.toString();
              int firstComma = m.indexOf(",");
              int secondComma = m.indexOf(",",firstComma+1);
              String methCall = m.substring(secondComma+2, m.indexOf("("));

              // Assume that the lock is a local variable also includes this
              OrdinalSet<? extends InstanceKey> lockSet = pointerAnalysis.getPointsToSet(heapModel.getPointerKeyForLocal(node, ref));
              //System.out.println(lockSet);
              for(InstanceKey ik : lockSet) {
                  //System.out.println(ik.toString());
                  if (ik.toString().indexOf("NEW <Application," + T1 + ">") >= 0) {
                        type = "type1";
                        return;
                        //System.out.println("MONITOR INST-----------------------------------: " + prettyPrint(in) + "   TYPE 1  " + ik.toString());
                  }
                  else if (ik.toString().indexOf("NEW <Application," + T2 + ">") >= 0) {
                        type = "type2";
                        //System.out.println("MONITOR INST-----------------------------------: " + prettyPrint(in) + "   TYPE 2  " + ik.toString());
                        key5 = key5 + 1;
                        newLineMethodClassTYPE6mon.put(key5, new Sev<String, String, String, Integer, String, String, String>(methCall, cl, type, sourceLineNum, currentLine, T1, T2));
                        break;
                  }
              }
              if (type == "") {
                return;
              }
            }
          }
          // If method is sync
          else if (insts[i] instanceof SSAInvokeInstruction && isInDesiredClass((SSAInvokeInstruction)insts[i])) {
              OrdinalSet<? extends InstanceKey> lockSet = pointerAnalysis.getPointsToSet(heapModel.getPointerKeyForLocal(node, 1));
              //System.out.println("LOCKSET SYNC: " + lockSet);
              for(InstanceKey ik : lockSet) {
                  if (ik.toString().indexOf("NEW <Application," + T1 + ">") >= 0) {
                        type = "type1";
                        IBytecodeMethod origMethod = (IBytecodeMethod)node.getIR().getMethod();
                        String OM = origMethod.toString();
                        int firstCom = OM.indexOf(",");
                        int secondCom = OM.indexOf(",",firstCom+1);
                        String ORIGmeth = OM.substring(secondCom+2, OM.indexOf("("));
                        int bytecodeIndexORIG = origMethod.getBytecodeIndex(i);
                        int sourceLineNumORIG = origMethod.getLineNumber(bytecodeIndexORIG);
                        //System.out.println("ORIG METHOD: " + ORIGmeth);
                     
                        MethodReference mr = ((SSAInvokeInstruction)insts[i]).getDeclaredTarget();
                        java.util.Set<CGNode> nodes = cg.getNodes(mr);
                        for(CGNode succ : nodes) {
                          if (succ.toString().indexOf("Application") >= 0) {   
                                //System.out.println("SUCC: " + succ);
                                IBytecodeMethod method = (IBytecodeMethod)succ.getIR().getMethod();
                                IClass decclass =  method.getDeclaringClass();
                                IR succIR = succ.getIR();
                                SSAInstruction[] instsSUCC = succIR.getInstructions();
                                for(int j=0; j < instsSUCC.length; j++) {
                                    int bytecodeIndex = method.getBytecodeIndex(j);
                                    int sourceLineNum = method.getLineNumber(bytecodeIndex);
                                    String cl = decclass.getName().toString();
                                    String m = method.toString();
                                    int firstComma = m.indexOf(",");
                                    int secondComma = m.indexOf(",",firstComma+1);
                                    String methCall = m.substring(secondComma+2, m.indexOf("("));
                                    //System.out.println(succ.getMethod().toString());
                                    if (succ.getMethod().isSynchronized()) {
                                      OrdinalSet<? extends InstanceKey> lockSet2 = pointerAnalysis.getPointsToSet(heapModel.getPointerKeyForLocal(succ, 1));
                                      //System.out.println("LOCKSET SYNC: " + lockSet);
                                      for(InstanceKey ik2 : lockSet2) {
                                          if (ik2.toString().indexOf("NEW <Application," + T1 + ">") >= 0) {
                                                type = "type1";
                                                return;
                                          }
                                          else if (ik2.toString().indexOf("NEW <Application," + T2 + ">") >= 0) {
                                                type = "type2";
                                                key6 = key6 + 1;
                                                //System.out.println("Adding " + methCall + " from " + ORIGmeth + " at " + sourceLineNumORIG);
                                                //System.out.println(currentLine + "  " + methCall + "   " + ORIGmeth);
                                                newLineMethodClassTYPE6meth.put(key6, new Eight<String, String, String, Integer, String, String, String, String>(methCall, cl, type, sourceLineNumORIG, ORIGmeth, currentLine, T1, T2));
                                                break;
                                          }
                                      }
                                      if (type == "") {
                                        return;
                                      }
                                    }
                                 }
                                }
                                // Method is not sync, so explore succ
                                else if (!(succ.getMethod().isSynchronized())) {
                                  exploreSuccessorsTYPE6(list, succ, depth--, T1, T2, currentLine);
                                }
                        }
                  }
                  else if (ik.toString().indexOf("NEW <Application," + T2 + ">") >= 0) {
                        type = "type2";
                        return;
                  }
              }
          }
        }
      }
    }
    
    private static void exploreCallSites(CGNode node, String T1, String T2, String currentLine) {
      String type = "";
      //System.out.println("EXPLORE CALL SITES : " + node);
      OrdinalSet<? extends InstanceKey> lockSet = pointerAnalysis.getPointsToSet(heapModel.getPointerKeyForLocal(node, 1));
      //System.out.println(lockSet);
      for(InstanceKey ik : lockSet) {
        if (ik.toString().indexOf("NEW <Application," + T1 + ">") >= 0) {
              type = "type1";
              return;
        }
        else if (ik.toString().indexOf("NEW <Application," + T2 + ">") >= 0) {
              type = "type2";
              break;
        }
      }
      if (type == "") {
        return;
      }
      //if (callSitesForInvokeForNew.entrySet().toString().indexOf("Node: < Application,") >= 0) System.out.println(callSitesForInvokeForNew.entrySet().toString());
      //System.out.println("KEY/VALUE " + callSitesForInvokeForNew.get(node));
      HashSet<CGNode> mnodes = callSitesForInvokeForNew.get(node);
      //System.out.println("MNODES: " + mnodes);
      String ORIGmeth = "";
      try{
      for (CGNode n : mnodes) {
        //System.out.println("NODE SITES: " + n.getMethod().toString());
        IR ir = n.getIR();
        if (n.getMethod().toString().indexOf("FakeRootMethod") >= 0 ) continue;
        if (ir.getMethod().getClass().toString().indexOf("FakeRootMethod") >= 0) continue;
        SSAInstruction[] insts = ir.getInstructions();
        for(int i = 0; i < insts.length; i++) {
          if (insts[i] instanceof SSAInvokeInstruction) {
            String mName = ((SSAInvokeInstruction)insts[i]).getDeclaredTarget().toString();
            //if (n.getMethod().toString().indexOf("Application") >= 0) System.out.println("METHOD NAME: " + mName + "  CGNODE: " + n.getMethod().toString());
            int firstCom = mName.indexOf(",");
            int secondCom = mName.indexOf(",",firstCom+1);
            ORIGmeth = mName.substring(secondCom+2, mName.indexOf("("));
            //System.out.println("ORIGmeth " + ORIGmeth);
            //if (mName.equals(n.getMethod().toString())) {
              //System.out.println("ENTERED!!!!");
              //System.out.println(ir.getMethod().getClass().toString());
              IBytecodeMethod cmethod = (IBytecodeMethod)ir.getMethod();
              IClass decclass = cmethod.getDeclaringClass();
              String cl = decclass.getName().toString();
              String m = cmethod.toString();
              int bytecodeIndex = cmethod.getBytecodeIndex(i);
              int sourceLineNum = cmethod.getLineNumber(bytecodeIndex);
              int firstComma = m.indexOf(",");
              int secondComma = m.indexOf(",",firstComma+1);
              String callSiteMethod = m.substring(secondComma+2, m.indexOf("("));
              //System.out.println("CALL SITE METHOD: " + callSiteMethod + "   SOURCE LINE NUM: " + sourceLineNum);
              //System.out.println("ORIGmeth " + ORIGmeth + "   " + sourceLineNum);
              key7 = key7 + 1;
              newLineMethodClassTYPE7.put(key7, new Eight<String, String, String, Integer, String, String, String, String>(callSiteMethod, cl, type, sourceLineNum, ORIGmeth, currentLine, T1, T2));
            //}
          }
        }
      }
      }
      catch(InvalidClassFileException e) { }
      catch(ClassCastException e) {}
    }
    
    private static void collectAllReachableInSubGraph(SSAInstruction inst,  ArrayList<SSAInstruction> list, int depth, String T1, String T2, int lineNum, String currentLine) throws InvalidClassFileException {
      Triple<Integer, CGNode, IExplodedBasicBlock> contextInfo = instructionContextNew.get(inst);
      CGNode node = contextInfo.val2;
      exploreSuccessors(list, node, depth, T1, T2, lineNum, currentLine);
    }
    
    private static void collectAllReachableInSubGraphType6(SSAInstruction inst,  ArrayList<SSAInstruction> list, int depth, String T1, String T2, String currentLine) throws InvalidClassFileException {
      Triple<Integer, CGNode, IExplodedBasicBlock> contextInfo = instructionContextNew.get(inst);
      CGNode node = contextInfo.val2;
      exploreSuccessorsTYPE6(list, node, depth, T1, T2, currentLine);
    }
    
    private static String prettyPrint(SSAInstruction inst) {
      //if (inst instanceof SSAInvokeInstruction)
      //  return inst.toString();
      Triple<Integer, CGNode, IExplodedBasicBlock> contextInfo = instructionContextNew.get(inst);
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
    
    static void readWatchlistInfo(String watchlistFile) throws Exception, IOException{
      BufferedReader bufR = new BufferedReader(new FileReader(watchlistFile));
      String line;
      Integer counterKey = 0;
      while ((line = bufR.readLine()) != null) {
         String[] sa = line.split(";");
         counterKey++;
         watchlistInfo.put(counterKey, new Double<String,String>(sa[0], sa[1]));
      }
      bufR.close();
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
        AnalysisScope scope = AnalysisScopeReader.readJavaScope(scopeFile, exclusionsFile, FilterRisky.class.getClassLoader()); 
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