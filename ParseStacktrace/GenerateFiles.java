package mycode_locks;

import java.io.*;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Properties;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

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
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.ssa.SSAInvokeInstruction;
import com.ibm.wala.ssa.SSAAbstractInvokeInstruction;
import com.ibm.wala.ssa.SSAMonitorInstruction;
import com.ibm.wala.ssa.analysis.ExplodedControlFlowGraph;
import com.ibm.wala.ssa.analysis.IExplodedBasicBlock;
import com.ibm.wala.types.ClassLoaderReference;
import com.ibm.wala.types.TypeReference;
import com.ibm.wala.util.config.AnalysisScopeReader;
import com.ibm.wala.util.debug.Assertions;
import com.ibm.wala.util.intset.OrdinalSet;
import com.ibm.wala.util.io.CommandLine;
import com.ibm.wala.util.strings.StringStuff;
import com.ibm.wala.util.warnings.Warnings;

/**
 *
 * @author chelseametcalf
 */
public class GenerateFiles {
  
   static class Pair<T1, T2> {
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
    
    static class Quad {
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
    }
    
    static ArrayList<String> entryClassList = new ArrayList<String>();
    static int targetNumber = 0;
    static String projectName = "";
    static String versionNumber = "";
    static String folderPath = "";
    static String stackTraceFileName = "";
    static String pType = "";
    static ArrayList<IClass> entryClasses = new  ArrayList<IClass>();
    static String entryClass;
    static CallGraphBuilder builder;
    static IClassHierarchy cha;
    static CallGraph cg;
    static ExplodedInterproceduralCFG icfg;
    static PointerAnalysis pointerAnalysis; 
    static HeapModel heapModel;
    
    // maps instructions to <cgnode,basicblock>
    static HashMap<SSAInstruction, Triple<Integer, CGNode, IExplodedBasicBlock>> instructionContext = new  HashMap<SSAInstruction, Triple<Integer, CGNode, IExplodedBasicBlock>>();
    static Class ssaInvokeInstructionClass = null;
    static HashMap<IClass, HashSet<Quad>> reflectionInfo = new HashMap<IClass, HashSet<Quad>>();
    static HashMap<CGNode, HashSet<SSAInstruction>> callSites = new HashMap<CGNode, HashSet<SSAInstruction>>();
    static HashMap<IClass, HashMap<IClass, HashSet<Pair<CGNode, IExplodedBasicBlock>>>> calledViaReflection = new HashMap<IClass,  HashMap<IClass, HashSet<Pair<CGNode, IExplodedBasicBlock>>>>();
    static boolean foundMethodNodeThatCallsMethod = false;
    static boolean foundEnclosingMethodNode = false;
    static ArrayList<String> waitingToLockList = new ArrayList<String>();
    
    public static void main(String[] args) throws Exception {
      
        Properties p = CommandLine.parse(args);
        projectName = p.getProperty("projectName");
        versionNumber = p.getProperty("versionNumber");
        
        if (projectName == null)
          throw new Exception("Project name must be provided!");
        
        if (versionNumber == null)
          throw new Exception("Version number must be provided!");
        
        //folderPath = "/home/chelsea/Dropbox/Documents/Research/GenerateLockTypes/" + projectName + "/";
        folderPath = "/Users/chelseametcalf/Dropbox/Documents/Research/AliasedLockOrder/" + projectName + "/";
        stackTraceFileName = folderPath + "stacktrace.txt";
        
        pType = p.getProperty("pointerAnalysis"); 
        if (pType == null)
           pType = "zeroOneConCFA";
        
        /*if (args.length != 2) {
            System.err.println("Usage: java GenerateFiles <project name> <version number>");
            System.exit(1);
        }
        
        String projectName = args[0];
        String versionNumber = args[1];*/

        generateScopeFileLinux(projectName, versionNumber);
        //String scopeFile = getScopeFile(projectName, versionNumber);
        // change back to scope.txt when on linux computer
        String scopeFile = folderPath + "scope-mac.txt";
        System.out.println("SCOPE FILE: " + scopeFile);
        
        getEntryClasses(stackTraceFileName);
        
        // if using Java 8
        //String entryClassString = String.join(";", entryClassList);
        System.out.println(entryClassList);
        String entryClassString = "";
        for (int i = 0; i < entryClassList.size(); i++) {
          if (i != entryClassList.size() - 1) {
            entryClassString = entryClassString + entryClassList.get(i) + ";";
          }
          else {
            entryClassString = entryClassString + entryClassList.get(i);
          }
        }
        entryClass = entryClassString;
        System.out.println(entryClass);
        
        generateRunFileLinux(projectName, entryClassString);

        System.out.println("Building call graph...");
        configureAndCreateCallGraph(scopeFile, "", entryClass); 

        pointerAnalysis = builder.getPointerAnalysis();
        heapModel = pointerAnalysis.getHeapModel();
        //System.out.println("Exploding the call graph.." + cg.getClass().getName());
                            
        icfg = ExplodedInterproceduralCFG.make(cg);
        
        for(CGNode node: icfg.getCallGraph()) {
           //if (!isATarget(node)) continue;
           ExplodedControlFlowGraph graph = (ExplodedControlFlowGraph) icfg.getCFG(node);

           IR ir = node.getIR();
           if (ir == null || !(node.toString().indexOf("Application") >= 0)) continue;
           SSAInstruction[] allInst = ir.getInstructions();

           if (graph == null) continue;

            java.util.Iterator<IExplodedBasicBlock> bbIt = graph.iterator();
            for(;bbIt.hasNext();) {
               IExplodedBasicBlock bb = bbIt.next();
               SSAInstruction inst = bb.getInstruction();
               if (inst != null) {
                  //System.out.println("recording instruction " + inst);
                  int instIndex = -1;
                  for(int i = 0; i < allInst.length; i++)
                     if (allInst[i] != null && allInst[i].equals(inst)) {
                        instIndex = i;
                        break;
                     }
                  instructionContext.put(inst, new Triple(instIndex, node, bb));
                  addCallSites(node, inst);
               }
            }
        }
            
        /*for(CGNode node: icfg.getCallGraph()) { 
           //if (!isATarget(node)) continue; 
           ExplodedControlFlowGraph graph = (ExplodedControlFlowGraph)  icfg.getCFG(node);
           if (graph == null) continue; 
           java.util.Iterator<IExplodedBasicBlock>   bbIt = graph.iterator();
           for(;bbIt.hasNext();) {
             IExplodedBasicBlock bb = bbIt.next();
              SSAInstruction inst = bb.getInstruction();
                if (ssaInvokeInstructionClass == null && inst instanceof SSAInvokeInstruction) {
                   ssaInvokeInstructionClass = inst.getClass();
                   System.out.println("ssaInvokeInstructionClass = " + ssaInvokeInstructionClass);
                }
                instructionContext.put(inst, new Triple(0, node, bb));
                addCallSites(node, inst);
                if (inst instanceof SSAInvokeInstruction) {
                  if (((SSAInvokeInstruction)inst).getDeclaredTarget().getName().toString().indexOf("start") >= 0) {
                       System.out.println("MAY BE A REFLECTIVE THREAD START IN NODE " + node);  
                       HashSet<IClass> clset = getClassesCanBeCalledByReflectiveThread(((SSAInvokeInstruction)inst).getDeclaredTarget().getDeclaringClass().getName().toString());
                       for(IClass cl : clset) {
                         addToSet(calledViaReflection, cl, cha.lookupClass(((SSAInvokeInstruction)inst).getDeclaredTarget().getDeclaringClass()), node, bb);
                       }
                  }
                }
             }
        }*/
        
        getWaitingToLock(stackTraceFileName);
        getRelevantStackTraceLines2(projectName, stackTraceFileName);
        
        getRelevantStackTraceLines(projectName, stackTraceFileName);
        
    }
    
    public static void getEntryClasses(String fileName) {
        String line = "";
        try {
            FileReader fileReader = new FileReader(fileName);
            BufferedReader bufferedReader = new BufferedReader(fileReader);
            while ((line = bufferedReader.readLine()) != null) {
                parseEntryClasses(line);
            }
            bufferedReader.close();
        }
        catch (Exception e) {
            System.out.println(e);
        }
    }
    
    public static void parseEntryClasses(String line) {
        if (line.trim().startsWith("at")) {
            Pattern p = Pattern.compile("^.*(?=(\\())");
            Matcher m = p.matcher(line);
            while (m.find()) {
                //System.out.println(m.group());
                String a = m.group().replace("at ", "").trim();
                String s = a.replace(".", "/");
                String entryClass = "L" + s.substring(0, s.lastIndexOf("/"));
                //System.out.println(entryClass);
                if ( (!entryClassList.contains(entryClass)) && (entryClass.startsWith("Lorg") || (entryClass.startsWith("Ljava"))) ) {
                    entryClassList.add(entryClass);
                    System.out.println("Adding entry class: " + entryClass);
                }
            }
        }
        if (line.trim().startsWith("- waiting to lock") || line.trim().startsWith("- locked")) {
            Pattern p = Pattern.compile("\\(([^)]+)\\)");
            Matcher m = p.matcher(line);
            while (m.find()) {
                //System.out.println("@@@@@@@@: " + m.group());
                String a = m.group().replace("(a ", "").trim();
                String b = a.replace(")", "");
                String s = b.replace(".", "/");
                String entryClass = "L" + s;
                //System.out.println("@@@@@@@: " + entryClass);
                if ( (!entryClassList.contains(entryClass)) && (entryClass.startsWith("Lorg") || (entryClass.startsWith("Ljava"))) ) {
                    entryClassList.add(entryClass);
                    System.out.println("Adding entry class: " + entryClass);
                }
            }
        }
    }
    
    public static void generateRunFileLinux(String projectName, String entryClasses) throws IOException {
        String run = "-scopeFile \"/home/chelsea/Dropbox/Documents/Research/AliasedLockOrder/"
        //String run = "-scopeFile \"/home/chelsea/Documents/DeadlockProject/GenerateLockTypes/"
                + projectName + "/scope.txt\" "
                + "-entryClass \"" + entryClasses + "\" "
                //+ "-watchListFile \"/home/chelsea/Documents/DeadlockProject/GenerateLockTypes/"
                + "-targetFile \"/home/chelsea/Dropbox/Documents/Research/AliasedLockOrder/"
                + projectName + "/target.txt\"";
        System.out.println(run);
        
        //String folder = "/home/chelsea/Dropbox/Documents/Research/GenerateLockTypes/" + projectName + "/";
        //String folder = "/Users/chelseametcalf/Dropbox/Documents/Research/AliasedLockOrder/" + projectName + "/";
        FileWriter writer = new FileWriter(folderPath + "run-linux2.txt");
        writer.append(run);
        writer.close();
    }
    
    public static void generateScopeFileLinux(String projectName, String version) throws IOException {
        String scope = "Primordial,Java,stdlib,none\n" +
            "Primordial,Java,jarFile,primordial.jar.model\n" +
            "Application,Java,binaryDir,/home/chelsea/Documents/"+version+"\n" +
            "Application,Java,sourceDir,/home/chelsea/Documents/"+version+"-sources";
        System.out.println(scope);
        
        //String folder = "/home/chelsea/Dropbox/Documents/Research/GenerateLockTypes/" + projectName + "/";
        //String folder = "/Users/chelseametcalf/Dropbox/Documents/Research/AliasedLockOrder/" + projectName + "/";
        FileWriter writer = new FileWriter(folderPath + "scope2.txt");
        writer.append(scope);
        writer.close();
    }
    
    public static void getRelevantStackTraceLines2(String projectName, String fileName) {
      ArrayList<String> encInfo = new ArrayList<String>();
      int lineCount = getNumberOfLines(fileName);
      String enclosedClass = "";
      String enclosedMethodThatCallsMethod = "";
      String enclosedMethod = "";
      String enclosedLockType = "";
      String enclosingClass = "";
      String enclosingMethod = "";
      String enclosingLockType = "";
      int sectionStackTrace = 0;
      try {
          FileReader fileReader = new FileReader(fileName);
          BufferedReader bufferedReader = new BufferedReader(fileReader);
          String currentLine = "";
          while ((currentLine = bufferedReader.readLine()) != null) {
              if (currentLine.trim().contains("\":")) {
                sectionStackTrace++;
                int i = 0;
                st: while (((currentLine = bufferedReader.readLine()) != null) && i < lineCount) {
                  //System.out.println("Adding " + currentLine + " to encInfo");
                  encInfo.add(currentLine.trim());
                  i++;
                  //for (int i = 0; i < waitingToLockList.size(); i++) {
                    if ( (sectionStackTrace == 1) && (currentLine.trim().contains("locked") && currentLine.trim().contains(waitingToLockList.get(1))) ) {
                      System.out.println("SECTION OF STACKTRACE: " + sectionStackTrace + "\t" + currentLine);
                      break st;
                    }
                    else if ( (sectionStackTrace == 2) && (currentLine.trim().contains("locked") && currentLine.trim().contains(waitingToLockList.get(0))) ) {
                      System.out.println("SECTION OF STACKTRACE: " + sectionStackTrace + "\t" + currentLine);
                      break st;
                    }
                  //}
                    //encInfo.clear();
                    //break;
                }
                
                
                
                  /*int i = 0;
                  while (((currentLine = bufferedReader.readLine()) != null) && i < lineCount) {
                      //System.out.println("Adding " + currentLine + " to encInfo");
                      encInfo.add(currentLine.trim());
                      i++;
                      if (currentLine.trim().contains("locked")) {
                          //System.out.println("ENC INFO: " + encInfo);
                          int lineAboveLockedLine = 0;
                          for (int j = 0; j < encInfo.size(); j++) {
                              if (j == 0) {
                                  enclosedMethod = returnMethod(encInfo.get(j));
                              }
                              if (j == 1) {
                                  enclosedLockType = returnLockType(encInfo.get(j));
                              }
                              if (j == 2) {
                                  enclosedMethodThatCallsMethod = returnMethod(encInfo.get(j));
                                  enclosedClass = returnClass(encInfo.get(j));
                              }
                              if (encInfo.get(j).contains("locked")) {
                                  enclosingLockType = returnLockType(encInfo.get(j));
                                  lineAboveLockedLine = j - 1;
                                  //System.out.println("*********" + lineAboveLockedLine);
                                  enclosingMethod = returnMethod(encInfo.get(lineAboveLockedLine));
                                  enclosingClass = returnClass(encInfo.get(lineAboveLockedLine));
                              }
                          }
                          generateTarget(projectName, enclosedClass, enclosedMethodThatCallsMethod, enclosedMethod, enclosedLockType, enclosingClass, enclosingMethod, enclosingLockType);
                          encInfo.clear();
                          break;
                      }
                  }*/
              }
          }
          bufferedReader.close();
      }
      catch (Exception e) {
          System.out.println(e);
      }
  }
    
    public static void getRelevantStackTraceLines(String projectName, String fileName) {
        ArrayList<String> encInfo = new ArrayList<String>();
        int lineCount = getNumberOfLines(fileName);
        //int key = 0;
        String enclosedClass = "";
        String enclosedMethodThatCallsMethod = "";
        String enclosedMethod = "";
        String enclosedLockType = "";
        String enclosingClass = "";
        String enclosingMethod = "";
        String enclosingLockType = "";
        try {
            FileReader fileReader = new FileReader(fileName);
            BufferedReader bufferedReader = new BufferedReader(fileReader);
            String currentLine = "";
            while ((currentLine = bufferedReader.readLine()) != null) {
                if (currentLine.trim().contains("\":")) {
                    int i = 0;
                    while (((currentLine = bufferedReader.readLine()) != null) && i < lineCount) {
                        //System.out.println("Adding " + currentLine + " to encInfo");
                        encInfo.add(currentLine.trim());
                        i++;
                        if (currentLine.trim().contains("locked")) {
                            //System.out.println("ENC INFO: " + encInfo);
                            int lineAboveLockedLine = 0;
                            for (int j = 0; j < encInfo.size(); j++) {
                                if (j == 0) {
                                    enclosedMethod = returnMethod(encInfo.get(j));
                                }
                                if (j == 1) {
                                    enclosedLockType = returnLockType(encInfo.get(j));
                                }
                                if (j == 2) {
                                    enclosedMethodThatCallsMethod = returnMethod(encInfo.get(j));
                                    enclosedClass = returnClass(encInfo.get(j));
                                }
                                if (encInfo.get(j).contains("locked")) {
                                    enclosingLockType = returnLockType(encInfo.get(j));
                                    lineAboveLockedLine = j - 1;
                                    //System.out.println("*********" + lineAboveLockedLine);
                                    enclosingMethod = returnMethod(encInfo.get(lineAboveLockedLine));
                                    enclosingClass = returnClass(encInfo.get(lineAboveLockedLine));
                                }
                            }
                            generateTarget(projectName, enclosedClass, enclosedMethodThatCallsMethod, enclosedMethod, enclosedLockType, enclosingClass, enclosingMethod, enclosingLockType);
                            encInfo.clear();
                            break;
                        }
                    }
                }
            }
            bufferedReader.close();
        }
        catch (Exception e) {
            System.out.println(e);
        }
    }
    
    public static void generateTarget(String projectName, String enclosedClass, String enclosedMethodThatCallsMethod, String enclosedMethod, String enclosedLockType, 
            String enclosingClass, String enclosingMethod, String enclosingLockType) throws IOException {
            String filterEnclosing = "";
            String filterEnclosed = "";
            String enclosingLineNum = "0";
            String enclosedLineNum = "";

            if (!enclosingClass.equals(enclosingLockType)) {
                String enclosingMonitorEnter = "monitorenter";
                CGNode enclosingMethodNode = null;
                for(CGNode node: icfg.getCallGraph()) {
                  ExplodedControlFlowGraph graph = (ExplodedControlFlowGraph) icfg.getCFG(node);
                  if (graph == null) continue;
                  //if (node.getMethod().toString().indexOf("fakeRootMethod") >= 0) continue;
                  if (node.getMethod().getDeclaringClass().getName().getClassName().toString().indexOf("FakeRootClass") >= 0) continue;
                  if (!(node.toString().indexOf("Application") >= 0)) continue;
                  if (node.getMethod().toString().indexOf("<clinit>") >=0) continue;
                  if (node.getMethod().toString().indexOf("<init>") >=0) continue;
                  enclosingMethodNode = findEnclosingNode(node, enclosingMethod);
                  if (foundEnclosingMethodNode == true) {
                    foundEnclosingMethodNode = false;
                    break;
                  }
                }
                System.out.println("METHOD NODE FOR ENCLOSING LINE NUM: " + enclosingMethodNode);
                enclosingLineNum = findEnclosingLineNum(enclosingMethodNode, enclosingLockType);
                filterEnclosing = "filterEnclosing=" + enclosingClass + ";" + enclosingMonitorEnter + ";" + enclosingLineNum + ";" + enclosingLockType;
            }
            else {
                filterEnclosing = "filterEnclosing=" + enclosingClass + ";" + enclosingMethod + ";" + enclosingLineNum + ";" + enclosingLockType;
            }
            
            CGNode methodNodeThatCallsMethod = null;
            for(CGNode node: icfg.getCallGraph()) {
              ExplodedControlFlowGraph graph = (ExplodedControlFlowGraph) icfg.getCFG(node);
              if (graph == null) continue;
              //if (node.getMethod().toString().indexOf("fakeRootMethod") >= 0) continue;
              if (node.getMethod().getDeclaringClass().getName().getClassName().toString().indexOf("FakeRootClass") >= 0) continue;
              if (!(node.toString().indexOf("Application") >= 0)) continue;
              if (node.getMethod().toString().indexOf("<clinit>") >=0) continue;
              if (node.getMethod().toString().indexOf("<init>") >=0) continue;
              methodNodeThatCallsMethod = findNode(node, enclosedMethodThatCallsMethod);
              if (foundMethodNodeThatCallsMethod == true) {
                foundMethodNodeThatCallsMethod = false;
                break;
              }
            }
            System.out.println("METHOD NODE FOR ENCLOSED LINE NUM: " + methodNodeThatCallsMethod);
            enclosedLineNum = findEnclosedLineNum(methodNodeThatCallsMethod, enclosedMethod);
            filterEnclosed = "filterEnclosed=" + enclosedClass + ";" + enclosedMethodThatCallsMethod + ";" + enclosedMethod + ";" + enclosedLineNum + ";" + enclosedLockType;
             
            String target = "//Two options for filterEnclosing:\n" + 
                "//1) classname;method that grabs the enclosing lock; 0 (as line no); lock type\n" + 
                "//2) file name (e.g. A.java); monitorenter; line no; lock type\n" + 
                filterEnclosing + "\n" + 
                "//classname;method that calls the enclosed locking instruction; enclosed locking instruction (methodname or monitorenter); line number in that method; line  no; lock type\n" + 
                filterEnclosed;
            System.out.println(target);

            //String folder = "/Users/chelseametcalf/Dropbox/Documents/Research/AliasedLockOrder/" + projectName + "/";
            targetNumber++;
            String targetName = "target" + targetNumber + ".txt";
            FileWriter writer = new FileWriter(folderPath + targetName);
            writer.append(target);
            writer.close();
    }
    
    public static int getNumberOfLines(String fileName) {
        int lineCount = 0;
        try {
            FileReader fileReader = new FileReader(fileName);
            BufferedReader bufferedReader = new BufferedReader(fileReader);
            String currentLine = "";
            while ((currentLine = bufferedReader.readLine()) != null) {
                lineCount++;
            }
            bufferedReader.close();
        }
        catch (Exception e) {
            System.out.println(e);
        }
        System.out.println("Number of lines in file: " + lineCount);
        return lineCount;
    }
    
    public static ArrayList<String> getWaitingToLock(String fileName) {
      //ArrayList<String> waitingToLockList = new ArrayList<String>();
      try {
          FileReader fileReader = new FileReader(fileName);
          BufferedReader bufferedReader = new BufferedReader(fileReader);
          String currentLine = "";
          while ((currentLine = bufferedReader.readLine()) != null) {
            if (currentLine.trim().startsWith("- waiting to lock")) {
              Pattern p = Pattern.compile("\\(([^)]+)\\)");
              Matcher m = p.matcher(currentLine);
              while (m.find()) {
                //System.out.println("@@@@@@@@: " + m.group());
                String lockType = m.group();
                waitingToLockList.add(lockType);
                System.out.println("WAITING LOCK TYPE: " + lockType);
              }
            }
          }
          bufferedReader.close();
      }
      catch (Exception e) {
          System.out.println(e);
      }
      System.out.println("Waiting To Lock Types: " + waitingToLockList);
      return waitingToLockList;
  }
    
    public static String returnMethod(String line) {
        String method = "";
        if (line.trim().startsWith("at")) {
            Pattern p = Pattern.compile("([\\s\\n\\r]*[\\w]+)[\\s\\n\\r]*(?=\\(.*\\))");
            Matcher m = p.matcher(line);
            while (m.find()) {
                //System.out.println("@@@: " + m.group());
                method = m.group().trim();
                System.out.println("METHOD: " + method);
            }
        }
        return method;
    }
    
    public static String returnLockType(String line) {
        String lockType = "";
        if (line.trim().startsWith("- waiting to lock")) {
            Pattern p = Pattern.compile("\\(([^)]+)\\)");
            Matcher m = p.matcher(line);
            while (m.find()) {
                //System.out.println("@@@@@@@@: " + m.group());
                String a = m.group().replace("(a ", "").trim();
                String b = a.replace(")", "");
                String s = b.replace(".", "/");
                if (s.startsWith("L")) {
                  lockType = s;
                }
                else {
                  lockType = "L" + s;
                }
                System.out.println("ENCLOSED LOCK TYPE: " + lockType);
            }
            //break;
        }
        if (line.trim().contains("locked")) {
            Pattern p = Pattern.compile("\\(([^)]+)\\)");
            Matcher m = p.matcher(line);
            while (m.find()) {
                //System.out.println("@@@@@@@@: " + m.group());
                String a = m.group().replace("(a ", "").trim();
                String b = a.replace(")", "");
                String s = b.replace(".", "/");
                if (s.startsWith("L")) {
                  lockType = s;
                }
                else {
                  lockType = "L" + s;
                }
                System.out.println("ENCLOSING LOCK TYPE: " + lockType);
            }
        }
        return lockType;
    }
    
    public static String returnClass(String line) {
        String eclass = "";
        if (line.trim().startsWith("at")) {
            Pattern p = Pattern.compile("^.*(?=(\\())");
            Matcher m = p.matcher(line);
            while (m.find()) {
                //System.out.println(m.group());
                String a = m.group().replace("at ", "").trim();
                String s = a.replace(".", "/");
                eclass = "L" + s.substring(0, s.lastIndexOf("/"));
                System.out.println("CLASS: " + eclass);
            }
        }
        return eclass;
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
      String result = "";
      try {
        IBytecodeMethod method = (IBytecodeMethod)ir.getMethod();
        IClass decclass =  method.getDeclaringClass();
        int bytecodeIndex = method.getBytecodeIndex(instIndex);
        int sourceLineNum = method.getLineNumber(bytecodeIndex);   
        result = "line " + sourceLineNum + " in " + (decclass.getSourceFileName() == null ? decclass.getName() : decclass.getSourceFileName());
      }
      catch(InvalidClassFileException e) {
         System.out.println(e);
      }
      catch(ClassCastException e) {
        result = "Fake class and method";
      }
      return result;
    }
    
    private static String prettyPrintLineNum(SSAInstruction inst) {
      //if (inst instanceof SSAInvokeInstruction)
      //  return inst.toString();
      Triple<Integer, CGNode, IExplodedBasicBlock> contextInfo = instructionContext.get(inst);
      int instIndex = contextInfo.val1.intValue();
      CGNode node = contextInfo.val2;        
      String instSt = inst.toString();
      int pos = instSt.indexOf("(");
      if (pos >= 0)
         instSt = instSt.substring(0,pos); 
      return prettyPrintLineNum(node.getIR(), instIndex);  
    }
    
    private static String prettyPrintLineNum(IR ir, int instIndex) {
      String lineNum = "";
      try {
        IBytecodeMethod method = (IBytecodeMethod)ir.getMethod();
        IClass decclass =  method.getDeclaringClass();
        Integer bytecodeIndex = method.getBytecodeIndex(instIndex);
        Integer sourceLineNum = method.getLineNumber(bytecodeIndex);   
        lineNum = sourceLineNum.toString();
      }
      catch(InvalidClassFileException e) {
         System.out.println(e);
      }
      System.out.println("LINE NUM: " + lineNum);
      return lineNum;
    }
    
    static String findEnclosedLineNum(CGNode methodNodeThatCallsMethod, String methodName) {
      String enclosedLineNum = "";
      SSAInstruction in = findCallToInstr(methodNodeThatCallsMethod, methodName);
      System.out.println("FOUND CALL TO INSTR: " + prettyPrint(in));
      enclosedLineNum = prettyPrintLineNum(in);
      return enclosedLineNum;
    }
    
    static String findEnclosingLineNum(CGNode node, String enclosingLockType) {
      String enclosingLineNum = "";
      IR ir = node.getIR();
      SSAInstruction[] insts = ir.getInstructions();
      for(int i = 0; i < insts.length; i++) {
        // If synch(o)
        if (insts[i] instanceof SSAMonitorInstruction) {
          SSAInstruction in = insts[i];
          if (in != null && (((SSAMonitorInstruction)in).isMonitorEnter()) ) {
            //System.out.println("MONITOR INST-----------------------------------: " + prettyPrint(in));
            
            int ref = ((SSAMonitorInstruction)in).getRef();
            // Assume that the lock is a local variable also includes this
            OrdinalSet<? extends InstanceKey> lockSet = pointerAnalysis.getPointsToSet(heapModel.getPointerKeyForLocal(node, ref));
            //System.out.println("LOCKSET: \t" + lockSet);
            for(InstanceKey ik : lockSet) {
                //System.out.println(ik.toString());
                if (ik.toString().indexOf("NEW <Application," + enclosingLockType + ">") >= 0) {
                  System.out.println("MONITOR INST-----------------------------------: " + prettyPrint(in) + "   LOCK TYPE:  " + enclosingLockType + "\t" + ik.toString());
                  enclosingLineNum = prettyPrintLineNum(in);
                  return enclosingLineNum;
                }
            }
            
            //enclosingLineNum = prettyPrintLineNum(in);
            //return enclosingLineNum;
          }
        }
      }
      System.out.println("Failed to find monitorenter in " + node);
      return null;
    }

    public static SSAInstruction findCallToInstr(CGNode n, String methodName) {
       IR ir = n.getIR();
       if (ir == null) return null;
       for (Iterator<SSAInstruction> it = ir.iterateAllInstructions(); it.hasNext();) {
           SSAInstruction s = it.next();
           if (s instanceof SSAAbstractInvokeInstruction) {
             SSAAbstractInvokeInstruction call = (SSAAbstractInvokeInstruction) s;
             if (call.getCallSite().getDeclaredTarget().getName().toString().equals(methodName)) {
               return s;
             }
           }
       }
       System.out.println("Failed to find call to " + methodName + " in " + n);
       //Assertions.UNREACHABLE("failed to find call to " + methodName + " in " + n);
       return null;
     }
    
    public static CGNode findEnclosingNode(CGNode n, String methodName) {
      //System.out.println("CHECKING NODE: " + n);
      CGNode returnNode;
      
      if (n.getMethod().getName().toString().equals(methodName)) {
        returnNode = n;
        System.out.println("FOUND ENCLOSING METHOD NODE: " + returnNode);
        //System.out.println(returnNode.getMethod().getDeclaringClass().getName());
        foundEnclosingMethodNode = true;
        return returnNode;
      }
      //Assertions.UNREACHABLE("failed to find call to " + methodName + " in " + n);
      System.out.println("Failed to find " + methodName);
      return null;
    }
    
    public static CGNode findNode(CGNode n, String methodName) {
      //System.out.println("CHECKING NODE: " + n);
      CGNode returnNode;
      
      if (n.getMethod().getName().toString().equals(methodName)) {
        returnNode = n;
        System.out.println("FOUND METHOD NODE THAT CALLS METHOD: " + returnNode);
        //System.out.println(returnNode.getMethod().getDeclaringClass().getName());
        foundMethodNodeThatCallsMethod = true;
        return returnNode;
      }
      //Assertions.UNREACHABLE("failed to find call to " + methodName + " in " + n);
      return null;
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
   
   private static void addCallSites(CGNode node, SSAInstruction inst) {
     if (inst instanceof SSAInvokeInstruction) {
           java.util.Set<CGNode> mnodes = cg.getNodes(((SSAInvokeInstruction)inst).getCallSite().getDeclaredTarget());
           //java.util.Set<CGNode> mnodes = getPossibleNodes(inst); 
           for(CGNode n : mnodes) 
              addToSetOld(callSites, n, inst);         
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
    
    private static void configureAndCreateCallGraph(String scopeFile, String mainClass, String entryClass) throws IOException, ClassHierarchyException, CallGraphBuilderCancelException  {
        File exclusionsFile = null;
        AnalysisScope scope = AnalysisScopeReader.readJavaScope(scopeFile, exclusionsFile, GenerateFiles.class.getClassLoader()); 
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