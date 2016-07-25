package gov.nasa.jpf.listener;

import gov.nasa.jpf.Config;
import gov.nasa.jpf.ListenerAdapter;
import gov.nasa.jpf.annotation.JPFOption;
import gov.nasa.jpf.search.Search;
import gov.nasa.jpf.vm.ChoiceGenerator;
import gov.nasa.jpf.vm.ClassInfo;
import gov.nasa.jpf.vm.ElementInfo;
import gov.nasa.jpf.vm.Instruction;
import gov.nasa.jpf.vm.VM;
import gov.nasa.jpf.vm.MethodInfo;
import gov.nasa.jpf.vm.ThreadInfo;
import gov.nasa.jpf.JPF;
import gov.nasa.jpf.jvm.bytecode.INVOKESPECIAL;
import gov.nasa.jpf.jvm.bytecode.JVMInvokeInstruction;
import gov.nasa.jpf.jvm.bytecode.VirtualInvocation;
import gov.nasa.jpf.vm.MJIEnv;
import gov.nasa.jpf.jvm.bytecode.MONITORENTER;
import gov.nasa.jpf.vm.InfoObject;
import gov.nasa.jpf.vm.bytecode.InstanceInvokeInstruction;
import gov.nasa.jpf.vm.ThreadChoiceGenerator;

import java.io.PrintWriter;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.DocumentBuilder;
import org.w3c.dom.Document;
import org.w3c.dom.NodeList;
import org.w3c.dom.Node;
import org.w3c.dom.Element;
import java.io.File;
import java.util.*;

public class ThreadAnalyzer extends ListenerAdapter {
  
  @JPFOption(type = "Boolean", key = "et.print_insn", defaultValue = "true", comment = "print executed bytecode instructions") 
  boolean printInsn = true;
  
  @JPFOption(type = "Boolean", key = "et.print_src", defaultValue = "true", comment = "print source lines")
  boolean printSrc = true;
  
  @JPFOption(type = "Boolean", key = "et.print_mth", defaultValue = "true", comment = "print executed method names")
  boolean printMth = true;
  
  @JPFOption(type = "Boolean", key = "et.skip_init", defaultValue = "true", comment = "do not log execution before entering main()")
  boolean skipInit = false;
  
  boolean showShared = false;
  
  PrintWriter out;
  String lastLine;
  MethodInfo lastMi;
  String linePrefix;
  
  boolean skip;
  MethodInfo miMain; // just to make init skipping more efficient

  static final String INDENT = "  ";

  static  class Pair<T1, T2> {
    T1 val1;
    T2 val2;

    public Pair(T1 v1, T2 v2) {
      val1 = v1;
      val2 = v2;
    }      
  }

  static HashMap<Integer, Object> attributeMap = new HashMap<Integer, Object>();
  static HashMap<Integer, HashSet<Integer>> isNestedMapFirst = new HashMap<Integer,HashSet<Integer>>();
  static HashMap<Integer, HashSet<Integer>> isNestedMapSecond = new HashMap<Integer,HashSet<Integer>>();
  static HashMap<Integer, HashSet<Integer>> isReachableMapFirst = new HashMap<Integer,HashSet<Integer>>();
  static HashMap<Integer, HashSet<Integer>> isReachableMapSecond = new HashMap<Integer,HashSet<Integer>>();


  Integer readXMLfileReturnID(String mode, int lineNUM, String methodNAME, String classNAME) {
    Integer attributeID = -1;
    int line = 0;
    String methodName = "";
    String className = "";
    HashSet<Integer> isNestedSet = new HashSet<Integer>();
    HashSet<Integer> isReachableSet = new HashSet<Integer>();
    Integer nestedId1 = -1;
    Integer nestedId2 = -1;
    Integer reachableId1 = -1;
    Integer reachableId2 = -1;

    try {
      File xmlFile = new File("/Users/chelseametcalf/Documents/XML/CodeInfo.xml");
      DocumentBuilderFactory dbFactory = DocumentBuilderFactory.newInstance();
      DocumentBuilder dBuilder = dbFactory.newDocumentBuilder();
      Document doc = dBuilder.parse(xmlFile);
      doc.getDocumentElement().normalize();
      //System.out.println("Root Element : " + doc.getDocumentElement().getNodeName());
      NodeList relationList = doc.getElementsByTagName("relation");
      //System.out.println("----------------------------");
      for (int i = 0; i < relationList.getLength(); i++) {
        Node relationNode = relationList.item(i);
        //System.out.println("\nCurrent Element : " + relationNode.getNodeName());
        if (relationNode.getNodeType() == Node.ELEMENT_NODE) {
          Element relationElement = (Element) relationNode;

          if (mode.equals("isAClass")) {
            NodeList classList = relationElement.getElementsByTagName("isAClass");
            for (int j = 0; j < classList.getLength(); j++) {
              Node classNode = classList.item(j);
              Element classElement = (Element) classNode;
              //System.out.println("isAClass ID : " + classElement.getAttribute("id"));
              //System.out.println("Class : " + classElement.getElementsByTagName("c").item(0).getTextContent());
              //attributeID = Integer.parseInt(classElement.getAttribute("id"));
              className = classElement.getElementsByTagName("c").item(0).getTextContent();
              if ( className.equals(classNAME) ) {
                System.out.println("Assigning attribute ID for method!!!");
                attributeID = Integer.parseInt(classElement.getAttribute("id"));
                return attributeID;
              }
            }
          }

          else if (mode.equals("isAMethod")) {
            NodeList methodList = relationElement.getElementsByTagName("isAMethod");
            for (int j = 0; j < methodList.getLength(); j++) {
              Node methodNode = methodList.item(j);
              Element methodElement = (Element) methodNode;
              /*System.out.println("isAMethod ID : " + methodElement.getAttribute("id"));
              System.out.println("Method : " + methodElement.getElementsByTagName("m").item(0).getTextContent());
              System.out.println("Class : " + methodElement.getElementsByTagName("c").item(0).getTextContent());*/
              //attributeID = Integer.parseInt(methodElement.getAttribute("id"));
              methodName = methodElement.getElementsByTagName("m").item(0).getTextContent();
              className = methodElement.getElementsByTagName("c").item(0).getTextContent();
              if ( (methodName.equals(methodNAME)) && (className.equals(classNAME)) ) {
                System.out.println("Assigning attribute ID for method!!!");
                attributeID = Integer.parseInt(methodElement.getAttribute("id"));
                return attributeID;
              }
            }
          }

          else if (mode.equals("isAMonitorEnter")) {
            NodeList monitorEnterList = relationElement.getElementsByTagName("isAMonitorEnter");
            for (int j = 0; j < monitorEnterList.getLength(); j++) {
              Node monitorEnterNode = monitorEnterList.item(j);
              Element monitorEnterElement = (Element) monitorEnterNode;
              /*System.out.println("isAMonitorEnter ID : " + monitorEnterElement.getAttribute("id"));
              System.out.println("File : " + monitorEnterElement.getElementsByTagName("f").item(0).getTextContent());
              System.out.println("Line : " + monitorEnterElement.getElementsByTagName("l").item(0).getTextContent());
              System.out.println("Method : " + monitorEnterElement.getElementsByTagName("m").item(0).getTextContent());
              System.out.println("Class : " + monitorEnterElement.getElementsByTagName("c").item(0).getTextContent());*/
              line = Integer.parseInt(monitorEnterElement.getElementsByTagName("l").item(0).getTextContent());
              methodName = monitorEnterElement.getElementsByTagName("m").item(0).getTextContent();
              //className = monitorEnterElement.getElementsByTagName("c").item(0).getTextContent();
              //System.out.println("line: " + line + " lineNUM: " + lineNUM + "\t" + "methodName: " + methodName + " methodNAME: " + methodNAME);
              if ( (line == lineNUM) && (methodName.equals(methodNAME)) ) {
                System.out.println("Assigning attribute ID for monitorenter!!!");
                attributeID = Integer.parseInt(monitorEnterElement.getAttribute("id"));
                return attributeID;
              }
            }
          }

          else if (mode.equals("isAMethodInvoke")) {
            NodeList methodInvokeList = relationElement.getElementsByTagName("isAMethodInvoke");
            for (int j = 0; j < methodInvokeList.getLength(); j++) {
              Node methodInvokeNode = methodInvokeList.item(j);
              Element methodInvokeElement = (Element) methodInvokeNode;
              /*System.out.println("isAMethodInvoke ID : " + methodInvokeElement.getAttribute("id"));
              System.out.println("Method : " + methodInvokeElement.getElementsByTagName("m").item(0).getTextContent());
              System.out.println("File : " + methodInvokeElement.getElementsByTagName("f").item(0).getTextContent());
              System.out.println("Line : " + methodInvokeElement.getElementsByTagName("l").item(0).getTextContent());*/
              
              line = Integer.parseInt(methodInvokeElement.getElementsByTagName("l").item(0).getTextContent());
              //methodName = methodInvokeElement.getElementsByTagName("m").item(0).getTextContent();
              //System.out.println("INVOKE ELEMENT: line: " + line + " lineNUM: " + lineNUM + "\t" + "methodName: " + methodName + " methodNAME: " + methodNAME);
              if ( line == lineNUM ) {
                System.out.println("Assigning attribute ID for method invoke!!!");
                attributeID = Integer.parseInt(methodInvokeElement.getAttribute("id"));
                return attributeID;
              }
            }
          }

          NodeList synchronizedMethodList = relationElement.getElementsByTagName("isSynchronizedMethod");
          for (int j = 0; j < synchronizedMethodList.getLength(); j++) {
            Node synchronizedMethodNode = synchronizedMethodList.item(j);
            Element synchronizedMethodElement = (Element) synchronizedMethodNode;
            //System.out.println("isSynchronizedMethod ID : " + synchronizedMethodElement.getAttribute("id"));
          }

          NodeList nestedAcquiredList = relationElement.getElementsByTagName("isNestedAcquired");
          for (int j = 0; j < nestedAcquiredList.getLength(); j++) {
            Node nestedAcquiredNode = nestedAcquiredList.item(j);
            Element nestedAcquiredElement = (Element) nestedAcquiredNode;
            /*System.out.println("isNestedAcquired ID1 : " + nestedAcquiredElement.getAttribute("id1"));
            System.out.println("isNestedAcquired ID2 : " + nestedAcquiredElement.getAttribute("id2"));*/
            nestedId1 = Integer.parseInt(nestedAcquiredElement.getAttribute("id1"));
            nestedId2 = Integer.parseInt(nestedAcquiredElement.getAttribute("id2"));

            addToSet(isNestedMapFirst, nestedId1, nestedId2);
            addToSet(isNestedMapSecond, nestedId2, nestedId1);
            
            //isNestedSet = new HashSet<Integer>();
            //isNestedSet.add(nestedId1);
            //isNestedSet.add(nestedId2);
            //isNestedMap.put(key, isNestedSet);
          }

          NodeList reachableNestedAcquiredList = relationElement.getElementsByTagName("isReachable");
          for (int j = 0; j < reachableNestedAcquiredList.getLength(); j++) {
            Node reachableNestedAcquiredNode = reachableNestedAcquiredList.item(j);
            Element reachableNestedAcquiredElement = (Element) reachableNestedAcquiredNode;
            /*System.out.println("isReachableNestedAcquired ID1 : " + reachableNestedAcquiredElement.getAttribute("id1"));
            System.out.println("isReachableNestedAcquired ID2 : " + reachableNestedAcquiredElement.getAttribute("id2"));*/
            reachableId1 = Integer.parseInt(reachableNestedAcquiredElement.getAttribute("id1"));
            reachableId2 = Integer.parseInt(reachableNestedAcquiredElement.getAttribute("id2"));

            //if (isReachableMap.containsKey(reachableKey)) {
            addToSet(isReachableMapFirst, reachableId1, reachableId2);
            addToSet(isReachableMapSecond, reachableId2, reachableId1);
            //}
            //isReachableSet = new HashSet<Integer>();
            //isReachableSet.add(reachableId1);
            //isReachableSet.add(reachableId2);
            //isReachableMap.put(key, isReachableSet);
          }

         }
        }
      } catch (Exception e) {
        e.printStackTrace();
      }
    //System.out.println("isNestedMap: " + isNestedMapSecond);
    //System.out.println("isReachableMap: " + isReachableMap);
    return attributeID;
  }

  public static void addToSet(HashMap<Integer, HashSet<Integer>> oneToMany, Integer key, Integer value) {
    HashSet<Integer> set; 
    if (oneToMany.containsKey(key)) {
        set = oneToMany.remove(key);
    }
    else {
        set = new HashSet<Integer>();
    }
    //boolean result = !set.contains(value);
    set.add(value);
    oneToMany.put(key, set);
    //return result;
  }
  
  public ThreadAnalyzer (Config config) {
    /** @jpfoption et.print_insn : boolean - print executed bytecode instructions (default=true). */
    printInsn = config.getBoolean("et.print_insn", true);

    /** @jpfoption et.print_src : boolean - print source lines (default=false). */
    printSrc = config.getBoolean("et.print_src", true);

    /** @jpfoption et.print_mth : boolean - print executed method names (default=false). */
    printMth = config.getBoolean("et.print_mth", true);

    /** @jpfoption et.skip_init : boolean - do not log execution before entering main() (default=true). */
    skipInit = config.getBoolean("et.skip_init", true);
    
    showShared = config.getBoolean("et.show_shared", true);
    
    if (skipInit) {
      skip = true;
    }
    
    out = new PrintWriter(System.out, true);
  }
  
  /******************************************* SearchListener interface *****/
  
  //--- the ones we are interested in
  @Override
  public void instructionExecuted(VM vm, ThreadInfo ti, Instruction nextInsn, Instruction executedInsn) {
    MethodInfo mi = executedInsn.getMethodInfo();
    ClassInfo mci = mi.getClassInfo();
    //out.println("Instruction: " + executedInsn + "\t" + executedInsn.getSourceLine() + "\n" + "Class Name: " + mci.getName() + "\n" + "Method Name: " + mi.getName());
    Instruction inst[] = mi.getInstructions();
    int line = 0;
    String methodName = "";
    String className = "";
    String mode = "";
    for (int i = 0; i < inst.length; i++) {
      /*if (inst[i] instanceof MONITORENTER) {
        line = inst[i].getLineNumber();
        out.println("FOUND MONITORENTER INSTRUCTION: " + inst[i] + "\t" + "LINE NUMBER: " + line + "  IN CLASS: " + mci.getName() + ", METHOD: " + mi.getName());
      }
      if (inst[i] instanceof JVMInvokeInstruction) {
        line = inst[i].getLineNumber();
        out.println("FOUND INVOKE INSTRUCTION: " + inst[i] + "\t" + "LINE NUMBER: " + line + "  IN CLASS: " + mci.getName() + ", METHOD: " + mi.getName());
      }*/
      line = inst[i].getLineNumber();
      methodName = mi.getName();
      className = mci.getName();
      if (inst[i] instanceof MONITORENTER) {
        mode = "isAMonitorEnter";
        addingAttributes(inst[i], line, methodName, className, mode);
      }
      else if (inst[i] instanceof JVMInvokeInstruction) {
        mode = "isAMethodInvoke";
        addingAttributes(inst[i], line, methodName, className, mode);
      }
    }
  }

  @Override
  public void classLoaded (VM vm, ClassInfo ci) {
    String methodName = "";
    String className = "";
    String mode = "";
    for (MethodInfo mi : ci.getDeclaredMethodInfos()) {
      mode = "isAMethod";
      methodName = mi.getName();
      className = ci.getName();
      addingAttributes(mi, methodName, className, mode);
    }

    mode = "isAClass";
    addingAttributes(ci, className, mode);
  }

  void addingAttributes(Instruction inst, int line, String methodName, String className, String mode) {
    if (!inst.hasAttr()) {
      Integer attrID = readXMLfileReturnID(mode, line, methodName, className);
      if (attrID != -1) {
        System.out.println("Adding attribute for instruction: " + inst + " at line " + line + ", " + attrID);
        inst.addAttr(attrID);
        attributeMap.put(attrID, inst);
      }
    }
    else {
      System.out.println("Attribute for " + inst + " is already set at line " + line);
    }
  }

  void addingAttributes(ClassInfo ci, String className, String mode) {
    int line = -1;
    String methodName = "";
    if (!ci.hasAttr()) {
      Integer attrID = readXMLfileReturnID(mode, line, methodName, className);
      if (attrID != -1) {
        System.out.println("Adding attribute for class: " + ci + ", " + attrID);
        ci.addAttr(attrID);
        attributeMap.put(attrID, ci);
      }
    }
    else {
      System.out.println("Attribute for " + ci + " is already set");
    }
  }

    void addingAttributes(MethodInfo mi, String methodName, String className, String mode) {
    int line = -1;
    if (!mi.hasAttr()) {
      Integer attrID = readXMLfileReturnID(mode, line, methodName, className);
      if (attrID != -1) {
        System.out.println("Adding attribute for method: " + mi + ", " + attrID);
        mi.addAttr(attrID);
        attributeMap.put(attrID, mi);
      }
    }
    else {
      System.out.println("Attribute for " + mi + " is already set");
    }
  }
  
  /****************************************** private stuff ******/

  void filterArgs (String[] args) {
    for (int i=0; i<args.length; i++) {
      if (args[i] != null) {
        if (args[i].equals("-print-lines")) {
          printSrc = true;
          args[i] = null;
        }
      }
    }
  }

  void logMethodCall(ThreadInfo ti, MethodInfo mi, int stackDepth) {
    out.print(ti.getId());
    out.print(":");

    for (int i=0; i<stackDepth%80; i++) {
      out.print(INDENT);
    }

    if (mi.isMJI()) {
      out.print("native ");
    }

    out.print("~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~METHOD CALL: " + mi.getFullName());

    if (ti.isFirstStepInsn()) {
      out.print("...");
    }

    out.println();
  }

  @Override
  public void executeInstruction (VM vm, ThreadInfo ti, Instruction insnToExecute) {
    MethodInfo mi = insnToExecute.getMethodInfo();

    if (mi != lastMi) {
      logMethodCall(ti, mi, ti.getStackDepth());
      lastMi = mi;

    } else if (insnToExecute instanceof JVMInvokeInstruction) {
      MethodInfo callee;

      // that's the only little gist of it - if this is a VirtualInvocation,
      // we have to dig the callee out by ourselves (it's not known
      // before execution)

      if (insnToExecute instanceof VirtualInvocation) {
        VirtualInvocation callInsn = (VirtualInvocation)insnToExecute;
        int objref = callInsn.getCalleeThis(ti);
        if (objref != MJIEnv.NULL){
          callee = callInsn.getInvokedMethod(ti, objref);
        } else {
          return; // this is causing a NPE, so don't report it as a unknown callee
        }

      } else if (insnToExecute instanceof INVOKESPECIAL) {
        INVOKESPECIAL callInsn = (INVOKESPECIAL)insnToExecute;
        callee = callInsn.getInvokedMethod(ti);

      } else {
        JVMInvokeInstruction callInsn = (JVMInvokeInstruction)insnToExecute;
        callee = callInsn.getInvokedMethod(ti);
      }

      if (callee != null) {
        if (callee.isMJI()) {
          logMethodCall(ti, callee, ti.getStackDepth()+1);
        }
      } else {
        out.println("ERROR: unknown callee of: " + insnToExecute);
      }
    }
  }

}

