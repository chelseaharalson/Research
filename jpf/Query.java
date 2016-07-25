import java.io.PrintWriter;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.DocumentBuilder;
import org.w3c.dom.Document;
import org.w3c.dom.NodeList;
import org.w3c.dom.Node;
import org.w3c.dom.Element;
import java.io.File;
import java.util.*;
import java.util.Scanner;

public class Query {
  
  static HashMap<Integer, Object> attributeMap = new HashMap<Integer, Object>();
  static HashMap<Integer, HashSet<Integer>> isNestedMapFirst = new HashMap<Integer,HashSet<Integer>>();
  static HashMap<Integer, HashSet<Integer>> isNestedMapSecond = new HashMap<Integer,HashSet<Integer>>();
  static HashMap<Integer, HashSet<Integer>> isReachableMapFirst = new HashMap<Integer,HashSet<Integer>>();
  static HashMap<Integer, HashSet<Integer>> isReachableMapSecond = new HashMap<Integer,HashSet<Integer>>();

  public static void main(String args[]) {
  	Scanner scanner = new Scanner(System.in);

  	readXMLfileReturnID();
  	System.out.println("isNestedMapFirst: " + isNestedMapFirst);
  	System.out.println("isNestedMapSecond: " + isNestedMapSecond);
  	System.out.println("isReachableMapFirst: " + isReachableMapFirst);
  	System.out.println("isReachableMapSecond: " + isReachableMapSecond);

  	int choice = -1;
  	while (choice != 0) {
  		System.out.println();
  		System.out.println("Please select a choice for the query. Press 0 to exit.");
	  	System.out.println("(1) Which ID would you like to see the NESTED set for? ");
	  	System.out.println("(2) Which ID would you like to see the REACHABLE set for? ");
	  	System.out.println("(3) Does the relation hold for a NESTED set? (Enter 2 IDs) ");
	  	System.out.println("(4) Does the relation hold for a REACHABLE set? (Enter 2 IDs) ");
	  	System.out.println();
	  	choice = scanner.nextInt();
	  	if (choice == 1) {
		  	//System.out.println("Which ID would you like to see the NESTED set for? ");
		  	int nestedSearchId = scanner.nextInt();
		  	for (Integer key : isNestedMapFirst.keySet()) {
		  		HashSet<Integer> isNestedSet = isNestedMapFirst.get(key);
		  		if (key == nestedSearchId) {
		  			System.out.println("Search ID: " + key + "\t Nested Set: " + isNestedSet);
		  		}
		  	}
	  	}

	  	else if (choice == 2) {
		  	//System.out.println("Which ID would you like to see the REACHABLE set for? ");
		  	int reachableSearchId = scanner.nextInt();
		  	for (Integer key : isReachableMapFirst.keySet()) {
		  		HashSet<Integer> isReachableSet = isReachableMapFirst.get(key);
		  		if (key == reachableSearchId) {
		  			System.out.println("Search ID: " + key + "\t Reachable Set: " + isReachableSet);
		  		}
		  	}
	  	}

	  	else if (choice == 3) {
			int nestedSearchId1 = scanner.nextInt();
			int nestedSearchId2 = scanner.nextInt();
		  	for (Integer key : isNestedMapFirst.keySet()) {
		  		HashSet<Integer> isNestedSet = isNestedMapFirst.get(key);
		  		if (key == nestedSearchId1 && isNestedSet.contains(nestedSearchId2)) {
		  			System.out.println("Relation holds: True");
		  			break;
		  		}
		  		else {
		  			System.out.println("Relation holds: False");
		  			break;
		  		}
		  	}
	  	}

	  	else if (choice == 4) {
	  		int reachableSearchId1 = scanner.nextInt();
			int reachableSearchId2 = scanner.nextInt();
		  	for (Integer key : isReachableMapFirst.keySet()) {
		  		HashSet<Integer> isReachableSet = isReachableMapFirst.get(key);
		  		if (key == reachableSearchId1 && isReachableSet.contains(reachableSearchId2)) {
		  			System.out.println("Relation holds: True");
		  			break;
		  		}
		  		else {
		  			System.out.println("Relation holds: False");
		  			break;
		  		}
		  	}
	  	}
  	}

  }

  public static void readXMLfileReturnID() {
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

          //if (mode.equals("isAClass")) {
            NodeList classList = relationElement.getElementsByTagName("isAClass");
            for (int j = 0; j < classList.getLength(); j++) {
              Node classNode = classList.item(j);
              Element classElement = (Element) classNode;
              //System.out.println("isAClass ID : " + classElement.getAttribute("id"));
              //System.out.println("Class : " + classElement.getElementsByTagName("c").item(0).getTextContent());
              //attributeID = Integer.parseInt(classElement.getAttribute("id"));
              className = classElement.getElementsByTagName("c").item(0).getTextContent();
              //if ( className.equals(classNAME) ) {
                System.out.println("Assigning attribute ID for method!!!");
                attributeID = Integer.parseInt(classElement.getAttribute("id"));
                //return attributeID;
              //}
            }
          //}

          //else if (mode.equals("isAMethod")) {
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
              //if ( (methodName.equals(methodNAME)) && (className.equals(classNAME)) ) {
                System.out.println("Assigning attribute ID for method!!!");
                attributeID = Integer.parseInt(methodElement.getAttribute("id"));
                //return attributeID;
              //}
            }
          //}

          //else if (mode.equals("isAMonitorEnter")) {
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
              //if ( (line == lineNUM) && (methodName.equals(methodNAME)) ) {
                System.out.println("Assigning attribute ID for monitorenter!!!");
                attributeID = Integer.parseInt(monitorEnterElement.getAttribute("id"));
                //return attributeID;
              //}
            }
          //}

          //else if (mode.equals("isAMethodInvoke")) {
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
              //if ( line == lineNUM ) {
                System.out.println("Assigning attribute ID for method invoke!!!");
                attributeID = Integer.parseInt(methodInvokeElement.getAttribute("id"));
                //return attributeID;
              //}
            }
          //}

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
    //return attributeID;
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
}