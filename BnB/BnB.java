import com.opencsv.*;
import java.io.BufferedReader;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.PriorityQueue;
import java.util.Queue;

/**
 *
 * @author chelseametcalf
 */
public class BnB {
    
    static String[][] compatMatrix;
    static ArrayList<String> variableList = new ArrayList<String>();
    static ArrayList<PredObj> predList = new ArrayList<PredObj>();
    static ArrayList<String> propList = new ArrayList<String>();
    static int depth;
    static ArrayList<ArrayList<String>> solutionList = new ArrayList<ArrayList<String>>();
    static String solutionString = "";
    static ArrayList<String> preProcessList = new ArrayList<String>();
    //static ArrayList<ArrayList<String>> solutionList = new ArrayList<ArrayList<String>>();

    public static void main(String[] args) throws IOException {
        if (args.length != 3) {
            System.err.println("Usage: java BnB <predAll.txt> <compat.csv> <depth>");
            System.exit(1);
        }
        String predFile = args[0];
        String compatFile = args[1];
        depth = Integer.parseInt(args[2]);
        
        readPredFile(predFile);
        readCompatFile(compatFile);
        printCompatFile();
        
        // Test
        getCompatValue("p5","p9");
        ArrayList<PredObj> testList = new ArrayList<PredObj>();
        PredObj p0 = new PredObj();
        p0.predVal = "p0";
        p0.predicate = "main.0.numRW16R = 0";
        testList.add(p0);
        PredObj p1 = new PredObj();
        p1.predVal = "p1";
        p1.predicate = "main.0.numB7A >= 0";
        testList.add(p1);
        PredObj p2 = new PredObj();
        p2.predVal = "p2";
        p2.predicate = "main.0.s >= AirplaneA.0.a";
        testList.add(p2);
        /*PredObj p3 = new PredObj();
        p3.predVal = "p3";
        p3.predicate = "main.0.s >= AirplaneA.1.a";
        testList.add(p3);*/
        System.out.println();
        System.out.println("Printing test list...");
        for (int i = 0; i < testList.size(); i++) {
            System.out.println(testList.get(i).predicate + ", " + testList.get(i).predVal);
        }
        computeVarCost(testList);
        computeCohesionCost(testList);
        ArrayList<String> tList = new ArrayList<String>();
        for (PredObj p : testList) {
            tList.add(p.predVal);
            System.out.println("Added " + p.predVal);
        }
        String[] permArr = tList.toArray(new String[testList.size()]);
        ArrayList<ArrayList<String>> cp = computePermutations(permArr, 0);
        System.out.println(cp);
        //System.out.println(test);
        System.out.println(solutionList);
    }
    
    public static ArrayList<ArrayList<String>> computePermutations(String[] pVal, int kDepth) {
        ArrayList<String> item = new ArrayList<String>();
        ArrayList<ArrayList<String>> result = new ArrayList<ArrayList<String>>();
        ArrayList<String> used = new ArrayList<String>();
        if (pVal.length == 0) {
            return result;
        }
        return helper(result, item, used, pVal, kDepth);
    }
    
    public static ArrayList<ArrayList<String>> helper(ArrayList<ArrayList<String>> result, ArrayList<String> item, 
        ArrayList<String> used, String[] pVal, int kDepth) {
        // base case: no more choices
        if (item.size() == pVal.length) {
            result.add(new ArrayList<String>(item));
            return result;
        }

        if (kDepth < depth) {
            // recursive case: choose each possible combination
            // use backtracking... before recursive call, add sth
            // after recursion, emove what has been added
            for (int i = 0; i < pVal.length; i++) {
                if (!used.contains(pVal[i])) {
                    item.add(pVal[i]);
                    used.add(pVal[i]);

                    /*solutionList.add(item);
                    System.out.println("ADDED: " + item);
                    System.out.println(solutionList);
                    System.out.println();*/
                    System.out.println("LIST: " + item);
                    for (String s : item) {
                        solutionString = solutionString + s + ";";
                    }
                    //System.out.println(solutionString);
                    preProcessList.add(solutionString);
                    if (!solutionList.contains(preProcessList)) {
                        solutionList.add(preProcessList);
                    }
                    solutionString = "";
                    helper(result, item, used, pVal, kDepth+1);
                    item.remove(item.size()-1);
                    used.remove(used.size()-1);
                }
            }
        }
        return result;
    }
    
    // numOfVars
    public static int computeVarCost(ArrayList<PredObj> solutionList) {
        int totalVarCost = 0;
        ArrayList<String> varList = new ArrayList<String>();
        String v1 = "";
        String v2 = "";

        for (PredObj p : solutionList) {
            int endIndex = p.predicate.indexOf(" ");
            v1 = p.predicate.substring(0, endIndex);
            if (!v1.trim().equals("0")) {
                if (!varList.contains(v1)) {
                    System.out.println("v1: " + v1.trim());
                    varList.add(v1.trim());
                }
            }
            int startIndex = p.predicate.indexOf("=");
            v2 = p.predicate.substring(startIndex+1, p.predicate.length());
            if (!v2.trim().equals("0")) {
                if (!varList.contains(v2)) {
                    System.out.println("v2: " + v2.trim());
                    varList.add(v2.trim());
                }
            }

        }
        totalVarCost = varList.size();
        System.out.println("Total Var Cost: " + totalVarCost);
        System.out.println(varList);
        return totalVarCost;
    }
    
    public static int computeCohesionCost(ArrayList<PredObj> solutionList) {
        int totalCohesionCost = 0;
        int cv = 0;
        for (int i = 0; i < solutionList.size(); i++) {
            for (int j = 0; j < solutionList.size(); j++) {
                if (i != j && j > i) {
                    cv = getCompatValue(solutionList.get(i).predVal, solutionList.get(j).predVal);
                    totalCohesionCost = totalCohesionCost + cv;
                }
            }
        }
        System.out.println("Total Cohesion Cost: " + totalCohesionCost);
        return totalCohesionCost;
    }
    
    public static void readPredFile(String fileName) {
        PredObj pObj = new PredObj();
        int i = 0;
        try {
            FileReader fileReader = new FileReader(fileName);
            BufferedReader bufferedReader = new BufferedReader(fileReader);
            String currentLine = "";
            // For variable list
            while ((currentLine = bufferedReader.readLine()) != null) {
                if (currentLine.trim().equals("preds:")) {
                    break;
                }
                else {
                    //System.out.println(currentLine);
                    if (!currentLine.trim().equals("vars:")) {
                        variableList.add(currentLine);
                        System.out.println("Adding to variable list... " + currentLine);
                    }
                }
            }
            // For pred list
            while ((currentLine = bufferedReader.readLine()) != null) {
                if (currentLine.trim().equals("prop:")) {
                    break;
                }
                else {
                    pObj.predicate = currentLine;
                    pObj.predVal = "p" + i;
                    predList.add(pObj);
                    System.out.println("Adding to pred list... " + pObj.predicate + "\t" + pObj.predVal);
                    i++;
                }
            }
           // For prop list
            while ((currentLine = bufferedReader.readLine()) != null) {
                propList.add(currentLine);
                System.out.println("Adding to prop list... " + currentLine);
            }
            bufferedReader.close();
        }
        catch (Exception e) {
            System.out.println(e);
        }
    }
    
    public static void readCompatFile(String fileName) throws IOException, FileNotFoundException {
        CSVReader csvReader = new CSVReader(new FileReader(fileName));
        List<String[]> compatList = csvReader.readAll();
        compatMatrix = new String[compatList.size()][compatList.size()];
        compatMatrix = compatList.toArray(compatMatrix);
    }
    
    public static void printCompatFile() {
        for (int i = 0; i < compatMatrix.length; i++) {
            for (int j = 0; j < compatMatrix.length; j++) {
                System.out.print(compatMatrix[i][j] + "\t");
            }
            System.out.println();
        }
    }
    
    public static int getCompatValue(String predValRow, String predValCol) {
        int compatVal = 0;
        for (int i = 0; i < compatMatrix.length; i++) {
            for (int j = 0; j < compatMatrix.length; j++) {
                if (compatMatrix[0][j].equals(predValRow) && compatMatrix[i][0].equals(predValCol)) {
                    System.out.println("FOUND VALUE FOR: " + predValRow + "," + predValCol + " : " + compatMatrix[i][j] + "\t");
                    compatVal = Integer.parseInt(compatMatrix[i][j]);
                }
            }
        }
        return compatVal;
    }
    
}
