import com.opencsv.*;
import java.io.BufferedReader;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

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
    static ArrayList<ArrayList<PredObj>> solutionListForLevel = new ArrayList<ArrayList<PredObj>>();
    static HashMap<ArrayList<PredObj>,ArrayList<Integer>> solutionCostMap = new HashMap<ArrayList<PredObj>,ArrayList<Integer>>();
    static ArrayList<PredObj> bestSolutionSet = new ArrayList<PredObj>();
    static ArrayList<String> bestSolutionVarList = new ArrayList<String>();

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
        
        /*for (PredObj p : predList) {
            System.out.println("PRED LIST: " + p.predVal + "\t" + p.predicate);
        }*/
        
        /*ArrayList<String> sList = new ArrayList<String>();
        for (PredObj p : predList) {
            sList.add(p.predVal);
            System.out.println("Added " + p.predVal);
        }
        String[] permArr = sList.toArray(new String[predList.size()]);
        ArrayList<ArrayList<String>> cp = computePermutations(permArr);
        System.out.println("All permutations: " + cp);*/
        
        computeSolutionSets(predList, 0);
        printSolutionListAtDepth();
        //System.out.println("SOLUTION LIST: " + solutionListForLevel);
        computeSolutionSetCost();
        HashMap<ArrayList<PredObj>,ArrayList<Integer>> bestSoln = getBestSolution();
        System.out.println(bestSoln);
        printBestSolution(bestSoln);
        System.out.println(bestSolutionVarList);
        writeToOutputFile(bestSolutionSet, bestSolutionVarList, propList);
        
        // Test
        /*getCompatValue("p5","p9");
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
        /*System.out.println();
        System.out.println("Printing test list...");
        for (int i = 0; i < testList.size(); i++) {
            System.out.println(testList.get(i).predicate + ", " + testList.get(i).predVal);
        }
        //computeVarCost(testList);
        //computeCohesionCost(testList);
        
        ArrayList<String> tList = new ArrayList<String>();
        for (PredObj p : testList) {
            tList.add(p.predVal);
            //System.out.println("Added " + p.predVal);
        }
        String[] permArr = tList.toArray(new String[testList.size()]);
        ArrayList<ArrayList<String>> cp = computePermutations(permArr);
        System.out.println("All permutations: " + cp);
        
        computeSolutionSets(testList, 0);
        printSolutionListAtDepth();
        //System.out.println("SOLUTION LIST: " + solutionListForLevel);
        computeSolutionSetCost();
        HashMap<ArrayList<PredObj>,ArrayList<Integer>> bestSoln = getBestSolution();
        System.out.println(bestSoln);
        printBestSolution(bestSoln);
        System.out.println(bestSolutionVarList);
        writeToOutputFile(bestSolutionSet, bestSolutionVarList, propList);*/
    }
    
    public static ArrayList<PredObj> computeSolutionSets(ArrayList<PredObj> pValList, int kDepth) {
        ArrayList<PredObj> item = new ArrayList<PredObj>();
        ArrayList<PredObj> result = new ArrayList<PredObj>();
        ArrayList<PredObj> used = new ArrayList<PredObj>();
        if (pValList.isEmpty()) {
            return result;
        }
        return helperForComputeSolutionSets(result, item, used, pValList, kDepth);
    }
    
    public static ArrayList<PredObj> helperForComputeSolutionSets(ArrayList<PredObj> result, ArrayList<PredObj> item, 
        ArrayList<PredObj> used, ArrayList<PredObj> pValList, int kDepth) {
        // base case: no more choices
        if (item.size() == pValList.size()) {
            //result.add(new ArrayList<PredObj>(item));
            return result;
        }

        if (kDepth < depth) {
            // recursive case: choose each possible combination
            // use backtracking... before recursive call, add sth
            // after recursion, remove what has been added
            for (int i = 0; i < pValList.size(); i++) {
                if (!used.contains(pValList.get(i))) {
                    item.add(pValList.get(i));
                    used.add(pValList.get(i));

                    ArrayList<PredObj> tempList = new ArrayList<PredObj>(item);
                    solutionListForLevel.add(tempList);
                    //System.out.println("LIST: " + tempList);

                    helperForComputeSolutionSets(result, item, used, pValList, kDepth+1);
                    item.remove(item.size()-1);
                    used.remove(used.size()-1);
                }
            }
        }
        return result;
    }
    
    public static void printSolutionListAtDepth() {
        System.out.println("Printing solution list at depth " + depth + ":");
        for (ArrayList<PredObj> pList : solutionListForLevel) {
            //System.out.println(pList);
            for (PredObj p : pList) {
                System.out.print(p.predVal + " ");
            }
            System.out.println();
        }
    }
    
    public static void printBestSolution(HashMap<ArrayList<PredObj>,ArrayList<Integer>> bestSoln) {
        System.out.println("Printing best solution...");
        for (Map.Entry<ArrayList<PredObj>, ArrayList<Integer>> entry : bestSoln.entrySet()) {
            ArrayList<PredObj> keyList = entry.getKey();
            ArrayList<Integer> valList = entry.getValue();
            bestSolutionVarList = getVars(keyList);
            bestSolutionSet = keyList;
            for (PredObj p : keyList) {
                System.out.print(p.predVal + " ");
            }
            System.out.println("VarCost: " + valList.get(0) + " CohesionCost: " + valList.get(1));
        }
    }
    
    public static ArrayList<ArrayList<String>> computePermutations(String[] pVal) {
        ArrayList<String> item = new ArrayList<String>();
        ArrayList<ArrayList<String>> result = new ArrayList<ArrayList<String>>();
        ArrayList<String> used = new ArrayList<String>();
        if (pVal.length == 0) {
            return result;
        }
        return helperForComputePermutations(result, item, used, pVal);
    }
    
    public static ArrayList<ArrayList<String>> helperForComputePermutations(ArrayList<ArrayList<String>> result, ArrayList<String> item, 
        ArrayList<String> used, String[] pVal) {
        // base case: no more choices
        if (item.size() == pVal.length) {
            result.add(new ArrayList<String>(item));
            return result;
        }
        
        // recursive case: choose each possible combination
        // use backtracking... before recursive call, add sth
        // after recursion, remove what has been added
        for (int i = 0; i < pVal.length; i++) {
            if (!used.contains(pVal[i])) {
                item.add(pVal[i]);
                used.add(pVal[i]);
                helperForComputePermutations(result, item, used, pVal);
                item.remove(item.size()-1);
                used.remove(used.size()-1);
            }
        }
        return result;
    }
    
    public static void computeSolutionSetCost() {
        // for each solution set, compute cost and store in hashmap
        for (ArrayList<PredObj> pList : solutionListForLevel) {
            //System.out.println(pList);
            //for (PredObj p : pList) {
                //System.out.print(p.predVal + " ");
            ArrayList<Integer> varAndCohesionCost = new ArrayList<Integer>();
            int totalVarCost = computeVarCost(pList);
            int totalCohesionCost = computeCohesionCost(pList);
            varAndCohesionCost.add(totalVarCost);
            varAndCohesionCost.add(totalCohesionCost);
            solutionCostMap.put(pList, varAndCohesionCost);
            //System.out.println(pList + "\t" + totalVarCost + "\t" + totalCohesionCost);
            //}
            //System.out.println();
        }
    }
    
    public static HashMap<ArrayList<PredObj>,ArrayList<Integer>> getBestSolution() {
        HashMap<ArrayList<PredObj>,ArrayList<Integer>> tempSol = new HashMap<ArrayList<PredObj>,ArrayList<Integer>>();
        int maxVarCost = 0;
        //int maxCohesionCost = 0;
        for (Map.Entry<ArrayList<PredObj>, ArrayList<Integer>> entry : solutionCostMap.entrySet()) {
            ArrayList<PredObj> keyList = entry.getKey();
            ArrayList<Integer> valList = entry.getValue();
            //for (Integer val : valList) {
                //System.out.println("Key: " + keyList + " Value: " + val);
            //}
            int totalVarCost = valList.get(0);
            int totalCohesionCost = valList.get(1);
            for (PredObj k : keyList) {
                System.out.print(k.predVal + " ");
            }
            System.out.println("\t \t TotalVarCost: " + totalVarCost + " TotalCohesionCost: " + totalCohesionCost);
            if (totalVarCost > maxVarCost) {
                maxVarCost = totalVarCost;
                tempSol.clear();
                tempSol.put(keyList, valList);
            }
            else if (totalVarCost == maxVarCost) {
                for (Map.Entry<ArrayList<PredObj>, ArrayList<Integer>> existingEntry : tempSol.entrySet()) {
                    ArrayList<Integer> existingValList = existingEntry.getValue();
                    int existingTotalCohesionCost = existingValList.get(1);
                    if (totalCohesionCost > existingTotalCohesionCost) {
                        tempSol.clear();
                        tempSol.put(keyList, valList);
                    }
                    else {
                        break;
                    }
                }
            }
        }
        return tempSol;
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
                if (!varList.contains(v1.trim())) {
                    System.out.println("v1: " + v1.trim());
                    varList.add(v1.trim());
                }
            }
	    int startIndex = 0;
	    if (p.predicate.contains("=")) {
		startIndex = p.predicate.indexOf("=");
	    }
	    else if (!p.predicate.contains("=")) {
		if (p.predicate.contains("<")) {
		    startIndex = p.predicate.indexOf("<");
		}
		else if (p.predicate.contains(">")) {
		    startIndex = p.predicate.indexOf(">");
		}
	    }
            v2 = p.predicate.substring(startIndex+1, p.predicate.length());
            if (!v2.trim().equals("0")) {
                if (!varList.contains(v2.trim())) {
                    System.out.println("v2: " + v2.trim());
                    varList.add(v2.trim());
                }
            }

        }
        totalVarCost = varList.size();
        System.out.println("@@@Total Var Cost: " + totalVarCost);
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
                        variableList.add(currentLine.trim());
                        System.out.println("Adding to variable list... " + currentLine.trim());
                    }
                }
            }
            // For pred list
            while ((currentLine = bufferedReader.readLine()) != null) {
                if (currentLine.trim().equals("prop:")) {
                    break;
                }
                else {
                    pObj.predicate = currentLine.trim();
                    pObj.predVal = "p" + i;
                    //ArrayList<PredObj> tempList = new ArrayList<PredObj>(item);
                    predList.add(new PredObj(pObj.predicate, pObj.predVal));
                    System.out.println("Adding to pred list... " + pObj.predicate + "\t" + pObj.predVal);
                    //System.out.println(predList);
                    i++;
                }
            }
           // For prop list
            while ((currentLine = bufferedReader.readLine()) != null) {
                propList.add(currentLine.trim());
                System.out.println("Adding to prop list... " + currentLine.trim());
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
    
    public static ArrayList<String> getVars(ArrayList<PredObj> predObjList) {
        ArrayList<String> varList = new ArrayList<String>();
        String v1 = "";
        String v2 = "";

        for (PredObj p : predObjList) {
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
        return varList;
    }
    
    public static void writeToOutputFile(ArrayList<PredObj> predObjList, ArrayList<String> varList, ArrayList<String> propPreds) throws IOException {
        System.out.println();
        System.out.println("Writing to output.txt...");
        FileWriter writer = new FileWriter("output_k_"+depth+".txt");
        //writer.append("{"+solSet+"}\n");
        String best = "";
        for (PredObj pVal : predObjList) {
            best = best + pVal.predVal + ",";
        }
        best = best.substring(0,best.length()-1);
        writer.append("{"+best+"}");
        writer.append("\n");
        writer.append("vars:\n");
        for (String v : varList) {
            writer.append(v + "\n");
        }
        writer.append("preds:\n");
        for (PredObj p : predObjList) {
            writer.append(p.predicate + "\n");
        }
        if (!propPreds.isEmpty()) {
            writer.append("prop preds:\n");
            for (String prop : propPreds) {
                writer.append(prop+"\n");
            }
        }
        writer.close();
    }
    
}
