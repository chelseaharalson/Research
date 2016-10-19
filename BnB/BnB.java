import com.opencsv.*;
import java.io.BufferedReader;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

/**
 *
 * @author chelseametcalf
 */
public class BnB {
    
    static String[][] compatMatrix;
    static ArrayList<String> variableList = new ArrayList<String>();
    //static ArrayList<String> predList = new ArrayList<String>();
    static ArrayList<PredObj> predList = new ArrayList<PredObj>();
    static ArrayList<String> propList = new ArrayList<String>();

    public static void main(String[] args) throws IOException {
        if (args.length != 3) {
            System.err.println("Usage: java BnB <predAll.txt> <compat.csv> <depth>");
            System.exit(1);
        }
        String predFile = args[0];
        String compatFile = args[1];
        int depth = Integer.parseInt(args[2]);
        
        readPredFile(predFile);
        readCompatFile(compatFile);
        printCompatFile();
        // Test
        getCompatValue("p10","p5");
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
                    System.out.print("FOUND VALUE: " + compatMatrix[i][j] + "\t");
                    compatVal = Integer.parseInt(compatMatrix[i][j]);
                }
            }
        }
        return compatVal;
    }
    
}
