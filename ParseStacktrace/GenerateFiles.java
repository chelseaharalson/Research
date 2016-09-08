import java.io.*;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 *
 * @author chelseametcalf
 */
public class GenerateFiles {
    
    static ArrayList<String> entryClassList = new ArrayList<String>();
    static int targetNumber = 0;
    //static ArrayList<ArrayList<String>> targetInfo = new ArrayList<ArrayList<String>>();
    //static HashMap<Integer, ArrayList<String>> targetInfo = new HashMap<Integer, ArrayList<String>>();
    //static ArrayList<String> encInfo = new ArrayList<String>();

    public static void main(String[] args) throws IOException {
        
        if (args.length != 2) {
            System.err.println("Usage: java GenerateRunFiles <project name> <version number>");
            System.exit(1);
        }
        String projectName = args[0];
        String versionNumber = args[1];

        generateScopeFileLinux(projectName, versionNumber);
        
        readFile("stacktrace.txt");
        
        String entryClassString = String.join(";", entryClassList);
        System.out.println(entryClassString);
        
        generateRunFileLinux(projectName, entryClassString);
        
        getRelevantStackTraceLines(projectName, "stacktrace.txt");
        
    }
    
    public static void readFile(String fileName) {
        String line = "";
        String waiting = "waiting to lock <";
        String locked = "locked <";
        try {
            FileReader fileReader = new FileReader(fileName);
            BufferedReader bufferedReader = new BufferedReader(fileReader);
            while ((line = bufferedReader.readLine()) != null) {
                //System.out.println(line);
                parseEntryClasses(line);
                //parseFilterEnclosing(line);
                //parseFilterEnclosed(line);
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
        String folder = "/Users/chelseametcalf/Dropbox/Documents/Research/AliasedLockOrder/" + projectName + "/";
        FileWriter writer = new FileWriter(folder + "run-linux2.txt");
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
        String folder = "/Users/chelseametcalf/Dropbox/Documents/Research/AliasedLockOrder/" + projectName + "/";
        FileWriter writer = new FileWriter(folder + "scope2.txt");
        writer.append(scope);
        writer.close();
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
                        System.out.println("Adding " + currentLine + " to encInfo");
                        encInfo.add(currentLine.trim());
                        i++;
                        if (currentLine.trim().contains("locked")) {
                            System.out.println("ENC INFO: " + encInfo);
                            int lineAboveLockedLine = 0;
                            for (int j = 0; j < encInfo.size(); j++) {
                            //for (String sLine : encInfo) {
                                //System.out.println("@@@@@@ " + s);
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
                                    System.out.println("*********" + lineAboveLockedLine);
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
            //System.out.println(targetInfo);
        }
        catch (Exception e) {
            System.out.println(e);
        }
    }
    
    public static void generateTarget(String projectName, String enclosedClass, String enclosedMethodThatCallsMethod, String enclosedMethod, String enclosedLockType, 
            String enclosingClass, String enclosingMethod, String enclosingLockType) throws IOException {
            String filterEnclosing = "";
            String filterEnclosed = "";
            int enclosingLineNum = 0;
            int enclosedLineNum = 0;

            if (!enclosingClass.equals(enclosingLockType)) {
                enclosingMethod = "monitorenter";
                //enclosingLineNum = findEnclosingLineNum();
                filterEnclosing = "filterEnclosing=" + enclosingClass + ";" + enclosingMethod + ";" + enclosingLineNum + ";" + enclosingLockType;
            }
            else {
                filterEnclosing = "filterEnclosing=" + enclosingClass + ";" + enclosingMethod + ";" + enclosingLineNum + ";" + enclosingLockType;
            }
            
            // enclosedLineNum = findEnclosedLineNum();
            filterEnclosed = "filterEnclosed=" + enclosedClass + ";" + enclosedMethodThatCallsMethod + ";" + enclosedMethod + ";" + enclosedLineNum + ";" + enclosedLockType;
             
            String target = "//Two options for filterEnclosing:\n" + 
                "//1) classname;method that grabs the enclosing lock; 0 (as line no); lock type\n" + 
                "//2) file name (e.g. A.java); monitorenter; line no; lock type\n" + 
                filterEnclosing + "\n" + 
                "//classname;method that calls the enclosed locking instruction; enclosed locking instruction (methodname or monitorenter); line number in that method; line  no; lock type\n" + 
                filterEnclosed;
            System.out.println(target);

            String folder = "/Users/chelseametcalf/Dropbox/Documents/Research/AliasedLockOrder/" + projectName + "/";
            targetNumber++;
            String targetName = "target" + targetNumber + ".txt";
            FileWriter writer = new FileWriter(folder + targetName);
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
                lockType = "L" + s;
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
                lockType = "L" + s;
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
    
    /*public static void parseFilterEnclosedAndEnclosing(String fileName) {
        ArrayList<String> encInfo = new ArrayList<String>();
        try {
            FileReader fileReader = new FileReader(fileName);
            BufferedReader bufferedReader = new BufferedReader(fileReader);
            String line = "";
            while ((line = bufferedReader.readLine()) != null) {
                //Two options for filterEnclosing:
                //1) classname;method that grabs the enclosing lock; 0 (as line no); lock type
                //2) file name (e.g. A.java); monitorenter; line no; lock type
                /*String enclosingClass = "";
                String enclosingMethod = "";
                String enclosingLockType = "";
                String enclosingLineNum = "";
                
                //classname;method that calls the enclosed locking instruction; enclosed locking instruction (methodname or monitorenter); 
                //line number in that method; line  no; lock type
                String enclosedClass = "";
                String enclosedMethodThatCallsLockingInstr = "";
                String enclosedLockingInstr = "";
                String enclosedLockType = "";
                String enclosedLineNum = "";*/
                
                /*String method = "";
                String enclosedLockType = "";
                String enclosingLockType = "";
                String enclosedClass = "";
                String enclosingClass = "";
                if (line.trim().startsWith("at")) {
                    Pattern p = Pattern.compile("([\\s\\n\\r]*[\\w]+)[\\s\\n\\r]*(?=\\(.*\\))");
                    Matcher m = p.matcher(line);
                    while (m.find()) {
                        //System.out.println("@@@: " + m.group());
                        method = m.group().trim();
                        System.out.println("METHODS: " + method);
                        encInfo.add(method);
                    }
                    //break;
                }
                if (line.trim().startsWith("- waiting to lock")) {
                    Pattern p = Pattern.compile("\\(([^)]+)\\)");
                    Matcher m = p.matcher(line);
                    while (m.find()) {
                        //System.out.println("@@@@@@@@: " + m.group());
                        String a = m.group().replace("(a ", "").trim();
                        String b = a.replace(")", "");
                        String s = b.replace(".", "/");
                        enclosedLockType = "L" + s;
                        System.out.println("ENCLOSED LOCK TYPE: " + enclosedLockType);
                        encInfo.add(enclosedLockType);
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
                        enclosingLockType = "L" + s;
                        System.out.println("ENCLOSING LOCK TYPE: " + enclosingLockType);
                        encInfo.add(enclosingLockType);
                    }
                    System.out.println(encInfo);
                    break;
                }
            }
            bufferedReader.close();
        }
        catch (Exception e) {
            System.out.println(e);
        }
        
    }*/
    
    /*public static void parseFilterEnclosedAndEnclosing(String fileName) {
        try {
            FileReader fileReader = new FileReader(fileName);
            BufferedReader bufferedReader = new BufferedReader(fileReader);
            String line = "";
            while ((line = bufferedReader.readLine()) != null) {
                //Two options for filterEnclosing:
                //1) classname;method that grabs the enclosing lock; 0 (as line no); lock type
                //2) file name (e.g. A.java); monitorenter; line no; lock type
                String enclosingClass = "";
                String enclosingMethod = "";
                String enclosingLockType = "";
                String enclosingLineNum = "";
                
                //classname;method that calls the enclosed locking instruction; enclosed locking instruction (methodname or monitorenter); 
                //line number in that method; line  no; lock type
                String enclosedClass = "";
                String enclosedMethodThatCallsLockingInstr = "";
                String enclosedLockingInstr = "";
                String enclosedLockType = "";
                String enclosedLineNum = "";
                if (line.trim().startsWith("at")) {
                    Pattern p = Pattern.compile("([\\s\\n\\r]*[\\w]+)[\\s\\n\\r]*(?=\\(.*\\))");
                    Matcher m = p.matcher(line);
                    while (m.find()) {
                        //System.out.println("@@@: " + m.group());
                        enclosedLockingInstr = m.group().trim();
                        System.out.println("ENCLOSED LOCKING INSTRUCTION: " + enclosedLockingInstr);
                    }
                    //break;
                }
                if (line.trim().startsWith("- waiting to lock")) {
                    Pattern p = Pattern.compile("\\(([^)]+)\\)");
                    Matcher m = p.matcher(line);
                    while (m.find()) {
                        //System.out.println("@@@@@@@@: " + m.group());
                        String a = m.group().replace("(a ", "").trim();
                        String b = a.replace(")", "");
                        String s = b.replace(".", "/");
                        enclosedLockType = "L" + s;
                        System.out.println("ENCLOSED LOCK TYPE: " + enclosedLockType);
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
                        enclosingLockType = "L" + s;
                        System.out.println("ENCLOSING LOCK TYPE: " + enclosingLockType);
                    }
                    break;
                }
            }
            bufferedReader.close();
        }
        catch (Exception e) {
            System.out.println(e);
        }
        
    }*/
    
}
