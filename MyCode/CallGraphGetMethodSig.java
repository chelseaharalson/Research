package MyCode;

import com.ibm.wala.ipa.cha.ClassHierarchy; 
import com.ibm.wala.ipa.cha.IClassHierarchy; 
import com.ibm.wala.classLoader.IClass; 
import com.ibm.wala.classLoader.IMethod; 
import com.ibm.wala.ipa.callgraph.AnalysisOptions; 
import com.ibm.wala.ipa.callgraph.AnalysisScope; 
import com.ibm.wala.types.ClassLoaderReference; 
import java.util.jar.JarFile; 
import java.io.IOException; 
import com.ibm.wala.ipa.cha.ClassHierarchyException; 

public class CallGraphGetMethodSig { 
    public static void main(String[] args) throws IOException, ClassHierarchyException { 
        AnalysisScope scope = AnalysisScope.createJavaAnalysisScope(); 
        scope.addToScope(ClassLoaderReference.Primordial, new JarFile("/home/chelseametcalf/workspace/jsdg-stubs-jre1.5.jar")); 
        //scope.addToScope(ClassLoaderReference.Application, new JarFile("/home/chelseametcalf/workspace/hadoop-0.18.1-core.jar")); 
        scope.addToScope(ClassLoaderReference.Application, new JarFile("/home/chelseametcalf/workspace/Test.jar"));
        IClassHierarchy cha = ClassHierarchy.make(scope); 

        for (IClass cl : cha) { 
            if (cl.getClassLoader().getReference().equals(ClassLoaderReference.Application)) { 
                for (IMethod m : cl.getAllMethods()) { 
                    String ac = ""; 
                    if (m.isAbstract()) ac = ac + "abstract "; 
                    if (m.isClinit()) ac = ac + "clinit "; 
                    if (m.isFinal()) ac = ac + "final ";  
                    if (m.isInit()) ac = ac + "init ";  
                    if (m.isNative()) ac = ac + "native ";  
                    if (m.isPrivate()) ac = ac + "private "; 
                    if (m.isProtected()) ac = ac + "protected ";  
                    if (m.isPublic()) ac = ac + "public ";  
                    if (m.isSynchronized()) ac = ac + "synchronized ";  
                    System.out.println(ac + m.getSignature());
                } 
            } 
        } 
    } 
} 