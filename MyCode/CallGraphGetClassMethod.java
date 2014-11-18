package MyCode;
import java.io.File;
import java.io.IOException;
import java.util.jar.JarFile;

import com.ibm.wala.classLoader.IClass;
import com.ibm.wala.classLoader.IMethod;
import com.ibm.wala.ipa.callgraph.AnalysisScope;
import com.ibm.wala.ipa.cha.ClassHierarchy;
import com.ibm.wala.ipa.cha.ClassHierarchyException;
import com.ibm.wala.ipa.cha.IClassHierarchy;
import com.ibm.wala.util.config.AnalysisScopeReader;
import com.ibm.wala.util.io.FileProvider;
 
 
public class CallGraphGetClassMethod {
	public static void main(String args[]) throws IOException, ClassHierarchyException 
	{
			File exFile=new FileProvider().getFile("Java60RegressionExclusions.txt");
			System.out.println(exFile.getAbsolutePath());
	    //File exFile = null;
			AnalysisScope scope = AnalysisScopeReader.makeJavaBinaryAnalysisScope("/home/chelseametcalf/workspace/hadoop-0.18.1-core.jar",exFile);
			//AnalysisScope scope = AnalysisScopeReader.makeJavaBinaryAnalysisScope("/home/chelseametcalf/workspace/Test.jar",exFile);
			IClassHierarchy cha = ClassHierarchy.make(scope);
			for (IClass c : cha) {
			  if (!scope.isApplicationLoader(c.getClassLoader())) continue;
				String cname = c.getName().toString();
				if (cname.indexOf("Lorg/apache/hadoop/mapred/ReduceTask") == -1 
	          || cname.indexOf("Lorg/apache/hadoop/mapred/ReduceTaskStatus") > -1) continue;    // continue = skip
				System.out.println("Class:" + cname);
				for (IMethod m : c.getAllMethods()) {
					String mname = m.getName().toString();
					System.out.println("  method:" + mname);
				}
				System.out.println();
			}
	}
}