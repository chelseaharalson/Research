/*******************************************************************************
 * Copyright (c) 2002 - 2006 IBM Corporation.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     IBM Corporation - initial API and implementation
 *******************************************************************************/
package MyCode;

import java.io.File;
import java.io.IOException;
import java.util.Collection;
import java.util.Iterator;
import java.util.Properties;

import com.ibm.wala.classLoader.IMethod;
import com.ibm.wala.core.tests.callGraph.CallGraphTestUtil;
import com.ibm.wala.examples.drivers.PDFTypeHierarchy;
import com.ibm.wala.examples.properties.WalaExamplesProperties;
import com.ibm.wala.ipa.callgraph.AnalysisCache;
import com.ibm.wala.ipa.callgraph.AnalysisOptions;
import com.ibm.wala.ipa.callgraph.AnalysisScope;
import com.ibm.wala.ipa.callgraph.CGNode;
import com.ibm.wala.ipa.callgraph.CallGraph;
import com.ibm.wala.ipa.callgraph.CallGraphStats;
import com.ibm.wala.ipa.callgraph.Entrypoint;
import com.ibm.wala.ipa.callgraph.impl.Everywhere;
import com.ibm.wala.ipa.callgraph.impl.Util;
import com.ibm.wala.ipa.callgraph.propagation.LocalPointerKey;
import com.ibm.wala.ipa.cha.ClassHierarchy;
import com.ibm.wala.properties.WalaProperties;
import com.ibm.wala.types.ClassLoaderReference;
import com.ibm.wala.types.MethodReference;
import com.ibm.wala.util.CancelException;
import com.ibm.wala.util.WalaException;
import com.ibm.wala.util.collections.Filter;
import com.ibm.wala.util.collections.HashSetFactory;
import com.ibm.wala.util.config.AnalysisScopeReader;
import com.ibm.wala.util.debug.Assertions;
import com.ibm.wala.util.graph.Acyclic;
import com.ibm.wala.util.graph.Graph;
import com.ibm.wala.util.intset.IBinaryNaturalRelation;
import com.ibm.wala.util.intset.IntPair;
import com.ibm.wala.util.io.CommandLine;
import com.ibm.wala.util.io.FileProvider;
import com.ibm.wala.util.io.FileUtil;
import com.ibm.wala.util.strings.StringStuff;
import com.ibm.wala.viz.DotUtil;
import com.ibm.wala.viz.PDFViewUtil;
import com.ibm.wala.ssa.IR;
import com.ibm.wala.ssa.ISSABasicBlock;
import com.ibm.wala.ssa.SSACFG;
import com.ibm.wala.ssa.SSACFG.BasicBlock;
import com.ibm.wala.ssa.SSAInstruction;

/**
 * This simple example WALA application builds a call graph and fires off ghostview to visualize a DOT representation.
 */
public class Test_PDFCallGraph {
  public static boolean isDirectory(String appJar) {
    return (new File(appJar).isDirectory());
  }

  public static String findJarFiles(String[] directories) throws WalaException {
    Collection<String> result = HashSetFactory.make();
    for (int i = 0; i < directories.length; i++) {
      for (Iterator<File> it = FileUtil.listFiles(directories[i], ".*\\.jar", true).iterator(); it.hasNext();) {
        File f = (File) it.next();
        result.add(f.getAbsolutePath());
      }
    }
    return composeString(result);
  }
  
  private static String composeString(Collection<String> s) {
    StringBuffer result = new StringBuffer();
    Iterator<String> it = s.iterator();
    for (int i = 0; i < s.size() - 1; i++) {
      result.append(it.next());
      result.append(File.pathSeparator);
    }
    if (it.hasNext()) {
      result.append(it.next());
    }
    return result.toString();
  }  
  
  private final static String PDF_FILE = "cg.pdf";

  /**
   * Usage: args = "-appJar [jar file name] {-exclusionFile [exclusionFileName]}" The "jar file name" should be something like
   * "c:/temp/testdata/java_cup.jar"
   * 
   * @throws CancelException
   * @throws IllegalArgumentException
   */
  public static void main(String[] args) throws WalaException, IllegalArgumentException, CancelException {
    run(args);
  }

  /**
   * Usage: args = "-appJar [jar file name] {-exclusionFile [exclusionFileName]}" The "jar file name" should be something like
   * "c:/temp/testdata/java_cup.jar"
   * 
   * @throws CancelException
   * @throws IllegalArgumentException
   */
  public static Process run(String[] args) throws WalaException, IllegalArgumentException, CancelException {
    Properties p = CommandLine.parse(args);
    validateCommandLine(p);
    return run(p.getProperty("appJar"), p.getProperty("exclusionFile", CallGraphTestUtil.REGRESSION_EXCLUSIONS));
  }

  /**
   * @param appJar something like "c:/temp/testdata/java_cup.jar"
   * @throws CancelException
   * @throws IllegalArgumentException
   */
  public static Process run(String appJar, String exclusionFile) throws IllegalArgumentException, CancelException {
    try {
      Graph<CGNode> g = buildPrunedCallGraph(appJar, (new FileProvider()).getFile(exclusionFile));
      //System.out.println("APP JAR !!!!!!!!!!!!!!!!!!: " + appJar);
      Properties p = null;
      try {
        p = WalaExamplesProperties.loadProperties();
        p.putAll(WalaProperties.loadProperties());
      } catch (WalaException e) {
        e.printStackTrace();
        Assertions.UNREACHABLE();
      }
      /*
      String pdfFile = p.getProperty(WalaProperties.OUTPUT_DIR) + File.separatorChar + PDF_FILE;

      String dotExe = p.getProperty(WalaExamplesProperties.DOT_EXE);
      DotUtil.dotify(g, null, PDFTypeHierarchy.DOT_FILE, pdfFile, dotExe);

      String gvExe = p.getProperty(WalaExamplesProperties.PDFVIEW_EXE);
      return PDFViewUtil.launchPDFView(pdfFile, gvExe);
      */
      return null;
    } catch (WalaException e) {
      e.printStackTrace();
      return null;
    } catch (IOException e) {
      e.printStackTrace();
      return null;
    }
  }

  /**
   * @param appJar something like "c:/temp/testdata/java_cup.jar"
   * @return a call graph
   * @throws CancelException
   * @throws IllegalArgumentException
   * @throws IOException 
   */
  public static Graph<CGNode> buildPrunedCallGraph(String appJar, File exclusionFile) throws WalaException,
      IllegalArgumentException, CancelException, IOException {
    AnalysisScope scope = AnalysisScopeReader.makeJavaBinaryAnalysisScope(appJar, exclusionFile != null ? exclusionFile : new File(
        CallGraphTestUtil.REGRESSION_EXCLUSIONS));

    ClassHierarchy cha = ClassHierarchy.make(scope);

    Iterable<Entrypoint> entrypoints = com.ibm.wala.ipa.callgraph.impl.Util.makeMainEntrypoints(scope, cha);
    AnalysisOptions options = new AnalysisOptions(scope, entrypoints);

    // //
    // build the call graph
    // //
    com.ibm.wala.ipa.callgraph.CallGraphBuilder builder = Util.makeZeroCFABuilder(options, new AnalysisCache(), cha, scope);
    CallGraph cg = builder.makeCallGraph(options, null);

    System.err.println(CallGraphStats.getStats(cg));
    IBinaryNaturalRelation backEdges = Acyclic.computeBackEdges(cg, cg.getFakeRootNode());
    //System.out.println(backEdges.hashCode());
    
    int num = 0;
    //int hashSum = 0;
    for(IntPair pair : backEdges){
      num++;
      //hashSum += pair.hashCode();
    }
    
    System.out.println("Totally " + num + " back edges;"); 
    //System.out.println("hash value: " + hashSum);
    
    // Code to go iterate through call graph
    for (CGNode node: cg)
    {
      String methodSig = "java.lang.StringBuffer.append(Ljava/lang/String;)Ljava/lang/StringBuffer";
      
      MethodReference mr = StringStuff.makeMethodReference(methodSig);

      IMethod m = cha.resolveMethod(mr);
      AnalysisCache cache = new AnalysisCache();
      // Get the IR of a CGNode
      //IR ir = node.getIR();
      //System.out.println(ir.toString());
      //System.out.println(ir.);
      //System.out.println(cg.getClass());
      IR ir = cache.getSSACache().findOrCreateIR(m, Everywhere.EVERYWHERE, options.getSSAOptions());
      //System.out.println("Chelsea: " + ir.getLocalNames(1, 1));

      // Get CFG from IR
      SSACFG cfg = ir.getControlFlowGraph();

      // Iterate over the Basic Blocks of CFG
      Iterator<ISSABasicBlock> cfgIt = cfg.iterator();
      while (cfgIt.hasNext())
      {
        ISSABasicBlock ssaBb = cfgIt.next();

        // Iterate over SSA Instructions for a Basic Block
        Iterator<SSAInstruction> ssaIt = ssaBb.iterator();
        while (ssaIt.hasNext())
        {
          SSAInstruction ssaInstr = ssaIt.next();
          //Print out the instruction
          System.out.println(ssaInstr);
        }
      }
    }
    
    return null;
    //Graph<CGNode> g = pruneForAppLoader(cg);
    //
    //return g;
  }

  public static Graph<CGNode> pruneForAppLoader(CallGraph g) throws WalaException {
    return PDFTypeHierarchy.pruneGraph(g, new ApplicationLoaderFilter());
  }

  /**
   * Validate that the command-line arguments obey the expected usage.
   * 
   * Usage:
   * <ul>
   * <li>args[0] : "-appJar"
   * <li> args[1] : something like "c:/temp/testdata/java_cup.jar" </ul?
   * 
   * @throws UnsupportedOperationException if command-line is malformed.
   */
  public static void validateCommandLine(Properties p) {
    if (p.get("appJar") == null) {
      throw new UnsupportedOperationException("expected command-line to include -appJar");
    }
  }

  /**
   * A filter that accepts WALA objects that "belong" to the application loader.
   * 
   * Currently supported WALA types include
   * <ul>
   * <li> {@link CGNode}
   * <li> {@link LocalPointerKey}
   * </ul>
   */
  private static class ApplicationLoaderFilter implements Filter<CGNode> {

    public boolean accepts(CGNode o) {
      if (o instanceof CGNode) {
        CGNode n = (CGNode) o;
        return n.getMethod().getDeclaringClass().getClassLoader().getReference().equals(ClassLoaderReference.Application);
      } else if (o instanceof LocalPointerKey) {
        LocalPointerKey l = (LocalPointerKey) o;
        return accepts(l.getNode());
      } else {
        return false;
      }
    }
  }
}
