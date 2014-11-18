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

import com.ibm.wala.classLoader.IClass;
import com.ibm.wala.core.tests.callGraph.CallGraphTestUtil;
import com.ibm.wala.examples.properties.WalaExamplesProperties;
import com.ibm.wala.ipa.callgraph.AnalysisCache;
import com.ibm.wala.ipa.callgraph.AnalysisOptions;
import com.ibm.wala.ipa.callgraph.AnalysisScope;
import com.ibm.wala.ipa.callgraph.CGNode;
import com.ibm.wala.ipa.callgraph.CallGraph;
import com.ibm.wala.ipa.callgraph.Entrypoint;
import com.ibm.wala.ipa.callgraph.impl.Util;
import com.ibm.wala.ipa.cha.ClassHierarchy;
import com.ibm.wala.ipa.cha.ClassHierarchyException;
import com.ibm.wala.ipa.cha.IClassHierarchy;
import com.ibm.wala.properties.WalaProperties;
import com.ibm.wala.ssa.IR;
import com.ibm.wala.ssa.ISSABasicBlock;
import com.ibm.wala.ssa.SSACFG;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.types.ClassLoaderReference;
import com.ibm.wala.util.WalaException;
import com.ibm.wala.util.collections.CollectionFilter;
import com.ibm.wala.util.collections.Filter;
import com.ibm.wala.util.config.AnalysisScopeReader;
import com.ibm.wala.util.debug.Assertions;
import com.ibm.wala.util.graph.Graph;
import com.ibm.wala.util.graph.GraphSlicer;
import com.ibm.wala.util.graph.impl.SlowSparseNumberedGraph;
import com.ibm.wala.util.io.FileProvider;
import com.ibm.wala.viz.DotUtil;
import com.ibm.wala.viz.PDFViewUtil;
import com.ibm.wala.ipa.callgraph.*;
import com.ibm.wala.ssa.ISSABasicBlock;
import com.ibm.wala.ssa.SSACFG;
import com.ibm.wala.ssa.SSACFG.BasicBlock;
import com.ibm.wala.ssa.SSAInstruction;

/**
 * 
 * This simple example WALA application builds a TypeHierarchy and fires off
 * ghostview to viz a DOT representation.
 * 
 * @author sfink
 */
public class Test_PDFTypeHierarchy {
  
  final static int CLASSPATH_INDEX = 1; 

  public static void main(String[] args) throws IOException, ClassHierarchyException 
  {
    System.out.println("hi");
    File exclusionFile = new File("/home/test1.txt");
    //AnalysisScope scope = AnalysisScopeReader.makeJavaBinaryAnalysisScope(appJar, new File(CallGraphTestUtil.REGRESSION_EXCLUSIONS));
    String classpath = args[CLASSPATH_INDEX];
    AnalysisScope scope = AnalysisScopeReader.makeJavaBinaryAnalysisScope(classpath, (new FileProvider()).getFile(CallGraphTestUtil.REGRESSION_EXCLUSIONS));

    // invoke WALA to build a class hierarchy
    ClassHierarchy cha = ClassHierarchy.make(scope);
    Iterable<Entrypoint> entrypoints1 = com.ibm.wala.ipa.callgraph.impl.Util.makeMainEntrypoints(scope, cha);
    AnalysisOptions options1 = new AnalysisOptions(scope, entrypoints1);
    com.ibm.wala.ipa.callgraph.CallGraphBuilder builder = Util.makeZeroCFABuilder(options1, new AnalysisCache(), cha, scope);
    CallGraph cg = null;
    try 
    {
      cg = builder.makeCallGraph(options1, null);
      for (CGNode node: cg) 
      {
        System.out.println(node.toString());
        // Get the IR of a CGNode
        IR ir = node.getIR();
        
        System.out.println("test8.5");
        
        if(ir == null)
        {
          System.out.println("NULL!!!!!!");
        }
        else
        {
          System.out.println("NOT NULL!!!!!!!");
        }
        
        // Get CFG from IR
        SSACFG cfg = ir.getControlFlowGraph();
        
        System.out.println("test8.6");

        // Iterate over the Basic Blocks of CFG
        Iterator<ISSABasicBlock> cfgIt = cfg.iterator();
        System.out.println("TEST9");
        while (cfgIt.hasNext())
        {
          ISSABasicBlock ssaBb = cfgIt.next();

          // Iterate over SSA Instructions for a Basic Block
          Iterator<SSAInstruction> ssaIt = ssaBb.iterator();
          System.out.println("TEST10");
          while (ssaIt.hasNext())
          {
            SSAInstruction ssaInstr = ssaIt.next();
            //Print out the instruction
            System.out.println(ssaInstr);
          }
        }
      }
    } 
    catch (IllegalArgumentException e) 
    {
      // TODO Auto-generated catch block
      e.printStackTrace();
     } 
    catch (Exception e) 
    {
      // TODO Auto-generated catch block
      e.printStackTrace();
    }
  } 

}