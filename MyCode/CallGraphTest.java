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
import java.util.Iterator;
import java.util.Properties;

import com.ibm.wala.classLoader.IMethod;
import com.ibm.wala.core.tests.callGraph.CallGraphTestUtil;
import com.ibm.wala.examples.drivers.PDFCallGraph;
import com.ibm.wala.examples.properties.WalaExamplesProperties;
import com.ibm.wala.ipa.callgraph.AnalysisCache;
import com.ibm.wala.ipa.callgraph.AnalysisOptions;
import com.ibm.wala.ipa.callgraph.AnalysisScope;
import com.ibm.wala.ipa.callgraph.CGNode;
import com.ibm.wala.ipa.callgraph.CallGraph;
import com.ibm.wala.ipa.callgraph.CallGraphBuilderCancelException;
import com.ibm.wala.ipa.callgraph.CallGraphStats;
import com.ibm.wala.ipa.callgraph.Entrypoint;
import com.ibm.wala.ipa.callgraph.impl.Everywhere;
import com.ibm.wala.ipa.callgraph.impl.Util;
import com.ibm.wala.ipa.cha.ClassHierarchy;
import com.ibm.wala.properties.WalaProperties;
import com.ibm.wala.ssa.IR;
import com.ibm.wala.ssa.SSAOptions;
import com.ibm.wala.types.MethodReference;
import com.ibm.wala.util.WalaException;
import com.ibm.wala.util.config.AnalysisScopeReader;
import com.ibm.wala.util.debug.Assertions;
import com.ibm.wala.util.graph.Graph;
import com.ibm.wala.util.io.FileProvider;
import com.ibm.wala.util.strings.StringStuff;
import com.ibm.wala.viz.PDFViewUtil;
import com.ibm.wala.ipa.callgraph.*;
import com.ibm.wala.ssa.ISSABasicBlock;
import com.ibm.wala.ssa.SSACFG;
import com.ibm.wala.ssa.SSACFG.BasicBlock;
import com.ibm.wala.ssa.SSAInstruction;

/**
 * This simple example application builds a WALA IR and fires off a PDF viewer to visualize a DOT representation.
 */
public class CallGraphTest {

  public static void main(String[] args) throws IOException 
  {
    String appJar = "/home/chelseametcalf/workspace/Test.jar";
    
    try 
    {
        if (PDFCallGraph.isDirectory(appJar)) 
        {
          appJar = PDFCallGraph.findJarFiles(new String[] { appJar });
        }
        
        File exclusionFile = new File("/home/test1.txt");
        //AnalysisScope scope1 = AnalysisScopeReader.makeJavaBinaryAnalysisScope(appJar, exclusionFile != null ? exclusionFile : new File(
        //    CallGraphTestUtil.REGRESSION_EXCLUSIONS));
        //AnalysisScope scope = AnalysisScopeReader.makeJavaBinaryAnalysisScope(appJar, new File(CallGraphTestUtil.REGRESSION_EXCLUSIONS));
        AnalysisScope scope = AnalysisScopeReader.makeJavaBinaryAnalysisScope(appJar, (new FileProvider())
            .getFile(CallGraphTestUtil.REGRESSION_EXCLUSIONS));
        ClassHierarchy cha = ClassHierarchy.make(scope);
        Iterable<Entrypoint> entrypoints = com.ibm.wala.ipa.callgraph.impl.Util.makeMainEntrypoints(scope, cha);
        AnalysisOptions options = new AnalysisOptions(scope, entrypoints);
        com.ibm.wala.ipa.callgraph.CallGraphBuilder builder = Util.makeZeroCFABuilder(options, new AnalysisCache(), cha, scope);
        CallGraph cg = null;
        try 
        {
          cg = builder.makeCallGraph(options, null);
          for (CGNode node: cg) 
          {
            //System.out.println(node.toString());
            
            
            
            String methodSig = "java.lang.StringBuffer.append(Ljava/lang/String;)Ljava/lang/StringBuffer";
            
            MethodReference mr = StringStuff.makeMethodReference(methodSig);

            IMethod m = cha.resolveMethod(mr);
            AnalysisCache cache = new AnalysisCache();
            // Get the IR of a CGNode
            IR ir = cache.getSSACache().findOrCreateIR(m, Everywhere.EVERYWHERE, options.getSSAOptions());

            if (ir == null) {
              Assertions.UNREACHABLE("Null IR for " + m);
            }

            System.err.println(ir.toString());
            
            
            System.err.println(CallGraphStats.getStats(cg));
            
            
            //IR ir = node.getIR();

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
    catch (WalaException e)
    {
      // TODO Auto-generated catch block
      e.printStackTrace();
    }
  }
  
/*  public static void printCallGraphInfo(CallGraph CG)
  {
    for (CGNode node: CG) 
    {
      // Get the IR of a CGNode
      IR ir = node.getIR();

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
  }*/

}