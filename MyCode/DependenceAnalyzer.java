package MyCode;


/*******************************************************************************
 * Copyright (c) 2008 IBM Corporation.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     IBM Corporation - initial API and implementation
 *******************************************************************************/


import java.io.File;
import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Iterator;
import java.util.Properties;
import java.util.HashSet;


import com.ibm.wala.classLoader.IBytecodeMethod;
import com.ibm.wala.classLoader.IClass;
import com.ibm.wala.classLoader.IMethod;
import com.ibm.wala.ipa.callgraph.AnalysisCache;
import com.ibm.wala.ipa.callgraph.AnalysisOptions;
import com.ibm.wala.ipa.callgraph.AnalysisScope;
import com.ibm.wala.ipa.callgraph.CallGraph;
import com.ibm.wala.ipa.callgraph.CallGraphBuilder;
import com.ibm.wala.ipa.callgraph.CallGraphBuilderCancelException;
import com.ibm.wala.ipa.callgraph.CallGraphStats;
import com.ibm.wala.ipa.callgraph.CGNode;
import com.ibm.wala.ipa.callgraph.ContextSelector;
import com.ibm.wala.ipa.callgraph.Entrypoint;
import com.ibm.wala.ipa.callgraph.propagation.HeapModel;
import com.ibm.wala.ipa.callgraph.propagation.InstanceKey;
import com.ibm.wala.ipa.callgraph.propagation.PointerAnalysis;
import com.ibm.wala.ipa.callgraph.propagation.PointerKey;
import com.ibm.wala.ipa.callgraph.propagation.SSAContextInterpreter;
import com.ibm.wala.ipa.callgraph.propagation.cfa.ZeroXContainerCFABuilder;
import com.ibm.wala.ipa.callgraph.propagation.cfa.ZeroXInstanceKeys;
import com.ibm.wala.ipa.callgraph.impl.DefaultEntrypoint;
import com.ibm.wala.ipa.callgraph.impl.ExplicitCallGraph;
import com.ibm.wala.ipa.callgraph.impl.Util;
import com.ibm.wala.ipa.callgraph.impl.Everywhere;
import com.ibm.wala.ipa.cfg.ExplodedInterproceduralCFG;
import com.ibm.wala.ipa.cha.ClassHierarchy;
import com.ibm.wala.ipa.cha.ClassHierarchyException;
import com.ibm.wala.ipa.cha.IClassHierarchy;
import com.ibm.wala.shrikeCT.InvalidClassFileException; 
import com.ibm.wala.ssa.IR;
import com.ibm.wala.ssa.SSACFG;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.ssa.SSAMonitorInstruction;
import com.ibm.wala.ssa.SSAAbstractInvokeInstruction;
import com.ibm.wala.ssa.SSAInvokeInstruction;
import com.ibm.wala.ssa.analysis.ExplodedControlFlowGraph;
import com.ibm.wala.ssa.analysis.IExplodedBasicBlock;
import com.ibm.wala.types.ClassLoaderReference;
import com.ibm.wala.types.TypeReference;
import com.ibm.wala.util.config.AnalysisScopeReader;
import com.ibm.wala.util.graph.NumberedEdgeManager;
import com.ibm.wala.util.intset.IntSet;
import com.ibm.wala.util.intset.OrdinalSet;
import com.ibm.wala.util.intset.IntSetAction;
import com.ibm.wala.util.intset.IntIterator;
import com.ibm.wala.util.io.CommandLine;
import com.ibm.wala.util.strings.StringStuff;
import com.ibm.wala.util.warnings.Warnings;

import com.ibm.wala.ipa.slicer.Slicer;
import com.ibm.wala.ipa.slicer.Slicer.ControlDependenceOptions;
import com.ibm.wala.ipa.slicer.Slicer.DataDependenceOptions;
import com.ibm.wala.ipa.slicer.Statement;
import com.ibm.wala.ipa.slicer.StatementWithInstructionIndex;
import com.ibm.wala.ipa.slicer.Statement.Kind;
import com.ibm.wala.ipa.slicer.thin.ThinSlicer;
import com.ibm.wala.util.debug.Assertions;
import com.ibm.wala.classLoader.ShrikeBTMethod;
import com.ibm.wala.ipa.slicer.NormalStatement;
import com.ibm.wala.ipa.slicer.NormalReturnCaller;
import java.util.HashMap;
/**
 * Driver that constructs a call graph for an application specified via a scope file.  
 * Useful for getting some code to copy-paste.    
 */
public class DependenceAnalyzer {

    // Should read this from the command line
    static String targetClassNames;
    static String mainClass;
    static String entryClass;
    static String exclusionsFile;
    static CallGraphBuilder builder;
    static IClassHierarchy cha;
    static CallGraph cg;
    static ExplodedInterproceduralCFG icfg;
    static PointerAnalysis pointerAnalysis; 
    static HeapModel heapModel;
    static String[] slicingMethod = {"context-sensitive traditional slice",
                             "context-sensitive thin slice",
                             "context-insensitive thin slice"}; 
    static int analysisChoice = 0; // context-sensitive traditional slice
    /* 1 : context-sensitive thin slice
       2: context-insensitive thin slice */

  /**
   * Usage: ScopeFileCallGraph -scopeFile file_path [-entryClass class_name |
   * -mainClass class_name]
   * 
   * If given -mainClass, uses main() method of class_name as entrypoint. If
   * given -entryClass, uses all public methods of class_name.
   * 
   * @throws IOException
   * @throws ClassHierarchyException
   * @throws CallGraphBuilderCancelException
   * @throws IllegalArgumentException
   */
    public static void main(String[] args) throws Exception, IOException, ClassHierarchyException, IllegalArgumentException,
            CallGraphBuilderCancelException, InvalidClassFileException {
    long start = System.currentTimeMillis();
    Properties p = CommandLine.parse(args);
    String scopeFile = p.getProperty("scopeFile");
    exclusionsFile = p.getProperty("exclusionsFile");
    entryClass = p.getProperty("entryClass");
    mainClass = p.getProperty("mainClass");
    targetClassNames = p.getProperty("targetClass");
    analysisChoice = Integer.valueOf(p.getProperty("analysisChoice"));
    // Format: Each line represents a separate statement specification
    // className;methodName;lineNo
    if (mainClass != null && entryClass != null) {
      throw new IllegalArgumentException("only specify one of mainClass or entryClass");
    }
    // use exclusions to eliminate certain library packages

    if (targetClassNames == null)
  System.out.println("WARNING: Analysis could be more efficient by specifying a semicolon separated list of target classes (excluding mainClass and entryClass) with -targetClassNames option (use / instead of . in class names)"); 

    System.out.println("building call graph...");
    configureAndCreateCallGraph(scopeFile, mainClass, entryClass); 

//    CallGraphBuilder builder = Util.makeNCFABuilder(2, options, cache, cha, scope);
//    CallGraphBuilder builder = Util.makeVanillaNCFABuilder(2, options, cache, cha, scope);


 

    pointerAnalysis = builder.getPointerAnalysis();
    heapModel = pointerAnalysis.getHeapModel();
    //System.out.println("Exploding the call graph.." + cg.getClass().getName());
    icfg = ExplodedInterproceduralCFG.make(cg);
    ArrayList<Statement> seedStatements = new ArrayList<Statement>();
                            
    for(CGNode node: icfg.getCallGraph()) {
       // find seed statement
       Statement statement = findCallTo(node, "newInstance");
       if (statement != null)
           seedStatements.add(statement);
    }
                            
    Collection<Statement> slice = null;
                            
    for(Statement statement: seedStatements)
    {
        if (analysisChoice == 0) 
        {
                 // context-sensitive traditional slice
                  slice = Slicer.computeBackwardSlice ( statement, cg, pointerAnalysis);
        }
        else if (analysisChoice == 1) 
        {
                                  
                 // context-sensitive thin slice
                 slice = Slicer.computeBackwardSlice(statement, cg, pointerAnalysis, DataDependenceOptions.NO_BASE_PTRS,ControlDependenceOptions.NONE);
        }
        else if (analysisChoice == 2) 
        {                  
            // context-insensitive slice
           ThinSlicer ts = new ThinSlicer(cg,pointerAnalysis);
           slice = ts.computeBackwardThinSlice ( statement );
        }
        dumpSlice(statement, analysisChoice, slice);                        
    }

    long end = System.currentTimeMillis();
    System.out.println("done");
    System.out.println("took " + (end-start) + "ms");
    System.out.println(CallGraphStats.getStats(cg));

  }

    private static void configureAndCreateCallGraph(String scopeFile, String mainClass, String entryClass) throws IOException, ClassHierarchyException, CallGraphBuilderCancelException  {
    File exclusionsFile = null;
    AnalysisScope scope = AnalysisScopeReader.readJavaScope(scopeFile, exclusionsFile, DependenceAnalyzer.class.getClassLoader());
    cha = ClassHierarchy.make(scope);
    //System.out.println(cha.getNumberOfClasses() + " classes");
    //System.out.println(Warnings.asString());
    Warnings.clear();
    AnalysisOptions options = new AnalysisOptions();
    Iterable<Entrypoint> entrypoints = null;
    if (entryClass != null) {
       ArrayList<Entrypoint> all = new ArrayList<Entrypoint>();
       String[] entryClassName = entryClass.split(";");
       for(int i=0; i < entryClassName.length; i++) {
          System.out.println("Making entry points for class " + entryClassName[i]);
          // Removing the prefix L before passing to makePublicEntryPoints!
          all.addAll((Collection<Entrypoint>)makePublicEntrypoints(scope, cha, entryClassName[i].substring(1)));
      }
       entrypoints = all;
    }
    else entrypoints = Util.makeMainEntrypoints(scope, cha, mainClass);
    //Iterable<Entrypoint> entrypoints = entryClass != null ? makePublicEntrypoints(scope, cha, entryClass) : Util.makeMainEntrypoints(scope, cha, mainClass);
    options.setEntrypoints(entrypoints);
    options.setHandleStaticInit(true);
    // you can dial down reflection handling if you like
    options.setReflectionOptions(AnalysisOptions.ReflectionOptions.NONE);
    AnalysisCache cache = new AnalysisCache();
    // other builders can be constructed with different Util methods
    Util.addDefaultSelectors(options, cha);
    Util.addDefaultBypassLogic(options, scope, Util.class.getClassLoader(), cha);
    ContextSelector appSelector = null;
    SSAContextInterpreter appInterpreter = null;
    // This disables ZeroXInstanceKeys.SMUSH_PRIMITIVE_HOLDERS (by not explicitly specifying it)
    builder = new ZeroXContainerCFABuilder(cha, options, cache, appSelector, appInterpreter, ZeroXInstanceKeys.ALLOCATIONS | ZeroXInstanceKeys.SMUSH_MANY |  ZeroXInstanceKeys.SMUSH_STRINGS | ZeroXInstanceKeys.SMUSH_THROWABLES);
    //Util.makeZeroOneContainerCFABuilder(options, cache, cha, scope);     
    cg = builder.makeCallGraph(options, null);

  }

  private static Iterable<Entrypoint> makePublicEntrypoints(AnalysisScope scope, IClassHierarchy cha, String entryClass) {
    Collection<Entrypoint> result = new ArrayList<Entrypoint>();
    System.out.println(StringStuff.deployment2CanonicalTypeString(entryClass));
    System.out.println(TypeReference.findOrCreate(ClassLoaderReference.Application,
        StringStuff.deployment2CanonicalTypeString(entryClass)));
    IClass klass = cha.lookupClass(TypeReference.findOrCreate(ClassLoaderReference.Application,
        StringStuff.deployment2CanonicalTypeString(entryClass)));
    for (IMethod m : klass.getDeclaredMethods()) {
      //if (m.isPublic()) {
        result.add(new DefaultEntrypoint(m, cha));
      //}
    }
    return result;
  }
    
    public static Statement findCallTo(CGNode n, String methodName) {
       if (targetClassNames != null && targetClassNames.indexOf(n.getMethod().getDeclaringClass().getName().toString()) < 0)
     return null;  

        IR ir = n.getIR();
        if (ir == null) return null;
        for (Iterator<SSAInstruction> it = ir.iterateAllInstructions(); it.hasNext();) {
            SSAInstruction s = it.next();
            if (s instanceof com.ibm.wala.ssa.SSAAbstractInvokeInstruction) {
                com.ibm.wala.ssa.SSAAbstractInvokeInstruction call = (com.ibm.wala.ssa.SSAAbstractInvokeInstruction) s;
                if (call.getCallSite().getDeclaredTarget().getName().toString().equals(methodName)) {
                    com.ibm.wala.util.intset.IntSet indices = ir.getCallInstructionIndices(call.getCallSite());
                    com.ibm.wala.util.debug.Assertions.productionAssertion(indices.size() == 1, "expected 1 but got " + indices.size());
                    return new com.ibm.wala.ipa.slicer.NormalStatement(n, indices.intIterator().next());
                }
            }
        }
        //Assertions.UNREACHABLE("failed to find call to " + methodName + " in " + n);
        return null;
  }
    
  public static void dumpSlice(Statement seed, int method, Collection<Statement> slice) 
  {
      System.out.println(slicingMethod[method] + "\nseed=" + seed);
        for (Statement s : slice) 
        {

            if (s.getKind() == Statement.Kind.NORMAL_RET_CALLER) 
            { // ignore special kinds of statements
               
               SSAAbstractInvokeInstruction inst = ((NormalReturnCaller)s).getInstruction();
               if (inst.getDeclaredTarget().getName().toString().indexOf("getInt") >= 0 && (inst.getDeclaredTarget().getDeclaringClass().getName().toString().indexOf("Lorg/apache/hadoop/conf/Configuration") >=0 || inst.getDeclaredTarget().getDeclaringClass().getName().toString().indexOf("Lorg/apache/hadoop/mapred/JobConf") >=0) && inst.getDeclaredTarget().getDescriptor().toString().indexOf("Ljava/lang/String;") >= 0) {   
                  System.out.println(s);
               int bcIndex, instructionIndex = ((StatementWithInstructionIndex) s).getInstructionIndex();
               try {
                     bcIndex = ((ShrikeBTMethod) s.getNode().getMethod()).getBytecodeIndex(instructionIndex);
                     try {
                           int src_line_number = s.getNode().getMethod().getLineNumber(bcIndex);
                           System.out.println ( "Source line number = " + src_line_number + " in class " + s.getNode().getMethod().getDeclaringClass());
                     } 
                     catch (Exception e) {
                       System.out.println("Bytecode index no good" + " in class " + s.getNode().getMethod().getDeclaringClass());
                       System.out.println(e.getMessage());
                     }
               } 
               catch (Exception e ) {
                   System.out.println("it's probably not a BT method (e.g. it's a fakeroot method)" + " in class " + s.getNode().getMethod().getDeclaringClass());
                   System.out.println(e.getMessage());
               } 
       }
            }
        }
  }
    
}
