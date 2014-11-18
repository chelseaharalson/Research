package MyCode;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;

import com.ibm.wala.classLoader.IClass;
import com.ibm.wala.classLoader.IMethod;
import com.ibm.wala.classLoader.ShrikeBTMethod;
import com.ibm.wala.ipa.callgraph.AnalysisCache;
import com.ibm.wala.ipa.callgraph.AnalysisOptions;
import com.ibm.wala.ipa.callgraph.AnalysisScope;
import com.ibm.wala.ipa.callgraph.CGNode;
import com.ibm.wala.ipa.callgraph.CallGraph;
import com.ibm.wala.ipa.callgraph.CallGraphBuilderCancelException;
import com.ibm.wala.ipa.callgraph.CallGraphStats;
import com.ibm.wala.ipa.callgraph.Entrypoint;
import com.ibm.wala.ipa.callgraph.impl.DefaultEntrypoint;
import com.ibm.wala.ipa.callgraph.impl.Util;
import com.ibm.wala.ipa.callgraph.propagation.LocalPointerKey;
import com.ibm.wala.ipa.callgraph.propagation.PointerAnalysis;
import com.ibm.wala.ipa.cfg.BasicBlockInContext;
import com.ibm.wala.ipa.cfg.InterproceduralCFG;
import com.ibm.wala.ipa.cha.ClassHierarchy;
import com.ibm.wala.ipa.cha.ClassHierarchyException;
import com.ibm.wala.ipa.slicer.MethodEntryStatement;
import com.ibm.wala.ipa.slicer.NormalReturnCaller;
import com.ibm.wala.ipa.slicer.NormalStatement;
import com.ibm.wala.ipa.slicer.Slicer;
import com.ibm.wala.ipa.slicer.Statement;
import com.ibm.wala.ipa.slicer.StatementWithInstructionIndex;
import com.ibm.wala.ipa.slicer.Slicer.ControlDependenceOptions;
import com.ibm.wala.ipa.slicer.Slicer.DataDependenceOptions;
import com.ibm.wala.ipa.slicer.thin.ThinSlicer;
import com.ibm.wala.ssa.IR;
import com.ibm.wala.ssa.ISSABasicBlock;
import com.ibm.wala.ssa.SSAAbstractInvokeInstruction;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.types.ClassLoaderReference;
import com.ibm.wala.types.Descriptor;
import com.ibm.wala.types.TypeReference;
import com.ibm.wala.util.CancelException;
import com.ibm.wala.util.WalaException;
import com.ibm.wala.util.collections.CollectionFilter;
import com.ibm.wala.util.collections.Filter;
import com.ibm.wala.util.config.AnalysisScopeReader;
import com.ibm.wala.util.debug.Assertions;
import com.ibm.wala.util.graph.Graph;
import com.ibm.wala.util.graph.GraphSlicer;
import com.ibm.wala.util.strings.Atom;

public class ControlStatements_Algorithm {

  static String appJar = "/home/chelseametcalf/workspace/hadoop-0.18.1-core.jar";
  
  static ArrayList<String> visitedNodes = new ArrayList<String>();

  public static void main(String args[]) throws IOException, ClassHierarchyException, IllegalArgumentException, CancelException {
    AnalysisScope scope = AnalysisScopeReader.makeJavaBinaryAnalysisScope(appJar, new File("Java60RegressionExclusions.txt"));

    ClassHierarchy cha = ClassHierarchy.make(scope);

    IClass reduceTask = cha.lookupClass(TypeReference.findOrCreate(ClassLoaderReference.Application, "Lorg/apache/hadoop/mapred/ReduceTask"));

    final ArrayList<Entrypoint> entries = new ArrayList<Entrypoint>();

    for (IMethod method : reduceTask.getAllMethods()) 
    {
      System.out.println("Adding Entry: " + method.getName());
      entries.add(new DefaultEntrypoint(method, cha));
    }

    Iterable<Entrypoint> entrypoints = new Iterable<Entrypoint>() 
    {
      @Override
      public Iterator<Entrypoint> iterator() 
      {
        return entries.iterator();
      }
    };

    AnalysisOptions options = new AnalysisOptions(scope, entrypoints);

    com.ibm.wala.ipa.callgraph.CallGraphBuilder builder = Util.makeZeroCFABuilder(options, new AnalysisCache(), cha, scope);
    CallGraph g = builder.makeCallGraph(options, null);
    PointerAnalysis pa = builder.getPointerAnalysis();

    Iterator<CGNode> iter = g.iterator();
    CGNode node;
    
    ArrayList<NormalStatement> statements = new ArrayList<NormalStatement>();
    while (iter.hasNext()) 
    {
      node = iter.next();
      if (node.getIR() == null) 
      {
        continue;
      }
      SSAInstruction[] instructions = node.getIR().getInstructions();

      for (SSAInstruction instruction : instructions) 
      {
        if (instruction instanceof SSAAbstractInvokeInstruction)
        {
          SSAAbstractInvokeInstruction invocation = (SSAAbstractInvokeInstruction) instruction;

          System.out.println("found method call: "
              + invocation.getCallSite().getProgramCounter()
              + ": "
              + invocation.getCallSite().getDeclaredTarget().getName());
          statements.add(new NormalStatement(node, node.getIR().getCallInstructionIndices(invocation.getCallSite()).intIterator().next()));
        }
      }
    }

    Statement[] parameter = new Statement[statements.size()];
    parameter = statements.toArray(parameter);
    traceConfig(parameter,g,pa);
  }

  public static String[] traceConfig(Statement[] statements, CallGraph g, PointerAnalysis pa) {
    ThinSlicer slicer = new ThinSlicer(g, pa);
    //ArrayList<String> visitedCGNodes = new ArrayList<String>();
    System.err.println(CallGraphStats.getStats(g));

    InterproceduralCFG icfg = new InterproceduralCFG(g);

    for (Statement t : statements) 
    {
      Iterator<BasicBlockInContext<ISSABasicBlock>> preds = icfg.getPredNodes(icfg.getEntry(t.getNode()));

      while (preds.hasNext()) 
      {
        BasicBlockInContext<ISSABasicBlock> pred = preds.next();
        // Get SSA instr out of BasicBlockInContext
        // Check instance of here...
        /*if (visitedCGNodes.indexOf(pred.toString()) > -1)
        {
           //System.out.println("Duplicate!");
           continue;
        }
        else
        {
          visitedCGNodes.add(pred.toString());
        }*/
        try 
        {
          // context-insensitive slice
          NormalStatement blockStatement = new NormalStatement(pred.getNode(), pred.getFirstInstructionIndex());
          Collection<Statement> backwardsSlices = slicer.computeBackwardThinSlice(blockStatement);
          for (Statement slice : backwardsSlices) 
          {
              // Filters normal statements
              if (!dumpSlice(slice))
              {
                break;
              }
          }
        } 
        catch (ArrayIndexOutOfBoundsException e)
        {
          //System.err.println("out of bounds exception thrown");
        }
      }
    }
    return new String[5];
  }
  
  public static boolean dumpSlice(Statement s) 
  {
    ArrayList<String> visitedSlice = new ArrayList<String>();
    //System.out.println(s.getKind() + "    " + Statement.Kind.NORMAL_RET_CALLER);
    if (s.getKind() == Statement.Kind.NORMAL_RET_CALLER) // ignore special kinds of statements
    { 
       SSAAbstractInvokeInstruction inst = ((NormalReturnCaller)s).getInstruction();
       if (inst.getDeclaredTarget().getName().toString().indexOf("getInt") >= 0 
           && (inst.getDeclaredTarget().getDeclaringClass().getName().toString().indexOf("Lorg/apache/hadoop/conf/Configuration") >= 0
           || inst.getDeclaredTarget().getDeclaringClass().getName().toString().indexOf("Lorg/apache/hadoop/mapred/ReduceTask") >= 0) 
           && inst.getDeclaredTarget().getDescriptor().toString().indexOf("Ljava/lang/String;") >= 0)
       {   
         //System.out.println(s);
         int bcIndex, instructionIndex = ((StatementWithInstructionIndex) s).getInstructionIndex();
         try {
               bcIndex = ((ShrikeBTMethod) s.getNode().getMethod()).getBytecodeIndex(instructionIndex);
               try {
                     int src_line_number = s.getNode().getMethod().getLineNumber(bcIndex);
                     String key = "Source line number = " + src_line_number + " in class " + s.getNode().getMethod().getDeclaringClass();
                     if (visitedNodes.indexOf(key) > -1 || visitedSlice.indexOf(s.toString()) > -1)
                     {
                        return false;
                     }
                     else
                     {
                        visitedNodes.add(key);
                        visitedSlice.add(s.toString());
                     }
                     System.out.println ( "Source line number = " + src_line_number + " in class " + s.getNode().getMethod().getDeclaringClass());
                     System.out.println(s);
                   } 
                   catch (Exception e) 
                   {
                     System.out.println("Bytecode index no good" + " in class " + s.getNode().getMethod().getDeclaringClass());
                     System.out.println(e.getMessage());
                   }
         } 
         catch (Exception e )
         {
             System.out.println("it's probably not a BT method (e.g. it's a fakeroot method)" + " in class " + s.getNode().getMethod().getDeclaringClass());
             System.out.println(e.getMessage());
         } 
     }
    }
    return true;
}
  
  public static CGNode findMainMethod(CallGraph cg) {
    Descriptor d = Descriptor.findOrCreateUTF8("([Ljava/lang/String;)V");
    Atom name = Atom.findOrCreateUnicodeAtom("main");
    for (Iterator<? extends CGNode> it = cg.getSuccNodes(cg.getFakeRootNode()); it.hasNext();) {
      CGNode n = it.next();
      if (n.getMethod().getName().equals(name) && n.getMethod().getDescriptor().equals(d)) {
        return n;
      }
    }
    Assertions.UNREACHABLE("failed to find main() method");
    return null;
  }

  public static Statement findCallTo(CGNode n, String methodName) {
    IR ir = n.getIR();
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
    Assertions.UNREACHABLE("failed to find call to " + methodName + " in " + n);
    return null;
  }

  public static Graph<CGNode> pruneForAppLoader(CallGraph g)
      throws WalaException {
    return pruneGraph(g, new ApplicationLoaderFilter());
  }

  public static <T> Graph<T> pruneGraph(Graph<T> g, Filter<T> f)
      throws WalaException {
    Collection<T> slice = GraphSlicer.slice(g, f);
    return GraphSlicer.prune(g, new CollectionFilter<T>(slice));
  }

  /**
   * A filter that accepts WALA objects that "belong" to the application
   * loader.
   * 
   * Currently supported WALA types include
   * <ul>
   * <li> {@link CGNode}
   * <li> {@link LocalPointerKey}
   * </ul>
   */
  private static class ApplicationLoaderFilter implements Filter<CGNode> {

    @Override
    public boolean accepts(CGNode o) {
      if (o instanceof CGNode) {
        CGNode n = (CGNode) o;
        return n.getMethod().getDeclaringClass().getClassLoader()
            .getReference()
            .equals(ClassLoaderReference.Application);
      } else if (o instanceof LocalPointerKey) {
        LocalPointerKey l = (LocalPointerKey) o;
        return accepts(l.getNode());
      } else {
        return false;
      }
    }
  }
}