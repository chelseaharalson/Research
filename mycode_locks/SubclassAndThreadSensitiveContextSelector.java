package mycode_locks;

import com.ibm.wala.ipa.callgraph.propagation.ReceiverInstanceContext;
import com.ibm.wala.ipa.callgraph.Context;
import com.ibm.wala.classLoader.IMethod;
import com.ibm.wala.classLoader.CallSiteReference;
import com.ibm.wala.ipa.callgraph.propagation.InstanceKey;
import com.ibm.wala.ipa.callgraph.CGNode;
import com.ibm.wala.ipa.callgraph.ContextSelector;
import com.ibm.wala.ipa.cha.IClassHierarchy;
import com.ibm.wala.types.TypeReference;
import com.ibm.wala.util.intset.IntSet;
import com.ibm.wala.util.intset.SparseIntSet;


/**
 * A context selector selecting a ReciverInstanceContext for java.lang.Thread.start()V invocations.
 */
class SubclassAndThreadSensitiveContextSelector implements ContextSelector {   
//    public Context getCalleeTarget(CGNode caller, CallSiteReference site, IMethod callee,  InstanceKey reciever) {
//    if (isThreadStart(callee))
//      return new ReceiverInstanceContext(reciever);
//    else
//      return null;
//  }
  
    public Context getCalleeTarget(CGNode caller, CallSiteReference site, IMethod callee,  InstanceKey[] actualParameters) {
  if ((isThreadMethod(callee) || callee.isSynchronized()) && actualParameters != null && actualParameters.length > 0 && actualParameters[0] != null)
      return new ReceiverInstanceContext(actualParameters[0]);
    else
      return null;
  }
    
  private boolean isThreadMethod(IMethod method) {
    IClassHierarchy cha = method.getClassHierarchy();
    return !method.isStatic() && cha.isAssignableFrom(cha.lookupClass(TypeReference.JavaLangThread), method.getDeclaringClass());
  }
  
  public IntSet getRelevantParameters(CGNode caller, CallSiteReference sitesite) {
    if (sitesite.getDeclaredTarget().getNumberOfParameters() > 0)
      return SparseIntSet.singleton(0);
    else 
      return new SparseIntSet();
  }
}