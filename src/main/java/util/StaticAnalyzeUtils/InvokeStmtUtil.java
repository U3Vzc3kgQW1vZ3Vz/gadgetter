package java.util.StaticAnalyzeUtils;

import jdd.tranModel.TransformableNode;
import java.cfg.Node;
import soot.*;
import soot.jimple.Stmt;
import jdd.util.ClassRelationshipUtils;

import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;
/**
 * Basic static analysis capabilities
 */
public class InvokeStmtUtil {

    public static ValueBox getObjectValueBox(Unit unit){
        for(ValueBox valueBox : unit.getUseBoxes()){
            if(valueBox.toString().contains("JimpleLocalBox")) return valueBox;
        }
        return null;
    }

    public static ValueBox getArgValueBox(Unit unit, int argIndex){
        if(!((Stmt) unit).containsInvokeExpr()) return null;
        return  ((Stmt) unit).getInvokeExpr().getArgBox(argIndex);
    }

    public static String getDefVariableName(Node node){
        if(node.unit.getDefBoxes().isEmpty()) return null;
        return node.unit.getDefBoxes().get(0).getValue().toString();
    }

    public static HashSet<ValueBox> getAllArgValueBoxes(Unit unit){
        HashSet<ValueBox> ret = new HashSet<>();
        if(!((Stmt) unit).containsInvokeExpr()) return ret;
        for(int ind = 0 ; ind < ((Stmt) unit).getInvokeExpr().getArgCount(); ind++){
            ValueBox vb = ((Stmt) unit).getInvokeExpr().getArgBox(ind);
            ret.add(vb);
        }
        return ret;
    }

    public static int getArgIndexByValueBox(Unit unit, ValueBox valueBox){
        if(!((Stmt) unit).containsInvokeExpr()) return -1;
        for(int ind = 0 ; ind < ((Stmt) unit).getInvokeExpr().getArgCount(); ind++){
            ValueBox vb = ((Stmt) unit).getInvokeExpr().getArgBox(ind);
            if(vb.equals(valueBox)) return ind;
        }
        return -1;
    }

    /**
     * Find the exact implementation from this type from many CHA methods, if it does not implement it itself, find its parent class;
     * If type is a non-specific method, filter the possibleMethods class that belongs to the subclass of the class corresponding to type.
     */
    public static HashSet<SootMethod> findExactMethodFromCHAMethods(Set<SootMethod> possibleMethods, SootClass expectClass,
                                                     TransformableNode tfNode){
        HashSet<SootMethod> ret = new HashSet<>();
        if(expectClass == null | !tfNode.containsInvoke() | possibleMethods.isEmpty()) return ret;

        String invokedMethodSubSig = tfNode.getUnitInvokeExpr().getMethod().getSubSignature();
        String invokedMethodName = tfNode.getUnitInvokeExpr().getMethod().getName();
// 1. Obtain the accurate method implementation [Note: Generally speaking, java.lang.Object should be excluded. If it needs to be excluded by default, it will be excluded before calling the method, otherwise the specific methods of the Object class will be filtered out]
        if (expectClass.isConcrete()){
            for (SootClass sootClass: ClassUtils.getAllSupers(expectClass)){
                SootMethod tmpInvokedMethod = sootClass.getMethodUnsafe(invokedMethodSubSig);
                if (tmpInvokedMethod != null){
                    ret.add(tmpInvokedMethod);
                    break;
                }
            }
        }
// 2. If the type is a non-specific method, filter the class in possibleMethods that belongs to the class corresponding to the type.
        else {
            ret = ClassRelationshipUtils.getAllSubMethods(expectClass, invokedMethodSubSig);
//            ret.retainAll(possibleMethods);
        }

// Consider the case where init and other related methods are taken out at once, that is, they cannot be returned directly. These methods need to be retained from possibleMethods
        for (SootMethod tmpInvokedMethod: possibleMethods){
            if (!tmpInvokedMethod.getSubSignature().equals(invokedMethodSubSig)
                    && !tmpInvokedMethod.getName().equals(invokedMethodName))
                ret.add(tmpInvokedMethod);
        }

        return ret;
    }

    /**
     * For multiple expected class processing scenarios that do not have mutually inclusive relationships
     * @param possibleMethods
     * @param expectClasses
     * @param tfNode
     * @return
     */
    public static HashSet<SootMethod> findExactMethodFromCHAMethods(Set<SootMethod> possibleMethods,
                                                                    HashSet<SootClass> expectClasses,
                                                                    TransformableNode tfNode){
        HashSet<SootMethod> ret = new HashSet<>();
        if(expectClasses.isEmpty()| !tfNode.containsInvoke() | possibleMethods.isEmpty()) return ret;

        SootMethod invokedMethod = tfNode.getUnitInvokeExpr().getMethod();
        String invokedMethodSubSig = tfNode.getUnitInvokeExpr().getMethod().getSubSignature();
        String invokedMethodName = tfNode.getUnitInvokeExpr().getMethod().getName();

// Solve common subclasses between constraint types; by default, filtering is performed when pointer information is stored, and the stored class constraint information should have a "solution"
// First perform type constraint solution, and then further solve the method
        HashSet<SootClass> sameSubClasses = ClassUtils.getAllSubs(invokedMethod.getDeclaringClass());
        for (SootClass expectClass: expectClasses){
            if (expectClass.isConcrete()) {
                sameSubClasses.retainAll(Arrays.asList(expectClass));
            }
            else {
                sameSubClasses.retainAll(ClassUtils.getAllSubs(expectClass));
            }
        }
        if (sameSubClasses.isEmpty())
            return ret;

        for (SootClass expectClass: sameSubClasses){
// Get the method directly, if not, look for the parent class
            SootMethod tmpInvokedMethod = expectClass.getMethodUnsafe(invokedMethodSubSig);
            if (tmpInvokedMethod != null) {
                if (tmpInvokedMethod.isConcrete())
                    ret.add(tmpInvokedMethod);
            }
            else {
                for (SootClass superClass: ClassUtils.getAllSupers(expectClass)){
                    tmpInvokedMethod = superClass.getMethodUnsafe(invokedMethodSubSig);
                    if (tmpInvokedMethod != null){
                        if (tmpInvokedMethod.isConcrete())
                            ret.add(tmpInvokedMethod);
                        break;
                    }
                }
            }
        }

// Consider the case where init and other related methods are taken out at once, that is, they cannot be returned directly. These methods need to be retained from possibleMethods
        for (SootMethod tmpInvokedMethod: possibleMethods){
            if (!tmpInvokedMethod.getSubSignature().equals(invokedMethodSubSig)
                    && !tmpInvokedMethod.getName().equals(invokedMethodName))
                ret.add(tmpInvokedMethod);
        }

        return ret;
    }

    public static SootMethod findExactMethodFromCHAMethods(SootMethod possibleMethod, String type){
        SootClass expectClass = Scene.v().getSootClassUnsafe(type);
        if (expectClass == null) return null;
        SootMethod sootMethod = expectClass.getMethodUnsafe(possibleMethod.getSubSignature());
        if (sootMethod != null) return sootMethod;

        for (SootClass sootClass: ClassUtils.getAllSupers(expectClass)){
            SootMethod subMethod = sootClass.getMethodUnsafe(possibleMethod.getSubSignature());
            if (subMethod != null)
                return subMethod;
        }
        return null;
    }

    /**
     * When sootMethod is an interface method, find all its method implementations
     */
    public static HashSet<SootMethod> findConcreteImplementations(SootMethod sootMethod){
        HashSet<SootMethod> implementations = new HashSet<>();
        if (!sootMethod.getDeclaringClass().isInterface())
            return implementations;

        for (SootClass subClass: ClassUtils.getAllSubs_BFS(sootMethod.getDeclaringClass())){
            SootMethod subMethod = subClass.getMethodUnsafe(sootMethod.getSubSignature());
            if (subMethod != null )
                if (subMethod.isConcrete())
                    implementations.add(subMethod);
        }

        return implementations;
    }
    public static HashSet<SootMethod> findConcreteImplementations(SootClass sootClass, String subSig) {
        HashSet<SootMethod> implementations = new HashSet<>();

        for (SootClass subClass: ClassUtils.getAllSubs_BFS(sootClass)){
            SootMethod subMethod = subClass.getMethodUnsafe(subSig);
            if (subMethod != null & subMethod.isConcrete())
                implementations.add(subClass.getMethodUnsafe(subSig));
        }

        return implementations;
    }
}
