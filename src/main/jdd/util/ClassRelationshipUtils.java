package jdd.util;

import jdd.container.BasicDataContainer;
import jdd.container.FragmentsContainer;
import jdd.markers.RelationShip;
import org.jetbrains.annotations.NotNull;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;

import java.util.*;
import callgraph.utilClass.StaticAnalyzeUtils.ClassUtils;
import java.util.regex.Pattern;

public class ClassRelationshipUtils {

    /**
     * A given basicTypes list such as a class/interface list, obtaining all their subclasses/interface implementation classes, including itself
     *
     * @param basicTypes
     * @return
     */
    public static HashSet<String> getAllSubClasses(List<String> basicTypes) {
        HashSet<String> ret = new HashSet<>();
        for (String className : basicTypes) {
            SootClass sootClass = Scene.v().getSootClassUnsafe(className);
            if (sootClass != null) {
                for (SootClass subClassName : ClassUtils.getAllSubs(sootClass))
                    ret.add(subClassName.getName());
            }
        }

        return ret;
    }

    /**
     * Given a series of interface types/abstract types/normal type basicTypes, take out all implementation classes/subclasses of this class
     * Comply with the method signature containing the method name specified in the rule
     *
     * @param basicTypes
     * @param rule
     * @return
     */
    public static HashSet<String> getAllSubMethodSigs(@NotNull List<String> basicTypes, String rule) {
        HashSet<String> methodSigs = new HashSet<>();
        for (String className : basicTypes) {
            SootClass sootClass = Scene.v().getSootClassUnsafe(className);
            if (sootClass == null) continue;

            for (SootClass subClass : ClassUtils.getAllSubs(sootClass)) {
                for (SootMethod sootMethod : subClass.getMethods()) {
                    if (matchRule(sootMethod, rule)) {
                        methodSigs.add(sootMethod.getSignature());
                    }
                }
            }
        }
        return methodSigs;
    }

    /**
     * Given a SootMethod and a regular expression rule judge
     * Determine whether the name of this method meets the regular expression
     *
     * @param sootMethod
     * @param rule
     * @return
     */
    public static boolean matchRule(SootMethod sootMethod, String rule) {
        return Pattern.matches(rule, sootMethod.getName());
    }

    /**
     * Get all implementation methods of methodSig
     *
     * @param methodSig
     * @return
     */
    public static HashSet<String> getAllSubMethodSigs(String methodSig) {
        HashSet<SootMethod> subMethods = new HashSet<>();
        if (!Scene.v().containsMethod(methodSig)) {
            return new HashSet<>();
        }
        SootMethod sootMethod = Scene.v().getMethod(methodSig);
        if (sootMethod == null) return new HashSet<>();

        return Utils.toMethodSigs(getAllSubMethods(sootMethod));
    }

    public static HashSet<SootMethod> getAllSubMethods(SootMethod sootMethod) {
// HashSet<SootMethod> ret = new HashSet<>();
// for (SootClass subClass: ClassUtils.getAllSubs(sootMethod.getDeclaringClass())){
// SootMethod subMethod = subClass.getMethodUnsafe(sootMethod.getSubSignature());
// if (subMethod != null){
// ret.add(subMethod);
// }
// }
        return getAllSubMethods(sootMethod.getDeclaringClass(), sootMethod.getSubSignature());
    }

    /**
     * Returns the methodSubSig method in the subclass of sootClass
     *
     * @param sootClass
     * @param methodSubSig
     * @return
     */
    public static HashSet<SootMethod> getAllSubMethods(SootClass sootClass, String methodSubSig) {
        HashSet<SootMethod> ret = new HashSet<>();
        for (SootClass subClass : ClassUtils.getAllSubs(sootClass)) {
            SootMethod tmpMethod = subClass.getMethodUnsafe(methodSubSig);
            if (tmpMethod != null)
                ret.add(tmpMethod);
        }
        return ret;
    }

    /**
     * Determine whether sootMethod1 and sootMethod2 have the same parent/interface class method
     *
     * @param sootMethod1
     * @param sootMethod2
     * @return
     */
    public static boolean hasSameSuperMethod(SootMethod sootMethod1, SootMethod sootMethod2) {
        if (sootMethod1.equals(sootMethod2))
            return true;

        HashSet<SootMethod> toDelete = new HashSet<>();
        HashSet<SootMethod> superMethods1 = getAllSuperMethods(sootMethod1, true);
        for (SootMethod sootMethod : superMethods1) {
            if (sootMethod.isConcrete())
                toDelete.add(sootMethod);
        }

        HashSet<SootMethod> superMethods2 = getAllSuperMethods(sootMethod2, true);
        for (SootMethod sootMethod : superMethods2) {
            if (sootMethod.isConcrete())
                toDelete.add(sootMethod);
        }
        superMethods1.removeAll(toDelete);
        superMethods2.removeAll(toDelete);

        superMethods2.retainAll(superMethods1);
        return !superMethods2.isEmpty();
    }

    /**
     * Determine whether sootClass is a subclass of superClass (including itself)
     *
     * @param sootClass
     * @param superClass
     * @return
     */
    public static boolean isSubClassOf(SootClass sootClass, SootClass superClass) {
        if (superClass == null) return false;
        if (Utils.isBasicType(superClass.getName()))
            return false; // JDD believe that the basic class cannot be a parent class
        if (superClass.getName().equals("java.lang.Object")) return true;
        String superClassName = superClass.getName();
        if (BasicDataContainer.subClassSearchRecord.containsKey(superClassName))
            return BasicDataContainer.subClassSearchRecord.get(superClassName).contains(sootClass.getName());

        HashSet<String> subClasses = Utils.toClassNames(ClassUtils.getAllSubs(superClass));
        if (superClassName.equals("java.io.Serializable")
                || superClassName.equals("java.lang.reflect.InvocationHandler")
                || superClassName.equals("java.util.List")
                || superClassName.equals("java.util.Collection")
                || superClassName.equals("java.util.Map$Entry")
                || superClassName.equals("java.util.Map")
                || BasicDataContainer.subClassSearchRecord.get("java.util.Map$Entry").contains(superClassName)) {
            BasicDataContainer.subClassSearchRecord.put(superClassName, subClasses);
        }
        return subClasses.contains(sootClass.getName());
    }

    /**
     * Get the relationship between sootClass1 and sootClass2
     * 0: It doesn't matter
     * 1: Same
     * 2: sootClass1 is a subclass of sootClass2
     * 3: sootClass2 is a subclass of sootClass1
     * 4: SootClass1 and sootClass 2 have no direct relationship, and the parent class intersects
     *
     * @param sootClass1
     * @param sootClass2
     * @return
     */
    public static RelationShip getExtentRelationshipAmongClasses(SootClass sootClass1, SootClass sootClass2) {
        if (sootClass1.equals(sootClass2))
            return RelationShip.EQUAL;
        if (sootClass1.getName().equals("java.lang.Object"))
            return RelationShip.SUPER;
        if (sootClass2.getName().equals("java.lang.Object"))
            return RelationShip.SUB;

        HashSet<SootClass> superClasses1 = ClassUtils.getAllSupers(sootClass1);
        HashSet<SootClass> superClasses2 = ClassUtils.getAllSupers(sootClass2);
        HashSet<SootClass> subClasses1 = ClassUtils.getAllSubs(sootClass1);
        HashSet<SootClass> subClasses2 = ClassUtils.getAllSubs(sootClass2);

        if (superClasses1.contains(sootClass2))
            return RelationShip.SUB;
        else if (superClasses2.contains(sootClass1))
            return RelationShip.SUPER;
        else {
            superClasses1.retainAll(superClasses2);
            subClasses1.retainAll(subClasses2);
// Determine whether the same subclass exists, and the priority is higher than whether the same parent class exists.
            if (!subClasses1.isEmpty() & !superClasses1.isEmpty())
                return RelationShip.HAS_SAME_SUPER_AND_SUB;

            if (!subClasses1.isEmpty())
                return RelationShip.HAS_SAME_SUB;

            if (!superClasses1.isEmpty()) {
                return RelationShip.HAS_SAME_SUPER;
            } else return RelationShip.NONE;
        }
    }


    /* Is the class corresponding to className an internal implementation class of outerClass */
    public static boolean isOuterClassOf(SootClass sootClass, SootClass outerCLass) {
        if (!sootClass.hasOuterClass()) return false;
        return sootClass.getOuterClass().equals(outerCLass);
    }

    /**
     * Find the outer class of sootClass. If sootClass is not an inner class, it returns itself
     */
    public static SootClass getOuterClass(SootClass sootClass) {
        if (sootClass == null)
            return null;
        if (sootClass.hasOuterClass() & Utils.endWithNumber(sootClass.getName()))
            return sootClass.getOuterClass();
        return sootClass;
    }


    /**
     * Get all clz interfaces/abstract classes, which may not include themselves (it will be deleted based on whether Concrete is required)
     * Remove the java.io.Serializable interface to prevent unnecessary duplication
     */
    public static HashSet<SootClass> getAllInterfaceAbstractClz(SootClass clz) {
        HashSet<SootClass> ret = new HashSet<>();
        if (clz == null)
            return ret;
        LinkedHashSet<SootClass> superClzSet = ClassUtils.getAllSupers(clz);
        if (superClzSet.isEmpty()) {
            return ret;
        }
        for (SootClass supClz : superClzSet) {
            if (supClz.isConcrete()) {
                continue;
            }
            if (supClz.getName().equals("java.io.Serializable")
                    | supClz.getName().contains("java.io.Externalizable")
                    | supClz.getName().contains("java.lang.Cloneable")) {
                continue;
            }
            ret.add(supClz);
        }
        return ret;
    }

    /**
     * Get all classes of clz directly extend / implements, including yourself
     *
     * @param clz
     * @return
     */
    public static HashSet<SootClass> getAllDirectInterfaceAbstractClz(SootClass clz) {
        HashSet<SootClass> res = new HashSet<>();
        Set<SootClass> superClzSet = new HashSet<>();
        if (clz.hasSuperclass())
            superClzSet.add(clz.getSuperclass());
        if (clz.getInterfaceCount() > 0) {
            superClzSet.addAll(clz.getInterfaces());
        }

        for (SootClass supClz : superClzSet) {
            if (supClz.isConcrete()) continue;
            if (supClz.getName().equals("java.io.Serializable")
                    | supClz.getName().contains("java.io.Externalizable")
                    | supClz.getName().contains("java.lang.Cloneable")) {
                continue;
            }
            res.add(supClz);
        }
        res.add(clz);
        return res;
    }

    /**
     * Get all parent classes with subSigMtd method (existed by default)
     *
     * @param clz
     * @param subSigMtd
     * @param selfFlag  does not contain clz
     * @return
     */
    public static HashSet<SootClass> getDirectSuperClzWithMtd(SootClass clz, String subSigMtd, boolean selfFlag) {
        HashSet<SootClass> res = new HashSet<>();
        for (SootClass superClz : getAllDirectInterfaceAbstractClz(clz)) {
            if (superClz.equals(clz) & !selfFlag)
                continue;
            if (superClz.getMethodUnsafe(subSigMtd) != null)
                res.add(superClz);
        }
        return res;
    }

    public static HashSet<SootClass> getAllSuperClzWithMtd(SootClass clz, String subSigMtd, boolean selfFlag) {
        HashSet<SootClass> res = new HashSet<>();
        for (SootClass superClz : ClassUtils.getAllSupers(clz)) {
            if (superClz.equals(clz) & !selfFlag)
                continue;
            if (superClz.getMethodUnsafe(subSigMtd) != null)
                res.add(superClz);
        }
        return res;
    }

    /**
     * Return all parent class methods of sootMethod
     *
     * @param sootMethod
     * @return
     */
    public static LinkedHashSet<SootMethod> getAllSuperMethods(SootMethod sootMethod, boolean selfFlag) {
        String methodSubSig = sootMethod.getSubSignature();
        LinkedHashSet<SootMethod> ret = new LinkedHashSet<>();
        for (SootClass superClass : ClassUtils.getAllSupers(sootMethod.getDeclaringClass())) {
            if (!selfFlag & sootMethod.getDeclaringClass().equals(superClass))
                continue;
            SootMethod superMethod = superClass.getMethodUnsafe(methodSubSig);
            if (superMethod != null) {
                ret.add(superMethod);
            }
        }
        return ret;
    }

    /**
     * Get all parent class methods of sootMethod (previously not included)
     *
     * @param sootMethod
     * @return
     */
    public static HashSet<SootMethod> getDirectSuperMtdBySubSig(SootMethod sootMethod, boolean selfFlag) {
        SootClass clz = sootMethod.getDeclaringClass();
        String subSig = sootMethod.getSubSignature();
        HashSet<SootMethod> res = new HashSet<>();
        for (SootClass superClz : getAllDirectInterfaceAbstractClz(clz)) {
            if (superClz.equals(clz) & !selfFlag)
                continue;
            SootMethod superMethod = superClz.getMethodUnsafe(subSig);
            if (superMethod != null)
                res.add(superMethod);
        }
        return res;
    }

    public static HashSet<SootMethod> getAllSuperMtdBySubSig(SootMethod sootMethod, boolean selfFlag) {
        SootClass clz = sootMethod.getDeclaringClass();
        String subSig = sootMethod.getSubSignature();
        HashSet<SootMethod> res = new HashSet<>();
        for (SootClass superClz : getAllInterfaceAbstractClz(clz)) {
            if (superClz.equals(clz) & !selfFlag)
                continue;
            SootMethod superMethod = superClz.getMethodUnsafe(subSig);
            if (superMethod != null)
                res.add(superMethod);
        }
        SootMethod tmpObjMtd = BasicDataContainer.commonClassMap.get("Object").getMethodUnsafe(subSig);
        if (tmpObjMtd != null)
            if (tmpObjMtd.isConcrete() & !tmpObjMtd.isFinal())
                res.add(tmpObjMtd);

        return res;
    }

    /**
     * Determine whether it is an abstract/interface method
     *
     * @param sootMethod
     * @return
     */
    public static boolean isPolyMethod(SootMethod sootMethod) {
        if (sootMethod.isAbstract() | sootMethod.getDeclaringClass().isInterface())
            return true;
        return false;
    }

    /**
     * InvocationHandler method to determine whether it is a dynamic proxy
     *
     * @param mtd
     * @return
     */
    public static boolean isProxyMethod(SootMethod mtd) {

        if (!BasicDataContainer.openDynamicProxyDetect) {
            return false;
        }

        if (!mtd.getSubSignature().equals("java.lang.Object invoke(java.lang.Object,java.lang.reflect.Method,java.lang.Object[])"))
            return false;

        if (isSubClassOf(mtd.getDeclaringClass(), Utils.toSootClass("java.lang.reflect.InvocationHandler")))
            return true;
        return false;
    }

    /**
     * Get access to sootMethod: public, private, protected
     *
     * @param sootMethod
     * @return
     */
    public static String getAccessPermission(SootMethod sootMethod) {
        String accessPermission = sootMethod.getDeclaration().split(" ")[0];
        if (!BasicDataContainer.accessPermissions.contains(accessPermission))
            return "default";
        return accessPermission;
    }

    public static boolean isGetterMethod(SootMethod sootMethod) {
        String pattern = "(get)+([^a-z]+.*)+";
        return Pattern.matches(pattern, sootMethod.getName());
    }

    public static boolean isIsMethod(SootMethod sootMethod) {
        String pattern = "(is)+([^a-z]+.*)+";
        return Pattern.matches(pattern, sootMethod.getName());
    }

    public static boolean isSetterMethod(SootMethod sootMethod) {
        String pattern = "(set)+([^a-z]+.*)+";
        return Pattern.matches(pattern, sootMethod.getName());
    }


    /**
     * Check whether the sootMethod is a rewrite method of a certain interface type
     *
     * @param sootMethod
     * @return
     */
    public static boolean isOverWrittenInterfaceMtd(SootMethod sootMethod) {
        if (!sootMethod.isConcrete())
            return false;
        HashSet<SootClass> superClzs = ClassUtils.getAllSupers(sootMethod.getDeclaringClass());
        String subSignature = sootMethod.getSubSignature();
        for (SootClass superClz : superClzs) {
            if (!superClz.isInterface())
                continue;
            if (superClz.getMethodUnsafe(subSignature) != null)
                return true;
        }
        return false;
    }


    /**
     * Extract the method in sootClass according to subSig
     *
     * @param sootClass
     * @param subSigs
     * @return
     */
    public static HashSet<SootMethod> getMethods(SootClass sootClass, HashSet<String> subSigs) {
        HashSet<SootMethod> ret = new HashSet<>();
        for (String subSig : subSigs) {
            SootMethod method = sootClass.getMethodUnsafe(subSig);
            if (method != null)
                ret.add(method);
        }
        return ret;
    }

    /**
     * Determine whether sootMethod is a dynamic method
     * (1) Polymorphism
     * (2) Dynamic Agent
     * Expandable
     */
    public static boolean isDynamicMethod(SootMethod sootMethod) {
        if (FragmentsContainer.dynamicMtds.contains(sootMethod))
            return true;
        if (sootMethod.isAbstract()
                | sootMethod.getDeclaringClass().isInterface()
                | sootMethod.getDeclaringClass().getName().equals("java.lang.Object"))
            return true;
        return false;
    }

    /**
     * Determine whether superMethod is the parent class interface/abstract method of sootMethod
     * Heuristic: Object type does not allow duplicate parent class methods at all
     * Used to judge the legality of Fragment:head<->end (end should be the controllable parent method of head, that is, it has higher permission to call other methods)
     *
     * @param sootMethod  can be a specific method
     * @param superMethod cannot be a specific method
     * @return
     */
    public static boolean isValidSuperAbstractOrInterfaceMethod(SootMethod sootMethod, SootMethod superMethod) {
        if (superMethod.isConcrete() | superMethod.isNative())
            return false;

        LinkedHashSet<SootMethod> allSuperMethods = getAllSuperMethods(sootMethod, false);
        if (!allSuperMethods.contains(superMethod)
                | allSuperMethods.size() < 2)
            return false;

        int index = 0;
        for (SootMethod superMtd : allSuperMethods) {
            if (superMtd.getDeclaringClass().getName().equals("java.lang.Object"))
                return false;
            if (!superMethod.equals(superMtd) & superMtd.isConcrete())
                return false;
            if (superMethod.equals(superMtd) & index > 0)
                return true;
            index++;
        }

        return false;
    }

    /**
     * Get the method in sootClass with the same sub sig as methodSubSigs
     *
     * @param sootClass
     * @param methodSubSigs
     * @return
     */
    public static HashSet<SootMethod> getMethodsOfClass(SootClass sootClass, HashSet<String> methodSubSigs) {
        HashSet<SootMethod> ret = new HashSet<>();
        if (sootClass == null)
            return ret;
        for (String methodSubSig : methodSubSigs) {
            SootMethod tmpMethod = sootClass.getMethodUnsafe(methodSubSig);
            if (tmpMethod != null)
                ret.add(tmpMethod);
        }

        return ret;
    }

    /**
     * Methods that take the same child signature as subSig in sootClass, consider the parent class
     *
     * @param sootClass
     * @param subSig
     * @return
     */
    public static SootMethod getMethodOfClassAndSuper(SootClass sootClass, String subSig) {
        for (SootClass tmpClass : ClassUtils.getAllSupers(sootClass)) {
            SootMethod tmpMethod = tmpClass.getMethodUnsafe(subSig);
            if (tmpMethod != null) {
                if (!isDynamicMethod(tmpMethod))
                    return tmpMethod;
            }
        }

        return null;
    }

    /**
     * Determine whether the caller is invokedMethod (actual call method: next) The parent class method of the class to which it belongs: caller (parent class method)->subclass method
     *
     * @param caller
     * @param invokedMethod
     * @param next
     * @return
     */
    public static boolean isAbsSuperCallee(SootMethod caller, SootMethod invokedMethod, SootMethod next) {
        if (next == null)
            return false;
        if (next.isStatic())
            return false;
// 1. Same as calling method subSig
        if (!next.getSubSignature().equals(invokedMethod.getSubSignature()))
            return false;
// 2. The class that calls the method is a subclass of the class to which the current method belongs
        if (!ClassUtils.getAllSupers(next.getDeclaringClass()).contains(caller.getDeclaringClass()))
            return false;
// 3. The call method does not have the current method
        if (next.getDeclaringClass().getMethodUnsafe(caller.getSubSignature()) != null)
            return false;
        return true;
    }


    /**
     * Determine whether the sootMethod is in the callstack
     * Contains: equal / and one of the methods, which is an implementation of the same interface / abstract method
     *
     * @param callStack
     * @param sootMethod
     * @return
     */
    public static boolean containsInCallStack(LinkedList<SootMethod> callStack, SootMethod sootMethod) {
        if (callStack == null) {
            return false;
        }
        String subSig = sootMethod.getSubSignature();
        Set<SootClass> supClzOfMtd = getAllInterfaceAbstractClz(sootMethod.getDeclaringClass());

        for (SootMethod mtd : callStack) {
            if (!mtd.getSubSignature().equals(subSig))
                continue;
            SootClass clz = mtd.getDeclaringClass();
            Set<SootClass> supClzs = getAllInterfaceAbstractClz(clz);
            supClzs.retainAll(supClzOfMtd);
            if (supClzs.isEmpty())
                continue;
            return true;
        }
        return false;
    }

    /**
     * Find the top-level interface/abstract method upward
     *
     * @param sootMethod
     * @return
     */
    public static SootMethod getTopSuperMethod(SootMethod sootMethod) {
        String methodSubSig = sootMethod.getSubSignature();
        SootMethod ret = null;
        for (SootClass superClass : ClassUtils.getAllSupers(sootMethod.getDeclaringClass())) {
            SootMethod superMethod = superClass.getMethodUnsafe(methodSubSig);
            if (superMethod != null) {
                ret = superMethod;
            }
        }
        return ret;
    }

    public static HashSet<SootMethod> getMethodsByName(SootClass sootClass, String methodName) {
        List<SootMethod> ret = sootClass.getMethods();
        ret.removeIf(mtd -> !mtd.getName().equals(methodName));
        return new HashSet<>(ret);
    }
}
