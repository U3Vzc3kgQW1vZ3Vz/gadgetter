package jdd.util;

import jdd.container.BasicDataContainer;
import jdd.dataflow.node.MethodDescriptor;
import jdd.dataflow.node.SourceNode;
import jdd.tranModel.Taint.Taint;
import lombok.extern.slf4j.Slf4j;
import soot.*;
import soot.jimple.FieldRef;
import soot.jimple.InvokeExpr;
import soot.jimple.ParameterRef;

import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;


@Slf4j
public class Utils {
    public static Set<String> toSet(String str) {
        HashSet<String> ret = new HashSet<>();
        for (String sinkRule : str.split(",")) {
            if (sinkRule.isEmpty()) continue;
            ret.add(sinkRule);
        }
        return ret;
    }

    public static LinkedList toLinkedList(Object object) {
        LinkedList ret = new LinkedList();
        ret.add(object);
        return ret;
    }

    public static SootMethod toSootMethod(String methodSig) {
        if (Scene.v().containsMethod(methodSig))
            return Scene.v().getMethod(methodSig);
        return null;
    }

    public static HashSet<String> toMethodSigs(HashSet<SootMethod> methods) {
        HashSet<String> ret = new HashSet<>();
        for (SootMethod sootMethod : methods)
            ret.add(sootMethod.getSignature());
        return ret;
    }

    public static HashSet<String> toClassNames(HashSet<SootClass> classes) {
        HashSet<String> ret = new HashSet<>();
        for (SootClass sootClass : classes)
            ret.add(sootClass.getName());
        return ret;
    }

    public static boolean endWithNumber(String str) {
        return Pattern.matches(".*\\$\\d+", str);
    }

    public static SootClass toSootClass(String className) {
        className = className.replace("[]", "");
        return Scene.v().getSootClassUnsafe(className);
    }

    // TODO: Do you need to consider the situation of []
    public static SootClass toSootClass(Type type) {
        String className = type.toString().replace("[]", "");
        return Scene.v().getSootClassUnsafe(className);
    }

    public static HashSet<String> toStringSet(HashSet hashSet) {
        return (HashSet<String>) hashSet.stream()
                .map(Object::toString) // Convert integers to strings
                .collect(Collectors.toSet());
    }


    public static boolean isBasicType(Type type) {
        String typeString = type.toString();
        return isBasicType(typeString);
    }

    public static boolean isBasicType(String typeString) {
        if (typeString.equals("java.lang.String"))
            return true;
        if (typeString.equals("int") || typeString.equals("java.lang.Integer"))
            return true;
        if (typeString.equals("byte") || typeString.equals("java.lang.Byte"))
            return true;
        if (typeString.equals("boolean") || typeString.equals("java.lang.Boolean"))
            return true;
        if (typeString.equals("short") || typeString.equals("java.lang.Short"))
            return true;
        if (typeString.equals("long") || typeString.equals("java.lang.Long"))
            return true;
        if (typeString.equals("char"))
            return true;
        if (typeString.equals("float") || typeString.equals("java.lang.Float"))
            return true;

        return false;
    }

    /**
     * Determine whether the types of the two objects are the same. In the basic type, E.g. Long == long
     *
     * @param type1
     * @param type2
     * @return
     */

    public static boolean isSameType(Type type1, Type type2) {
        String type1Str = type1.toString().toLowerCase();
        String type2Str = type2.toString().toLowerCase();

        if (type1Str.equals(type2Str))
            return true;
        if (!Utils.isBasicType(type1) | Utils.isBasicType(type2))
            return false;
        return type1Str.contains(type2Str) | type2Str.contains(type1Str);
    }

    public static boolean listEqual(List a, List b) {
        if (a.size() != b.size()) return false;
        for (int ind = 0; ind < a.size(); ind++) {
            if (a.get(ind) != b.get(ind)) return false;
        }
        return true;
    }


    /**
     * Determine whether a contains b, consider the forward order relationship
     *
     * @param a
     * @param b
     * @return
     */

    public static boolean listContains(List a, List b) {
        if (a.size() < b.size()) return false;

        int lastIndex = -1;
        for (int ind = 0; ind < b.size(); ind++) {
            int tmpIndex = a.indexOf(b.get(ind));
            if (tmpIndex == -1 || tmpIndex < lastIndex)
                return false;
            lastIndex = tmpIndex;
        }
        return true;
    }

    /**
     * Determine whether a contains b, consider the reverse order relationship
     *
     * @param a a,b,c
     * @param b d,b,c
     * @return
     */
    public static boolean isSubRevList(List a, List b) {
        if (a.size() < b.size()) return false;
        int bLen = b.size(), aLen = a.size();
        for (int ind = 0; ind < bLen; ind++) {
            if (!a.get(aLen - ind - 1).equals(b.get(bLen - ind - 1)))
                return false;
        }
        return true;
    }

    /**
     * Determine whether a is a sub-List of b
     *
     * @param a
     * @param b
     * @return
     */
    public static boolean isSubList(List a, List b) {
        if (a.size() > b.size()) return false;
        for (int ind = 0; ind < a.size(); ind++) {
            if (!a.get(ind).equals(b.get(ind)))
                return false;
        }
        return true;
    }

    public static int getCallStacksDeviation(List a, List b) {
        int index = 0;
        int compareMax = a.size() > b.size() ? b.size() : a.size();

        for (; index < compareMax; index++) {
            if (a.get(index) != b.get(index))
                break;
        }

        return a.size() - index;
    }

    public static boolean isEqual(Object value1, Object value2) {
        if (value1 == null & value2 == null)
            return true;
        if (value1 == null & value2 != null)
            return false;
        if (value1 != null & value2 == null)
            return false;

        if (value1.equals(value2))
            return true;

        if (value1 instanceof FieldRef & value2 instanceof FieldRef) {
            if (((FieldRef) value1).getField().equals(((FieldRef) value2).getField()))
                return true;
        }
        if (value1 instanceof ParameterRef & value2 instanceof ParameterRef) {
            if (((ParameterRef) value1).getIndex() == ((ParameterRef) value2).getIndex())
                return true;
        }

        return false;
    }

    /**
     * Determine whether the value is contaminated
     *
     * @param value
     * @param taints
     * @return
     */
    public static boolean isTainted(Value value, HashSet<Taint> taints) {
        if (value == null)
            return false;
        for (Taint taint : taints) {
            if (taint.object.equals(value))
                return true;
        }
        return false;
    }

    public static boolean isCompleteTainted(Value value, HashSet<Taint> taints) {
        if (value == null)
            return false;
        for (Taint taint : taints) {
            if (taint.object.equals(value) && taint.accessPath.isEmpty()) {
                return true;
            }
        }
        return false;
    }

    /**
     * will
     *
     * @param descriptor
     * @param value
     * @return
     */
    public static boolean isTaintedOrGen(MethodDescriptor descriptor, Value value) {
        if (value == null)
            return false;
        if (descriptor.tempGeneratedObjs.contains(value))
            return true;
        for (Taint taint : descriptor.taints) {
            if (taint.object.equals(value))
                return true;
        }

        return false;
    }

    public static boolean isTaintedInnerClzMethodCall(MethodDescriptor descriptor,
                                                      Value thisValue,
                                                      InvokeExpr invokeExpr) {
        SootClass thisValueClz = Utils.toSootClass(thisValue.getType());
        if (!thisValueClz.isInnerClass())
            return false;

        SootClass outerClz = thisValueClz.getOuterClass();
        for (Value argValue : invokeExpr.getArgs()) {
            SootClass argClz = Utils.toSootClass(argValue.getType());
            if (!argClz.equals(outerClz)) continue;
            if (Utils.isTainted(argValue, descriptor.taints)) { // If uncontrollable, return false
                return true;
            }

            return false;
        }
        return false;
    }

    /**
     * According to the taint relationship recorded in fields-taints, if the source is an input parameter, it indicates that it depends on the input parameter of the head method.
     * (1) Find each parameter of the calling method (including this)
     * (2) Only find the tainted parameters
     * (3) Record the case where the corresponding source is parameter (indicating that it depends on the input parameter of the head method)
     *
     * @param descriptor
     * @param value
     * @return
     */
    public static HashSet<Integer> getEndToHeadTaintsCon(MethodDescriptor descriptor, Value value) {
        HashSet<Integer> tmpTaintParams = new HashSet<>();
        HashSet<SourceNode> sourceNodes = descriptor.sourcesTaintGraph.matchTaintedSources(value);
        for (SourceNode sourceNode : sourceNodes) {
            if (sourceNode.isParameter())
                tmpTaintParams.add(sourceNode.ind);
            else if (sourceNode.isFieldOfParameter()) {
                tmpTaintParams.add(sourceNode.ind);
            }
        }
        return tmpTaintParams;
    }

    public static boolean hashSameElement(Set a, Set b) {
        if (a == null | b == null)
            return false;
        for (Object object : a) {
            if (b.contains(object))
                return true;
        }
        return false;
    }

    public static boolean hashSameElement(Collection a, Collection b) {
        if (a == null | b == null)
            return false;
        for (Object object : a) {
            if (b.contains(object))
                return true;
        }
        return false;
    }

    public static boolean hashSameElement(List a, List b) {
        if (a == null | b == null)
            return false;

        for (int ind = 0; ind < a.size(); ind++) {
            if (b.contains(a.get(ind)))
                return true;
        }
        return false;
    }

    public static boolean isJdkInnerMethod(SootMethod sootMethod) {
        String className = sootMethod.getDeclaringClass().getName();
        if (className.startsWith("java."))
            return true;
        if (className.startsWith("javax."))
            return true;
        if (className.startsWith("jdk."))
            return true;
        if (className.startsWith("com.sun"))
            return true;
        if (className.startsWith("sun."))
            return true;
        if (className.startsWith("com.oracle.deploy")
                | className.startsWith("com.oracle.jrockit"))
            return true;
        if (className.startsWith("sun.net.spi.nameservice.dns"))
            return true;
        if (className.startsWith("oracle.jrockit"))
            return true;
        if (className.startsWith("javafx"))
            return true;
        if (className.startsWith("netscape"))
            return true;
        if (className.startsWith("sun.security"))
            return true;
        if (className.startsWith("apple"))
            return true;
        if (className.startsWith("org.ietf")
                | className.startsWith("org.jcp")
                | className.startsWith("org.omg")
                | className.startsWith("org.w3c.dom")
                | className.startsWith("org.xml.sax"))
            return true;
        return false;
    }

    /**
     * According to the type declaration of field, extract the element type of the Array type object
     *
     * @param typeSignature
     * @return
     */
    public static LinkedList<String> extractArrayElementType(String typeSignature) {
        LinkedList<String> extractedTypes = new LinkedList<>();
        String pattern = "L(.*?);"; // Match the content of a string starting with L and ending with;
        Pattern r = Pattern.compile(pattern);
        Matcher m = r.matcher(typeSignature);

        while (m.find()) {
            String type = m.group(1);
            extractedTypes.add(type);
        }

        return extractedTypes;
    }

    public static SootClass getRealClass(SootMethod sootMethod) {
        MethodDescriptor descriptor = BasicDataContainer.getOrCreateDescriptor(sootMethod);
        return descriptor.getCurrentClass();
    }

    public static SootMethod getPreObjSootMethod(LinkedList<SootMethod> callStack, SootMethod curMtd) {
        int curIndex = callStack.indexOf(curMtd);
        curIndex = curIndex != -1 ? curIndex : callStack.size() - 1;
        for (int index = curIndex; index >= 0; index--) {
            if (callStack.get(index).isStatic())
                continue;
            return callStack.get(index);
        }
        return null;
    }

    /**
     * Use TreeMap to sort the elements in unsortedMap and output the outNum of the top ranking
     *
     * @param unsortedMap
     * @param outNum
     * @return
     */
    public static LinkedList getSortedElement(HashMap unsortedMap, int outNum) {
        LinkedList out = new LinkedList<>();
        TreeMap treeMap = new TreeMap<>();
        for (Object key : unsortedMap.keySet()) {
            treeMap.put(key, unsortedMap.get(key));
        }

        int count = 0;
        for (Object key : treeMap.keySet()) {
            if (count >= outNum)
                break;
            out.add(treeMap.get(key));
            count++;
        }

        return out;
    }

    public static SootMethod getMethod(LinkedList<SootMethod> chain, String subMethodSig, int index) {
        int count = 0;
        for (SootMethod sootMethod : chain) {
            if (!sootMethod.getSubSignature().equals(subMethodSig)) continue;
            count++;
            if (count == index) return sootMethod;
        }
        return null;
    }

    public static boolean inList(List a, Set superList) {
        for (Object o : a) {
            if (superList.contains(o))
                return true;
        }
        return false;
    }

    public static boolean isElementInSet(String element, Set<String> strSet) {
        for (String str : strSet) {
            if (str.contains(element)) return true;
        }
        return false;
    }

    public static boolean isElementContainsSet(Set<String> strSet, String element) {
        for (String str : strSet) {
            if (element.contains(str)) return true;
        }
        return false;
    }

    public static String getLastIndexSubStr(String str, String delimiter) {
        int lastIndex = str.lastIndexOf(delimiter);
        if (lastIndex != -1) {
            return str.substring(lastIndex + 1);
        }
        return str;
    }

    public static <T> Set<T> getRandomElements(HashSet<T> set, int n) {
        List<T> list = new ArrayList<>(set);
        Collections.shuffle(list); // Use Collections.shuffle to randomly disrupt the list
        return new HashSet<>(list.subList(0, Math.min(n, list.size())));
    }


    /**
     * Output time difference
     *
     * @param curTime   current time
     * @param startTime start time
     */
    public static void printTimeConsume(long curTime, long startTime) {
        long timeConsume = curTime - startTime;
        long seconds = (timeConsume) / 1000; // Convert to seconds
        long minutes = seconds / 60; // Convert to minutes
        long hours = minutes / 60;

log.info("Program run time: " + hours + " h : " + (minutes - hours * 60) + " m: " + (seconds - minutes * 60) + " s");
    }
}
