package jdd.container;

import jdd.tranModel.TransformableNode;
import callgraph.cg.CG;
import jdd.config.SootConfig;
import jdd.dataflow.node.MethodDescriptor;
import jdd.markers.Stage;
import jdd.rules.sinks.ClassLoaderCheckRule;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import jdd.util.ClassRelationshipUtils;
import jdd.util.Utils;

import java.util.*;
/**
 * Store some basic information that may be used globally
 */
public class BasicDataContainer {
    public static CG cg = null;
    public static boolean openDebugMode = false;
public static boolean needSerializable = true; // Determine whether serialization check is enabled
public static boolean openDynamicProxyDetect = false; // Determine whether to start the proxy detection
    public static boolean isEntryPolluteSelect;
    public static int stackLenLimitNum = 5;
    public static int polyLenLimit = 3;
    public static int methodLimitNum = 5;
    public static int serializableInterceptLen = 3;
public static boolean hashCollisionModeSelect = true; // true: Case type A that does not consider hash collision (prone to false positives)
    public static int linkTimeLimit = 3;
    public static int chainLimit = 20;
    public static int stackDeviationLimit = 3;
    public static int stackLenLimitForFieldsCollection = 2;
    public static boolean openChainedSinkCheck = false;
    public static int interimFragmentToConClassLimit = 3;
    public static boolean gadgetParamsGenerate = false;
    public static boolean infosCollect = false;

    public static boolean openJoinRule = false;

    public static boolean openAliasAnalysis = true;
    public static boolean openPointerToAnalysis = true;

    public static Stage stage = Stage.OFF;

    public static HashMap<String, HashSet<String>> subClassSearchRecord = new HashMap<>();
    public static HashMap<String, SootClass> commonClassMap = new HashMap<>();
    public static HashMap<String, SootMethod> commonMtdMap = new HashMap<>();
    public static List<String> blackList = SootConfig.getBlackList();

// Access permissions for the method
    public static List<String> accessPermissions = Arrays.asList("public","protected","private");

    public static HashMap<SootMethod, MethodDescriptor> methodMapDescriptor = new HashMap<>();
    public static HashMap<Integer, TransformableNode> conditionTfNodesMap = new HashMap<>();
    public static int heuristicShortChainCutLen = 0;

    public static void reset(){
        BasicDataContainer.commonMtdMap = new HashMap<>();
        BasicDataContainer.commonClassMap = new HashMap<>();
        BasicDataContainer.subClassSearchRecord = new HashMap<>();

        resetState();

        RulesContainer.reset();
        FragmentsContainer.reset();
    }

    public static void init(){
        commonMtdMap.put("invokeHandler", Scene.v().getMethod("<java.lang.reflect.InvocationHandler: java.lang.Object invoke(java.lang.Object,java.lang.reflect.Method,java.lang.Object[])>"));
        commonClassMap.put("Map", Utils.toSootClass("java.util.Map"));
        commonClassMap.put("List", Utils.toSootClass("java.util.List"));
        commonClassMap.put("Entry", Utils.toSootClass("java.util.Map$Entry"));
        commonClassMap.put("Object", Utils.toSootClass("java.lang.Object"));
        BasicDataContainer.subClassSearchRecord.put("java.util.Map$Entry", ClassRelationshipUtils.getAllSubClasses(Collections.singletonList("java.util.Map$Entry")));
    }

    public static boolean inBlackList(SootMethod sootMethod){
        if (blackList.isEmpty())
            return false;
        String className = sootMethod.getDeclaringClass().getName();
        if (blackList.contains(className))
            return true;

        for (String black: blackList){
            if (className.startsWith(black))
                return true;
        }

        return false;
    }
    public static boolean inBlackList(SootClass sootClass){
        if (blackList.size() == 0)
            return false;
        String className = sootClass.getName();
        if (blackList.contains(className))
            return true;

        for (String black: blackList){
            if (className.startsWith(black))
                return true;
        }

        return false;
    }

    public static MethodDescriptor getOrCreateDescriptor(SootMethod sootMethod){
        if(methodMapDescriptor.containsKey(sootMethod)){
            return methodMapDescriptor.get(sootMethod);
        }else{
            MethodDescriptor methodDescriptor = new MethodDescriptor(sootMethod);
            methodDescriptor.isDynamicEntry = ClassRelationshipUtils.isDynamicMethod(sootMethod);
            methodMapDescriptor.put(sootMethod, methodDescriptor);
            return methodDescriptor;
        }
    }

    public static void resetMethodDescriptorState(){
        if(!methodMapDescriptor.isEmpty()) { methodMapDescriptor.clear(); }
        else { methodMapDescriptor = new HashMap<>(); }
    }

    public static void resetState(){
        resetMethodDescriptorState();
        ClassLoaderCheckRule.callStacksRecord.clear();
    }

    public static boolean isValidHeadOfObjectMethod(SootMethod sootMethod){
        if (!sootMethod.getDeclaringClass().getName().equals("java.lang.Object"))
            return false;

        if (sootMethod.getSubSignature().equals("java.lang.String toString()")
                | sootMethod.getSubSignature().equals("boolean equals(java.lang.Object)")
                | sootMethod.getSubSignature().equals("int hashCode()"))
            return true;

        return false;
    }
}
