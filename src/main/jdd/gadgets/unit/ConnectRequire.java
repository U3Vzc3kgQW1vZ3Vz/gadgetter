package jdd.gadgets.unit;

import jdd.container.BasicDataContainer;
import jdd.container.FragmentsContainer;
import soot.SootMethod;

import java.util.HashMap;
import java.util.HashSet;

public class ConnectRequire {
public HashSet<SootMethod> preLinkableMethods = new HashSet<>(); // Fragment jump condition
public HashSet<HashSet<Integer>> paramsTaitRequire = null; // taint requirement
    public HashSet<Integer> condSet = new HashSet<>();

    /** Other link conditions */
// Currently consider two types: method name limitation/type limitation to which the method belongs
    public HashMap<String, HashSet<String>> dynamicProxyLinkCheck = new HashMap<>();
    

// Record the splicing requirements of fragments that reflect splicing
// static(1) getter(1)/Interface(2)/any(0) non-parameter(0默认)/String(1)
    public String reflectionCheck = "010";

    public ConnectRequire(HashSet<HashSet<Integer>> paramsTaitRequire, HashSet<SootMethod> preLinkableMethods){
        dynamicProxyLinkCheck.put("MethodNameBlackList", new HashSet<>());
        dynamicProxyLinkCheck.put("MethodNameWhiteList", new HashSet<>());
        dynamicProxyLinkCheck.put("DecClassBlackList", new HashSet<>());
        dynamicProxyLinkCheck.put("DecClassWhiteList", new HashSet<>());
        this.paramsTaitRequire = paramsTaitRequire;
        this.preLinkableMethods = preLinkableMethods;
    }

    public ConnectRequire(HashSet<SootMethod> preLinkableMethods){
        dynamicProxyLinkCheck.put("MethodNameBlackList", new HashSet<>());
        dynamicProxyLinkCheck.put("MethodNameWhiteList", new HashSet<>());
        dynamicProxyLinkCheck.put("DecClassBlackList", new HashSet<>());
        dynamicProxyLinkCheck.put("DecClassWhiteList", new HashSet<>());
        this.preLinkableMethods = preLinkableMethods;
    }
}
