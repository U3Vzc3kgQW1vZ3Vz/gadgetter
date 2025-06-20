package jdd.tranModel;

import jdd.PointToAnalyze.pointer.Pointer;
import java.cfg.CFG;
import java.cfg.Node;
import jdd.container.BasicDataContainer;
import jdd.dataflow.node.MethodDescriptor;
import jdd.dataflow.node.SourceNode;
import soot.*;
import soot.jimple.IfStmt;
import soot.jimple.InvokeExpr;
import soot.jimple.Stmt;
import soot.jimple.toolkits.callgraph.Edge;
import jdd.tranModel.Taint.Taint;
import java.util.StaticAnalyzeUtils.Parameter;
import jdd.util.Utils;

import javax.xml.transform.Source;
import java.util.*;

/**
 * 用于封装cfg.Node
 */
public class TransformableNode extends Transformable{
    public Node node;
    public SootMethod method;
    public HashSet<TransformableNode> successors = new HashSet<>();
    public HashSet<TransformableNode> precursors = new HashSet<>();

    public Context context = new Context();

    public SootMethod addMethod = null;

public boolean isCycle = false; // Record whether it is a loop statement. If it is a loop statement such as For, the error problem of conditional branch records may occur. Whether it is a loop statement when building topological sorting

    public int[] ruleFlag = new int[10];
// Used to identify whether the current Unit is a Sink. If it is a Sink, then the subsequent Unit will be abandoned.
// ToDo: It may cause subsequent sinks to be missed
    public boolean exec = true;
// for path sensitivity analysis
    public HashSet<Integer> path_record = new HashSet<>();

    public boolean needInputTaintedParamFlush = true;

    public static HashMap<Integer, TransformableNode> ifStmtHashMap = new HashMap<>();


    public TransformableNode(Node node, SootMethod sootMethod){
        this.node = node;
        this.method = sootMethod;
        this.context.method = sootMethod;
        this.context.sootClass = sootMethod.getDeclaringClass();
    }

    public TransformableNode(Node node){
        this.node = node;
    }

    public TransformableNode(){
    }



    public boolean containsInvoke(){
        return ((Stmt) node.unit).containsInvokeExpr();
    }

    public IfStmt getIfStmt(){
        IfStmt ifStmt = null;

        if (((Stmt)this.node.unit) instanceof IfStmt) {
            ifStmt = (IfStmt) this.node.unit;
        }
        return ifStmt;
    }

    /**
     * 用于判断当前这条Jimple方法调用语句存在的对外函数（即多态的情况）有哪些，并：
     * 1、将污点传播到方法调用中去
     * 2、处理soot.jimple.toolkits.callgraph.Edge#tgt()在匿名内部类中的方法链接异常
     * @return
     */
    public HashSet<SootMethod> invokeMethods(MethodDescriptor descriptor){

        HashSet<SootMethod> ret = new HashSet<>();
        if(!containsInvoke()) return ret;
// Get the edge out, return directly without the edge out
        Iterator<Edge> edgeIterator = BasicDataContainer.cg.callGraph.edgesOutOf(node.unit);
        if (edgeIterator == null)
            return ret;

        int index = 0;
// Process these derived methods and use connectParameters to pass stain information.
        while (edgeIterator.hasNext()) {
            index++;
            SootMethod invokeMethod = edgeIterator.next().tgt();
            if (index>1) { connectParameters(invokeMethod, descriptor); }
            ret.add(invokeMethod);
        }
        if (ret.size() == 0 && needConnectParams()) {
            ret = findExactMethod(descriptor);
        }
        return ret;
    }

    @Override
    public String toString(){
        return this.node.unit.toString();
    }

    /**
     * 返回Jimple对应unit的InvokeExpr
     * @return
     */
    public InvokeExpr getUnitInvokeExpr(){
        if (this.containsInvoke()){
            return ((Stmt)node.unit).getInvokeExpr();
        }
        return null;
    }

    @Override
    public int hashCode() {
        return this.node.toString().hashCode();
    }

    public boolean needConnectParams(){
        InvokeExpr invokeExpr = this.getUnitInvokeExpr();
        SootMethod currentMethod = invokeExpr.getMethod();
        SootClass classOfCM = currentMethod.getDeclaringClass();

        if (classOfCM.getName().equals("java.security.AccessController")){
            return true;
        }
        return false;
    }

    public HashSet<SootMethod> findExactMethod(MethodDescriptor descriptor){

        HashSet<SootMethod> res = new HashSet<>();

        InvokeExpr invokeExpr = this.getUnitInvokeExpr();
        SootMethod currentMethod = invokeExpr.getMethod();

        Integer index = null;
// Determine whether the parameters of this method contain java.security.PrivilegedAction, and if there is one, get its parameter location.
        for (int ind=0; ind< currentMethod.getParameterCount(); ind++){
            Type type = currentMethod.getParameterType(ind);
            if (type.toString().equals("java.security.PrivilegedAction")
                    || type.toString().equals("java.security.PrivilegedAction")
                    || type.toString().equals("java.security.PrivilegedExceptionAction")) {
                index = ind;
                break;
            }
        }
// Get all methods in the java.security.PrivilegedAction class (a series of classes summarized by expert experience)
// Get the run method inside and pollute its variables
        if (index != null){
            Value arg = invokeExpr.getArg(index);
            String argTypeName = arg.getType().toString();
            SootClass sootClass = Scene.v().getSootClassUnsafe(argTypeName);
            if (sootClass != null){
// ToDo: Why not directly specify a specific method name? sootClass.getMethod();
                List<SootMethod> sootMethods = sootClass.getMethods();
                for (SootMethod sootMethod: sootMethods){
if (sootMethod.getName().equals("run") ){ //& !sootMethod.getReturnType().toString().equals("java.lang.Object")
                        res.add(sootMethod);
                        connectParameters(sootMethod, descriptor);
                    }
                }
            }
        }

        return res;

    }


    public void connectParameters(SootMethod invokedMethod, MethodDescriptor descriptor){
        if (!needConnectParams())
            return;

        InvokeExpr invokeExpr = this.getUnitInvokeExpr();
// Because the proxy method cannot be directly connected by cg, there is no need to consider it
        MethodDescriptor invokedDescriptor = BasicDataContainer.getOrCreateDescriptor(invokedMethod);

        if (invokedDescriptor == null)
            return;
        if (invokedDescriptor.cfg == null){
            CFG cfg = new CFG(invokedMethod, true);
            cfg.buildCFG();
            invokedDescriptor.cfg = cfg;
        }

        invokedDescriptor.paramIdMapLocalValue = Parameter.getParametersLocalValues(invokedDescriptor.cfg);

        List<Taint> taintRecords = new LinkedList<>();
// traverse each incoming parameter of the called method. If the incoming parameter is equivalent to an existing taint parameter, then note this taint
        for (Value arg: invokeExpr.getArgs()){
            for (Taint taint:descriptor.taints)
                if (taint.object.equals(arg))
                    taintRecords.add(taint);
        }
// If the incoming registry is contaminated and the method type is the same as the subsequent call, it will be contaminated.
        for (Taint taint: taintRecords){
            if (taint.object.getType().toString().equals(invokedMethod.getDeclaringClass().getName())){
                invokedDescriptor.inputParamMapTaints.put(-1,descriptor.getAllTaintsAboutThisValue(taint.object));
                if (descriptor.pointTable.contains(taint)){
                    invokedDescriptor.paramValInfo.put(-1,descriptor.pointTable.getPointer(taint));
                }
                needInputTaintedParamFlush = false;
            }
        }
    }

    @Override
    public boolean equals(Object obj) {
        if(!(obj instanceof TransformableNode)) return false;
        return this.node.equals(((TransformableNode) obj).node);
    }

// Remove records with positive and negative values, that is, extract the path records that really need related
    public void extractPathRecords(){
        HashSet<Integer> remove = new HashSet<>();
        for (Integer hashCode : path_record){
            if (path_record.contains(-hashCode))
                remove.add(hashCode);
        }
        for (Integer hashCode: remove){
            path_record.remove(hashCode);
            path_record.remove(-hashCode);
        }
    }

}
