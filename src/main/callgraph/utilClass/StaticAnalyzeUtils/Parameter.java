package callgraph.utilClass.StaticAnalyzeUtils;

import callgraph.cfg.CFG;
import callgraph.cfg.Node;
import callgraph.dataflow.DataFlow;
import callgraph.dataflow.Event;
import lombok.extern.slf4j.Slf4j;
import soot.*;
import soot.jimple.*;
import jdd.tranModel.TransformableNode;

import java.util.*;

/**
 * Basic static analysis capabilities
 */
@Slf4j
public class Parameter {

    public static HashMap<Integer, Value> getParametersLocalValues(SootMethod sootMethod){
        CFG cfg = new CFG(sootMethod, true);
        cfg.buildCFG();
        return getParametersLocalValues(cfg);
    }

    /**
     * Get the correspondence between formal parameters/this and local variables in the current method
     * And keep this relationship in descriptor.paramIdMapLocalValue
     * The return value is -1: the value corresponding to this
     */
    public static HashMap<Integer, Value> getParametersLocalValues(CFG cfg){
        HashMap<Integer, Value> paramMapValue = new HashMap<>();
        for(Node node : cfg.allNodes.values()){
            Integer paramInd = tryGetParamIdentifiedInUnit(node.unit);
            if(paramInd != null) {
                paramMapValue.put(paramInd, node.unit.getDefBoxes().get(0).getValue());
            }
        }
        return paramMapValue;
    }
    public static HashMap<Integer, List<Event>> getParametersMapTaintedEvent(CFG cfg, SootMethod sootMethod){
        int paramCount = sootMethod.getParameterCount();
        HashMap<Integer, List<Event>> paramMapTaintedEvent = new HashMap<>();
        Node node = cfg.headNode;
        for(int i = 0; i < paramCount + 1; i++){
//            log.info("---------------------------");
//            log.info(node.unit);
            Integer paramInd = tryGetParamIdentifiedInUnit(node.unit);
            if(paramInd == null) {
                if(node.successorNodes.size() == 0) break;
                node = node.successorNodes.iterator().next();
                continue;
            }
            if(paramInd == -1) {
// "this"
                if(node.successorNodes.size() == 0) break;
                node = node.successorNodes.iterator().next();
                continue;
            }
// affected
            ArrayList<Event> taintedEvent = new ArrayList<>();
            HashMap<Node, ValueBox> tmp = new HashMap<>();
            tmp.put(node, node.unit.getDefBoxes().get(0));
            for(Map.Entry<Node, ValueBox> entry : DataFlow.findAllUnitAndValueAffected(tmp).entrySet()){
//                log.info(entry.getKey());
//                log.info(entry.getValue());
                Event event = new Event(entry.getKey(), entry.getValue());
                taintedEvent.add(event);
            }
// Direct Quote
//            List<Event> taintedEvent = DataFlow.getValueBoxRefEvents(node.unit.getDefBoxes().get(0), node);
            paramMapTaintedEvent.put(paramInd, taintedEvent);
            if(node.successorNodes.size() == 0) break;
            node = node.successorNodes.iterator().next();
        }
        return paramMapTaintedEvent;
    }

    public static HashMap<Integer, List<Event>> getParametersMapDirectRefEvent(CFG cfg, SootMethod sootMethod){
        HashMap<Integer, List<Event>> paramMapTaintedEvent = new HashMap<>();
        for(Node node : cfg.allNodes.values()){
            Integer paramInd = tryGetParamIdentifiedInUnit(node.unit);
            if(paramInd != null) {
                List<Event> taintedEvent = DataFlow.getValueBoxRefEvents(node.unit.getDefBoxes().get(0), node);
                paramMapTaintedEvent.put(paramInd, taintedEvent);
            }

        }
        return paramMapTaintedEvent;
    }

    /**
     * Given a Unit:
     * 1. Determine that it is IdentifyStmt
     * 2. Determine whether its DefBox comes from the method formal parameters or this, if so, return the corresponding index
     * @param unit
     * @return
     */
    public static Integer tryGetParamIdentifiedInUnit(Unit unit){
        /* return:
              -1 : this
         */
        if(unit instanceof IdentityStmt){
            if(unit.getUseBoxes().size() > 0){
                String s = unit.getUseBoxes().get(0).getValue().toString();
                String[] sp = s.split("[@:]");
                if(sp.length >= 3 && sp[1].contains("parameter")){
                    try{
                        return Integer.parseInt(sp[1].substring(sp[1].length() - 1));
                    } catch (Exception e){
log.warn("Unable to obtain unit" + unit + "This/formal parameter correspondence, return null");
                        return null;
                    }
                }
                else if(sp.length >= 3 && sp[1].contains("this")) return -1;
            }
        }
        return null;
    }

    /**
     * Given Node, get the ValueBox of the method parameter specified in unit.
     * @param node
     * @param argIndex
     * @return
     */
    public static ValueBox getArgValueBox(Node node, int argIndex){
        Stmt crtStmt = (Stmt) node.unit;
        if(!crtStmt.containsInvokeExpr()) { return null; }
        InvokeExpr crtIE = crtStmt.getInvokeExpr();
        if(crtIE.getArgCount() < argIndex + 1) { return null; }
        return crtIE.getArgBox(argIndex);
    }

    public static HashSet<ValueBox> getAllArgValueBoxes(Node node){
        HashSet<ValueBox> ret = new HashSet<>();
        if(!((Stmt) node.unit).containsInvokeExpr()) return ret;
        for(int ind = 0 ; ind < ((Stmt) node.unit).getInvokeExpr().getArgCount(); ind++){
            ValueBox vb = ((Stmt) node.unit).getInvokeExpr().getArgBox(ind);
            ret.add(vb);
        }
        return ret;
    }

    public static int getArgIndexByValueBox(Node node, ValueBox valueBox){
        if(!((Stmt) node.unit).containsInvokeExpr()) return -1;
        for(int ind = 0 ; ind < ((Stmt) node.unit).getInvokeExpr().getArgCount(); ind++){
            ValueBox vb = ((Stmt) node.unit).getInvokeExpr().getArgBox(ind);
            if(vb.equals(valueBox)) return ind;
        }
        return -1;
    }

    public static Node getParamTransferNode(CFG cfg, SootMethod sootMethod, int index){
        int paramCount = sootMethod.getParameterCount();
        Node node = cfg.headNode;
        for(int i = 0; i < paramCount + 1; i++){
//            log.info("---------------------------");
//            log.info(node.unit);
            Integer paramInd = tryGetParamIdentifiedInUnit(node.unit);
            if(paramInd == null) {
                if(node.successorNodes.size() == 0) break;
                node = node.successorNodes.iterator().next();
                continue;
            }
            if(paramInd == index) {
                return node;
            }

            if(node.successorNodes.size() == 0) break;
            node = node.successorNodes.iterator().next();
        }
        return null;
    }

// eg. O.method->O

    /**
     * Gel the valueBox of the node
     * @param node
     * @return
     */
    public static ValueBox getThisValueBox(Node node){
        if (!((Stmt) node.unit).containsInvokeExpr())
            return null;

        InvokeExpr invokeExpr = ((Stmt) node.unit).getInvokeExpr();
        if(invokeExpr instanceof VirtualInvokeExpr || invokeExpr instanceof InterfaceInvokeExpr) {
            InstanceInvokeExpr instanceInvokeExpr = (InstanceInvokeExpr) invokeExpr;
            return instanceInvokeExpr.getBaseBox();
        }
// hack
        ValueBox thisBox = null;
        HashSet<ValueBox> argBoxes = getAllArgValueBoxes(node);
        //check if the argument is not a use box then it is a value box
        for (ValueBox valueBox:invokeExpr.getUseBoxes()){
            if(!argBoxes.contains(valueBox)) thisBox = valueBox;
        }
        return thisBox;
    }

// eg. O.method->O
    public static ValueBox getThisValueBox(Stmt stmt){
        InvokeExpr invokeExpr = stmt.getInvokeExpr();
        if(invokeExpr instanceof InstanceInvokeExpr) {
            InstanceInvokeExpr instanceInvokeExpr = (InstanceInvokeExpr) invokeExpr;
            return instanceInvokeExpr.getBaseBox();
        }
        return null;
    }

    /**
     * Get the object value returned by the function call
     * eg. r1=r0.method -> r1
     * @param node
     * @return If the provided Unit is an assignment statement, then return the value assigned by the function call return value, otherwise return null
     */
    public static ValueBox getReturnedValueBox(Node node){
        if (node.unit instanceof AssignStmt){
            return ((AssignStmt)node.unit).getLeftOpBox();
        }
        return null;
    }

    public static Value getReturnedValue(Node node){
        if (node.unit instanceof AssignStmt){
            return ((AssignStmt)node.unit).getLeftOp();
        }
        return null;
    }

    public static Value getReturnedValue(Stmt stmt){
        if (stmt instanceof AssignStmt){
            return ((AssignStmt)stmt).getLeftOp();
        }
        return null;
    }

    public static ValueBox getReturnedValueBox(Stmt stmt){
        if (stmt instanceof AssignStmt){
            return ((AssignStmt) stmt).getLeftOpBox();
        }

        return null;
    }

// Find the actual value corresponding to a static field constant
    public static Value getStaticFieldValue(FieldRef fieldRef){
        SootClass sootClass = fieldRef.getFieldRef().declaringClass();

        if (sootClass.resolvingLevel() < 3) return null;
        SootMethod clint = sootClass.getMethodByNameUnsafe("<clinit>");
        if (clint != null){
            for (Unit unit: clint.retrieveActiveBody().getUnits()){

                if ((Stmt)unit instanceof AssignStmt){
                    AssignStmt assignStmt = (AssignStmt)unit;
                    Value left = assignStmt.getLeftOp();
                    Value right = assignStmt.getRightOp();

if (left instanceof FieldRef) { // Check whether it is field, if it is yes, extract the corresponding value
                        if (((FieldRef) left).toString().equals(fieldRef.toString())) {
                            return right;
                        }
                    }
                }
            }
        }
        return null;
    }

    /**
     * Specify type to get the corresponding parameter ValueBox in the calling function in the calling statement invokeExpr
     * @param invokeExpr
     * @param type
     * @return If not, return null
     */
    public static ValueBox getArgByType(InvokeExpr invokeExpr, String type){
        ValueBox testArg = null;
// The content of the class to be created needs to be controllable
        for (int ind = 0; ind < invokeExpr.getArgCount(); ind++){
            ValueBox arg = invokeExpr.getArgBox(ind);
            if (arg.getValue().getType().toString().equals(type))
                testArg = arg;
        }

        return testArg;
    }

    public static Integer getArgByType(SootMethod sootMethod, String type){
        Integer testArgIndex = null;
// The content of the class to be created needs to be controllable
        for (int ind = 0; ind < sootMethod.getParameterCount(); ind++){
            Type argType = sootMethod.getParameterType(ind);
            if (argType.toString().equals(type))
                testArgIndex = ind;
        }

        return testArgIndex;
    }

    public static Integer getArgIndexByValue(InvokeExpr invokeExpr,
                                             TransformableNode tfNode,
                                             Value argValue){
        if (argValue == null)
            return null;
        ValueBox thisValueBox = Parameter.getThisValueBox(tfNode.node);
        if (thisValueBox != null && thisValueBox.getValue().equals(argValue))
            return -1;

        Value retValue = Parameter.getReturnedValue(tfNode.node);
        if (retValue != null && retValue.equals(argValue))
            return -2;

        for (int ind = 0; ind < invokeExpr.getArgCount(); ind++){
            ValueBox arg = invokeExpr.getArgBox(ind);
            if (arg.getValue().equals(argValue))
                return ind;
        }

        return null;
    }

    public static Integer getArgIndexByType(SootMethod sootMethod, String type){
        for (int ind = 0; ind < sootMethod.getParameterCount(); ind++){
            if (sootMethod.getParameterType(ind).toString().equals(type))
                return ind;
        }
        return null;
    }

// What parameter is the analysis
    public static Integer getParamIndex(String sig){
        String[] sp = sig.split("[@:]");
        if (sp.length >= 3 && sp[1].contains("parameter")){
            try {
                return Integer.parseInt(sp[1].substring(sp[1].length()-1));
            } catch (NumberFormatException e) {
                throw new RuntimeException(e);
            }
        }else if (sp.length >= 3 && sp[1].contains("this")) return -1;

        return null;
    }
}
