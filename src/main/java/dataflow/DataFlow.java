package java.dataflow;

import java.cfg.Node;
import java.cfg.Path;
import soot.Unit;
import soot.Value;
import soot.ValueBox;
import soot.jimple.*;
import java.util.StringUtil;

import java.util.*;

/**
 * Tools that provide data flow analysis functions
 *
 * @since 2.0
 */
public class DataFlow {



    public static boolean isValueUsedInUnit(Unit unit, Value value) {
        List<String> usedValue = new ArrayList<>();
        for (ValueBox useBox : unit.getUseBoxes()) {
            usedValue.add(useBox.getValue().toString());
        }
        return usedValue.contains(value.toString());
    }

    public static boolean isValueDefinedInUnit(Unit unit, Value value) {
        List<String> definedValue = new ArrayList<>();
        for (ValueBox defBox : unit.getDefBoxes()) {
            definedValue.add(defBox.getValue().toString());
        }
        return definedValue.contains(value.toString());
    }

    public static ValueBox findValueBoxByValue(Unit unit, Value value) {
        for (ValueBox valueBox : unit.getUseAndDefBoxes())
            if (valueBox.getValue().toString().equals(value.toString()))
                return valueBox;
        return null;
    }


    public static void addNewEvent(EventQueue waitForProcessEvent, HashSet<Event> processedEvent, Node node, ValueBox valueBox) {
        Event newEvent = new Event(node, valueBox);
        if (processedEvent.contains(newEvent))
            return;
        waitForProcessEvent.add(newEvent);
    }

    public static void doWithInputAsLeftValueOrRef(Node node, ValueBox valueBox, EventQueue waitForProcessEvent, HashSet<Event> processedEvent, HashMap<Node, ValueBox> result) {
//Troubleshooting the case where the polluting variable is: rvalue or the call statement refers to the object, that is, a=b or a=b.C()
        if (isValueUsedInUnit(node.unit, valueBox.getValue()) && !isValueDefinedInUnit(node.unit, valueBox.getValue())) {
            result.put(node, findValueBoxByValue(node.unit, valueBox.getValue()));
if (!((Stmt) node.unit).containsInvokeExpr() && node.unit.getDefBoxes().size() != 0) {//If the polluting variable is an lvalue, it is not a call statement
                addNewEvent(waitForProcessEvent, processedEvent, node, node.unit.getDefBoxes().get(0));
            }
if(((Stmt) node.unit).containsInvokeExpr()&&!node.isExpand){//If the statement here is a call statement and is not expanded, we assume here that as long as the polluted variable is used in the lvalue, the statement here is polluted
                if(node.unit.getDefBoxes().size()!=0){
                    addNewEvent(waitForProcessEvent,processedEvent,node,node.unit.getDefBoxes().get(0));
                }
            }


        }
    }


    public static void doWithInputAsParam(Node node, Node beginNode,ValueBox valueBox, EventQueue waitForProcessEvent, HashSet<Event> processedEvent) {
int index = ((Stmt) node.unit).getInvokeExpr().getArgs().indexOf(valueBox.getValue());//Find the index value of the variable used
        if (index >= 0) {
Node paramNode = dnfFind(beginNode, index);//Find the parameters of the infection
            assert paramNode != null;
            addNewEvent(waitForProcessEvent, processedEvent, paramNode, paramNode.unit.getDefBoxes().get(0));
        }
    }

    public static void doWithInputAsRet(Node node, Node succor, ValueBox valueBox, EventQueue waitForProcessEvent, HashSet<Event> processedEvent, HashMap<Node, ValueBox> result) {
if (((Stmt) node.unit) instanceof ReturnStmt || ((Stmt) node.unit) instanceof RetStmt) {//If the previous is a return value statement
if (isValueUsedInUnit(node.unit, valueBox.getValue())) {//If the return value is polluted
                for (Node su : succor.successorNodes) {
                    for (Node pre : su.originPreNode) {
                        if (pre.unit.getDefBoxes().size() != 0) {
                            result.put(pre, findValueBoxByValue(pre.unit, pre.unit.getDefBoxes().get(0).getValue()));
                            addNewEvent(waitForProcessEvent, processedEvent, pre, pre.unit.getDefBoxes().get(0));
                        }
                    }
                }
            }
        }
    }

    public static void doWithInputAsThis(Node node, EventQueue waitForProcessEvent, HashSet<Event> processedEvent, HashMap<Node, ValueBox> result) {
        for (Node succor : node.successorNodes) {
            for (Node pre : succor.originPreNode) {
                addNewEvent(waitForProcessEvent, processedEvent, succor, ((Stmt) pre.unit).getInvokeExpr().getUseBoxes().get(0));
result.put(pre, ((Stmt) pre.unit).getInvokeExpr().getUseBoxes().get(0));//We need to record the polluted object
            }
        }
    }


    public static HashMap<Node, ValueBox> findAllUnitAndValueAffected(HashMap<Node, ValueBox> sourceMap) {
//Forward search for data propagation, find all affected units and values
        HashSet<Event> processedEvent = new HashSet<>();
        HashMap<Node, ValueBox> result = new HashMap<>();
        EventQueue waitForProcessEvent = new EventQueue();
        for (Node sourceNode : sourceMap.keySet()) {
            waitForProcessEvent.add(new Event(sourceNode, sourceMap.get(sourceNode)));
        }
        while (!waitForProcessEvent.isEmpty()) {
            Event event = waitForProcessEvent.poll();
            Node node = event.node;
            ValueBox valueBox = event.valueBox;
            if (valueBox == null)   continue;
            processedEvent.add(event);
            for (Node succor : node.successorNodes) {
                if (succor.tag == null) {
                    if (!isValueDefinedInUnit(succor.unit, valueBox.getValue()))
                        addNewEvent(waitForProcessEvent, processedEvent, succor, valueBox);
                    doWithInputAsLeftValueOrRef(succor, valueBox, waitForProcessEvent, processedEvent, result);

                } else if (succor.tag.equals("BEGIN")) {
                    for (Node succorNode : node.originSuccorNode) {
                        if (!isValueDefinedInUnit(succorNode.unit, valueBox.getValue())) {
                            addNewEvent(waitForProcessEvent, processedEvent, succorNode, valueBox);
                        }
                        doWithInputAsLeftValueOrRef(succorNode, valueBox, waitForProcessEvent, processedEvent, result);
                    }
if (isValueUsedInUnit(node.unit, valueBox.getValue())) {//If there is a misplaced parameter in it
                        doWithInputAsParam(node, succor,valueBox, waitForProcessEvent, processedEvent);
                    }
} else if (succor.tag.equals("END")) {//If the successor node is
                    doWithInputAsRet(node, succor, valueBox, waitForProcessEvent, processedEvent, result);
                    if (valueBox.getValue().getUseBoxes().size() != 0 && valueBox.getValue().getUseBoxes().get(0).getValue().toString().contains("r0")) {
//If the fields of our object are polluted, we think the entire object is polluted.
                        doWithInputAsThis(succor, waitForProcessEvent, processedEvent, result);
                    }
                }
            }
        }
        return result;
    }



    public static Node dnfFind(Node beginNode, int index) {
        Queue<Node> queue = new LinkedList<>();
        queue.add(beginNode);
        while (!queue.isEmpty()) {
            Node front = queue.poll();
            if (front.unit != null && ((Stmt) front.unit).toString().contains("@parameter" + index))
                return front;
            for (Node succor : front.successorNodes) {
                if (succor.unit.toString().contains("@param") || succor.unit.toString().contains("@this"))
                    queue.add(succor);
            }
        }
        return null;
    }

    public static Node dnfBackFind(Node node) {
        Queue<Node> queue = new LinkedList<>();
        queue.add(node);
        while (!queue.isEmpty()) {
            Node front = queue.poll();
            if (front.tag!=null&&front.tag.equals("BEGIN"))
                return front;
            queue.addAll(front.precursorNodes);
        }
        return null;
    }

    /**
     * Find all definition statements that affect a variable
     *
     * @param sourceNode statement where this variable is located (you need to use this parameter to locate the position of the variable in cfg)
     * @param valueBox variable
     * @return {@link HashSet}<{@link Node}>
     */
public static LinkedHashSet<Node> findAllDefUnitAffectThisValue(Node sourceNode, ValueBox valueBox) {//Reverse search data propagation
        HashSet<Event> processedEvent = new HashSet<>();
        EventQueue waitForProcessEvent = new EventQueue();
        waitForProcessEvent.add(new Event(sourceNode, valueBox));
        LinkedHashSet<Node> nodeAffect = new LinkedHashSet<>();
        while (!waitForProcessEvent.isEmpty()) {
            Event event = waitForProcessEvent.poll();
            Node node = event.node;
            ValueBox valuebox = event.valueBox;
            processedEvent.add(event);
for (Node preNode : node.precursorNodes) {//We want to traverse all predecessors
if (preNode.tag == null) {// means that the previous statement is a general one
                    if (preNode.unit.getDefBoxes().isEmpty() || !isValueDefinedInUnit(preNode.unit, valuebox.getValue())) {
//If the previous one is not an assignment statement or the assignment statement that specifies the variable to us
                        addNewEvent(waitForProcessEvent, processedEvent, preNode, valuebox);
                    } else if (isValueDefinedInUnit(preNode.unit, valuebox.getValue())) {
//If the variable is defined in this statement, it is necessary to judge the situation. There are six situations in total
//Save the relevant assignment statements we found first
                        nodeAffect.add(preNode);
//                        log.info(preNode.unit+": "+valuebox.getValue());
//1. It was new
                        Stmt stmt = (Stmt) preNode.unit;
if (stmt instanceof AssignStmt && ((AssignStmt) stmt).getRightOp() instanceof NewExpr) {//If it is an assignment statement and it is new, terminate on this path

//do nothing
} else if (stmt.containsFieldRef()) {//If contains field reference
//2. If it is a field belonging to the class
                            if (stmt.getFieldRef().getField().isStatic()) {
//
} else {//3. If it belongs to an instance, we want to obtain the instance, we will not pursue the field, because the field is not complicated
                                AssignStmt assignStmt = (AssignStmt) stmt;
                                addNewEvent(waitForProcessEvent, processedEvent, preNode, assignStmt.getRightOp().getUseBoxes().get(0));
                            }
} else if (preNode.unit.toString().contains("@this")) {//4. It belongs to this object, we should continue to observe the object
Node beginNode = dnfBackFind(preNode);//Query the node it started
if(beginNode == null) // It's over
                                continue;
for (Node invokeNode : beginNode.precursorNodes) {//We get the call statement and then investigate the object
                                ValueBox thisValueBox = ((Stmt) invokeNode.unit).getInvokeExpr().getUseBoxes().get(0);
                                addNewEvent(waitForProcessEvent, processedEvent, invokeNode, thisValueBox);
                            }

} else if (preNode.unit.toString().contains("@param")) {//5. It is a parameter, we should pay attention to the parameters
int index = StringUtil.getParameterOrder(((Stmt) preNode.unit).toString());//Get parameter sequence number
                            Node beginNode = dnfBackFind(preNode);
if(beginNode == null) // It's over
                                continue;
                            for (Node invokeNode : beginNode.precursorNodes) {
                                ValueBox paramValueBox = ((Stmt) invokeNode.unit).getInvokeExpr().getUseBoxes().get(index);
                                addNewEvent(waitForProcessEvent, processedEvent, invokeNode, paramValueBox);
                            }
} else if (preNode.unit instanceof AssignStmt) { //TODO : Report an error soot.jimpl.internal.JIdentityStmt cannot be cast to soot.jimpl.AssignStmt, update and improve and correct
                            if (((AssignStmt) preNode.unit).containsInvokeExpr()) {
//6. It belongs to the return value. We want to view the return value.
                                if (node.tag != null && node.tag.equals("BEGIN")) {
for (Node originSuccor: preNode.originSuccorNode) {//We query the direct successor of the original node
for (Node endNode : originSuccor.precursorNodes) {//The original direct successor is now an END statement
                                            for (Node pre : endNode.precursorNodes) {
if (pre.unit.toString().contains("null"))//If the return value is null, it will not be considered
                                                    continue;
                                                if ((Stmt) pre.unit instanceof ReturnStmt) {
                                                    ValueBox returnValueBox = ((ReturnStmt) pre.unit).getOpBox();
                                                    addNewEvent(waitForProcessEvent, processedEvent, preNode, returnValueBox);
                                                }
                                            }
                                        }
                                    }
                                }
                            }
} else if (stmt instanceof AssignStmt){//7, it is an ordinary assignment statement
//                            assert stmt instanceof AssignStmt;
                            AssignStmt assignStmt = (AssignStmt) stmt;
                            addNewEvent(waitForProcessEvent, processedEvent, preNode, assignStmt.getRightOpBox());
                        }
                    }
                } else if (preNode.tag.equals("END")) {
//If it is END, it means that the previous one is an expansion of a call statement. Let's directly look for its original predecessor.
for (Node originPre : node.originPreNode) {//Finish the original front-wheel drive
                        if (originPre.unit.getDefBoxes().isEmpty() || !isValueDefinedInUnit(originPre.unit, valuebox.getValue())) {
//If the previous node is not assigned a value to the variable
                            addNewEvent(waitForProcessEvent, processedEvent, originPre, valuebox);
} else if (isValueDefinedInUnit(originPre.unit, valuebox.getValue())) {//If it is redefined, what needs to be viewed?
for (Node beginNode : originPre.successorNodes) {//We should
                                addNewEvent(waitForProcessEvent, processedEvent, beginNode, originPre.unit.getDefBoxes().get(0));
                            }

                        }
                    }
                }
            }
        }
        return nodeAffect;
    }

    /**
     * Determine whether a variable depends on another variable
     *
     * @param srcNode Statement where the stain variable is located (you need to use this parameter to locate the position of the variable in cfg)
     * @param srcValueBox blemish variable
     * @param tarNode Target Statement
     * @return boolean Can it be contaminated
     */
public boolean isDependencyBetweenValue(Node srcNode, ValueBox srcValueBox, Node tarNode) {//Judge the independence between data
        HashMap<Node, ValueBox> mp = new HashMap<>();
        mp.put(srcNode, srcValueBox);
        HashMap<Node, ValueBox> allUnitAndValueAffected = findAllUnitAndValueAffected(mp);
        return allUnitAndValueAffected.containsKey(tarNode);
    }

    /**
     * Find all variables that can affect using a variable as the source
     *
     * @param sourceMap Source of pollution
     * @return {@link HashMap}<{@link Node}, {@link ValueBox}> All pollution points after pollution spread
     */
    public static HashMap<Node, ValueBox> findAllUnitAndValueAffectedByPath(Path path, HashMap<Node, ValueBox> sourceMap) {
//path, an execution path
//sourceMap, the polluted nodes and paths on the path
//Determine how the given data propagates along a given path
        HashSet<Event> processedEvent = new HashSet<>();
        HashMap<Node, ValueBox> result = new HashMap<>();
        EventQueue waitForProcessEvent = new EventQueue();
        for (Node sourceNode : sourceMap.keySet()) {
            waitForProcessEvent.add(new Event(sourceNode, sourceMap.get(sourceNode)));
        }
        while (!waitForProcessEvent.isEmpty()) {
            Event event = waitForProcessEvent.poll();
            Node node = event.node;
            ValueBox valueBox = event.valueBox;
            processedEvent.add(event);
//We need to process the data after this node
            for (Node succor : node.successorNodes) {
if (path.nodes.contains(succor)) {//Find out the true successor on this path, there is only one successor
                    if (succor.tag == null) {
                        if (!isValueDefinedInUnit(succor.unit, valueBox.getValue()))
                            addNewEvent(waitForProcessEvent, processedEvent, succor, valueBox);
doWithInputAsLeftValueOrRef(succor, valueBox, waitForProcessEvent, processedEvent, result);//Judge whether the lvalue is affected. If it is just an ordinary lvalue or an object in the call statement, we think that the lvalue will be polluted
                    } else if (succor.tag.equals("BEGIN")) {
for (Node succorNode : node.originSuccorNode) {//Finish the original front-wheel drive
if (path.nodes.contains(succorNode)) {//Find the true original successor on this path
                                if (!isValueDefinedInUnit(succorNode.unit, valueBox.getValue()))
                                    addNewEvent(waitForProcessEvent, processedEvent, succorNode, valueBox);
                                doWithInputAsLeftValueOrRef(succorNode, valueBox, waitForProcessEvent, processedEvent, result);
                            }
                        }
if (isValueUsedInUnit(node.unit, valueBox.getValue())) {//If the polluting variable is used in this statement
                            doWithInputAsParam(node, succor,valueBox, waitForProcessEvent, processedEvent);
                        }
                    } else if (succor.tag.equals("END")) {
if (((Stmt) node.unit) instanceof ReturnStmt || ((Stmt) node.unit) instanceof RetStmt) {//If the previous is a return value statement
if (isValueUsedInUnit(node.unit, valueBox.getValue())) {//If the return value is polluted, we need to record the polluted return value
                                Node originNode = path.nodes.get(path.nodes.indexOf(succor) + 1);
                                for (Node invokeNode : originNode.originSuccorNode) {
                                    if (path.nodes.contains(invokeNode) && invokeNode.unit.getDefBoxes().size() != 0) {
                                        addNewEvent(waitForProcessEvent, processedEvent, invokeNode,invokeNode.unit.getDefBoxes().get(0));
                                        result.put(invokeNode,invokeNode.unit.getDefBoxes().get(0));
                                    }
                                }
                            }
if (valueBox.getValue().getUseBoxes().size() != 0 && valueBox.getValue().getUseBoxes().get(0).getValue().toString().contains("r0")) {//If the field of the object in the statement is polluted
                                Node originNode = path.nodes.get(path.nodes.indexOf(succor) + 1);
                                for (Node invokeNode : originNode.originSuccorNode) {
                                    if (path.nodes.contains(invokeNode)) {
                                        result.put(invokeNode,((Stmt) invokeNode.unit).getInvokeExpr().getUseBoxes().get(((Stmt) invokeNode.unit).getInvokeExpr().getUseBoxes().size() - 1));
                                        addNewEvent(waitForProcessEvent,processedEvent,originNode,((Stmt) invokeNode.unit).getInvokeExpr().getUseBoxes().get(((Stmt) invokeNode.unit).getInvokeExpr().getUseBoxes().size() - 1));
                                    }
                                }

                            }
                        }
                    }
                }

            }

        }
        return result;
    }

// Directly quote a statement to a valuebox
    public static List<Node> getValueBoxRefNodes(ValueBox valueBox, Node src){
        List<Node> result = new LinkedList<>();

        Queue<Node> queue = new LinkedList<>();
        HashSet<Node> visitedNodes = new HashSet<>();
        visitedNodes.add(src);
        queue.add(src);

        while (!queue.isEmpty()){
            Node node = queue.poll();
//            log.info(node.unit);
            for(Node successor : node.successorNodes){
                if(!visitedNodes.contains(successor)) {
                    queue.add(successor);
                    visitedNodes.add(successor);
                }
            }

            for(ValueBox usedBox : node.unit.getUseBoxes()){
                if(usedBox.getValue().toString().equals(valueBox.getValue().toString())) {
                    result.add(node);
                    break;
                }
            }
        }
        return result;
    }

// Directly refer to the event of a valuebox
    public static List<Event> getValueBoxRefEvents(ValueBox valueBox, Node src){
        List<Event> result = new LinkedList<>();

        Queue<Node> queue = new LinkedList<>();
        HashSet<Node> visitedNodes = new HashSet<>();
        visitedNodes.add(src);
        queue.add(src);

        while (!queue.isEmpty()){
            Node node = queue.poll();
//            log.info(node.unit);
            for(Node successor : node.successorNodes){
                if(!visitedNodes.contains(successor)) {
                    queue.add(successor);
                    visitedNodes.add(successor);
                }
            }

            for(ValueBox usedBox : node.unit.getUseBoxes()){
                if(usedBox.getValue().toString().equals(valueBox.getValue().toString())) {
                    Event event = new Event(node, usedBox);
                    result.add(event);
                }
            }
        }
        return result;
    }

// Direct definition of a variable
    public static List<Node> getDefNodes(ValueBox valueBox, Node src){
        List<Node> result = new LinkedList<>();

        Queue<Node> queue = new LinkedList<>();
        HashSet<Node> visitedNodes = new HashSet<>();
        visitedNodes.add(src);
        queue.add(src);

        while (!queue.isEmpty()){
            Node node = queue.poll();
//            log.info(node.unit);
            for(Node precursor : node.precursorNodes){
                if(!visitedNodes.contains(precursor)) {
                    queue.add(precursor);
                    visitedNodes.add(precursor);
                }
            }

            for(ValueBox defBox : node.unit.getDefBoxes()){
                if(defBox.getValue().toString().equals(valueBox.getValue().toString())) {
                    result.add(node);
                }
            }
        }
        return result;
    }

}
