package jdd.tranModel;

import jdd.container.FragmentsContainer;
import jdd.dataflow.node.MethodDescriptor;
import jdd.gadgets.collection.node.GadgetInfoRecord;
import jdd.gadgets.collection.rule.InferRule;
import soot.SootMethod;

import java.io.IOException;
import java.util.LinkedList;
import java.util.List;

public class Transformable {
    public enum State{
        ORIGIN, TRANSFORMED, TERMINATED
    }

// Rule container
    static List<Rule> rules = new LinkedList<>();
    static List<InferRule> inferRules = new LinkedList<>();
    static List<InferRule> extraInferRules = new LinkedList<>();
    public State state = State.ORIGIN;

// Clear the rules
    public static void clearRules(){
        rules = new LinkedList<>();
    }

    public static void clearInferRules(){
        inferRules = new LinkedList<>();
    }

    public static void clearExtraInferRules(){
        extraInferRules = new LinkedList<>();
    }

// Add rules
    public static void addRule(Rule rule){
        rules.add(rule);
    }

    public static void addInferRule(InferRule inferRule){
        inferRules.add(inferRule);
    }

    public static void addExtraInferRule(InferRule inferRule){
        extraInferRules.add(inferRule);
    }

    /**
     * Used to apply various rules in the data flow analysis process, such as alias, Point2, taint propagation, etc.
     * @param descriptor
     */
    public void forward(MethodDescriptor descriptor){
        state = State.TRANSFORMED;
        for(Rule rule : rules){
            rule.apply(this,descriptor);
        }
    }

    /**
     * Used for the collection of risky call stack information
     * @param descriptor
     * @param callStack
     * @throws IOException
     */
    public void forwardCheck(MethodDescriptor descriptor,
                             LinkedList<SootMethod> callStack) throws IOException {
        FragmentsContainer.protocolCheckRule.apply(descriptor, callStack, this);
    }

    public void forwardInferCheck(MethodDescriptor descriptor,
                                  GadgetInfoRecord gadgetInfoRecord) throws IOException {
        for (InferRule inferRule: inferRules)
            inferRule.apply(descriptor, gadgetInfoRecord, this);
    }

    public void forwardExtraInferCheck(MethodDescriptor descriptor,
                                  GadgetInfoRecord gadgetInfoRecord) throws IOException {
        for (InferRule inferRule: extraInferRules)
            inferRule.apply(descriptor, gadgetInfoRecord, this);
    }

    public void terminate(){
        state = State.TERMINATED;
    }

    public boolean isTerminated(){
        return state.equals(State.TERMINATED);
    }
}
