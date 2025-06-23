package jdd.rules.sinks;


import jdd.tranModel.Transformable;
import jdd.tranModel.TransformableNode;
import jdd.container.BasicDataContainer;
import jdd.container.FragmentsContainer;
import jdd.dataflow.node.MethodDescriptor;
import jdd.gadgets.unit.Fragment;
import jdd.markers.SinkType;
import jdd.markers.Stage;
import soot.SootMethod;
import soot.jimple.InvokeExpr;
import jdd.util.Utils;

import java.io.IOException;
import java.util.HashSet;
import java.util.LinkedList;

/**
 * Abstract class for Gadget Sink detection rules
 * Used to check the generation of Sink Fragment
 */

public abstract class AbstractCheckRule implements CheckRule {
    public SinkType sinkType;
// Switches reserved specifically for ClassLoader for repeated Gadget comparisons
    boolean isClassLoadGadget = false;

    /**
     * @param callStack In the call stack when performing data flow analysis, we will detect whether the current data flow is a preset risky method in the process.
     * @param descriptor Used to describe the context of the current method
     * @param transformable Used to identify the Jimple IR for the current analysis
     */
    public void apply(MethodDescriptor descriptor,
                      LinkedList<SootMethod> callStack,
                      Transformable transformable) throws IOException { }


    public boolean checkRisky(MethodDescriptor descriptor, TransformableNode tfNode){ return false;}

    /**
     * Check whether there are duplicate call stack in Fragments under the same Sink Type
     * @param callStack
     * @param sinkType
     * @return true: repeat; false: not repeat
     */
    protected boolean checkGadgetDuplication(LinkedList<SootMethod> callStack, SinkType sinkType) {
// This check is only performed during the Fragment search phase
        if (!BasicDataContainer.stage.equals(Stage.FRAGMENT_SEARCHING))
            return false;
        boolean flag = false;
        HashSet<Fragment> toDelete = new HashSet<>();

        for (Fragment fragment: FragmentsContainer.getSinkFragmentsByHead(callStack.getFirst())){
            if (fragment.sinkType.equals(sinkType)){
                if (Utils.listEqual(fragment.getGadgets(), callStack)){
                    flag = true;
                }
// Some heuristic rules
                else if (Utils.listContains(callStack, fragment.getGadgets())
& callStack.size() > fragment.getGadgets().size() + 2){ // If the call stack is included in fragment.gadgets and the number of gadgets is smaller, then
                    flag = true;
                }else if (Utils.listContains(fragment.getGadgets(),callStack)
                        & fragment.getGadgets().size() > callStack.size() + 2)
                    toDelete.add(fragment);
            }
        }
        for (Fragment fragment: FragmentsContainer.getSinkFragmentByEnd(callStack.getLast())){
            if (fragment.sinkType.equals(sinkType)){
                if (Utils.listEqual(fragment.getGadgets(), callStack)){
                    flag = true;
} // Heuristic filtering can be deleted
                else if (Utils.isSubRevList(callStack, fragment.getGadgets())
                        && callStack.size() > fragment.getGadgets().size()+BasicDataContainer.heuristicShortChainCutLen){
                    flag = true;
                }else if (Utils.isSubRevList(fragment.getGadgets(), callStack)
                        && fragment.getGadgets().size() < callStack.size()-BasicDataContainer.heuristicShortChainCutLen){
                    toDelete.add(fragment);
                }
            }
        }

        for (Fragment fragment: toDelete){
            FragmentsContainer.stateFragmentsMap.get(Fragment.FRAGMENT_STATE.SINK).remove(fragment);
            FragmentsContainer.typeFragmentsMap.get(fragment.type).remove(fragment);
            FragmentsContainer.sinkFragments.remove(fragment);
        }

        return flag;
    }
}
