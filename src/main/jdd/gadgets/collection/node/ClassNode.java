package jdd.gadgets.collection.node;

import jdd.dataflow.node.MethodDescriptor;
import jdd.dataflow.node.SourceNode;
import soot.SootClass;
import soot.SootField;
import soot.SootMethod;

import java.util.*;

public class ClassNode {
// Representative Class
    public SootClass sootClass = null;

    public int classId = 0;
    public ClassNode rootClassNode = null;
public GadgetInfoRecord gadgetInfoRecord = null; // The GadgetInfoRecord belongs to, convenient for indexing
    public SootMethod caller = null;
    public SourceNode source = null;
public HashSet<SourceNode> candidateSources = new HashSet<>(); // Record potential sources, because sometimes the inference may be inaccurate enough, and there will be multiple potential sources
// Record which gadgets belong to this category in gadget chains
    public LinkedList<SootMethod> gadgets = new LinkedList<>();
    public LinkedHashMap<SootMethod, GadgetNode> gadgetNodes = new LinkedHashMap<>();
    public LinkedHashMap<SootMethod, GadgetNode> implicitGadgetNodes = new LinkedHashMap<>();
public HashMap<SourceNode, HashSet<ClassNode>> fields = new HashMap<>(); // Thinking: Fixed to 1->N record format
    public HashMap<SourceNode, HashSet<ClassNode>> conFields = new HashMap<>();

    public HashMap<SourceNode, HashSet<ClassNode>> implicitFields = new HashMap<>();
// Record sinks construction related information
    public HashSet<SinkNode> sinkNodes = new HashSet<>();
public boolean isProxy = false; // Whether the flag is a dynamic proxy class
public SootMethod triggerMethod = null; // Method to trigger dynamic proxy
// For dynamic proxy class nodes, mark their Invocation Handler class nodes
    public ClassNode invocationHandlerClassNode = null;

    public boolean flag = true;

    public ClassNode(ClassNode rootClassNode, SootMethod caller,
                     SootClass sootClass, SourceNode source,
                     GadgetInfoRecord gadgetInfoRecord, HashSet<SourceNode> candidateSources){
        this.rootClassNode = rootClassNode;
        this.caller = caller;
        this.sootClass = sootClass;
        this.source = source;
        this.gadgetInfoRecord = gadgetInfoRecord;
        if (candidateSources.size() > 1)
            this.candidateSources = candidateSources;
    }

    public ClassNode(SootClass sootClass, GadgetInfoRecord gadgetInfoRecord){
        this.sootClass = sootClass;
        this.gadgetInfoRecord = gadgetInfoRecord;
    }


    public void addGadgetNode(GadgetNode newGadgetNode) {
        boolean inGadgetChain = this.gadgetInfoRecord.gadgets.contains(newGadgetNode.sootMethod);
        if (inGadgetChain){
            if (!gadgetNodes.containsKey(newGadgetNode.sootMethod)) {
                gadgetNodes.put(newGadgetNode.sootMethod, newGadgetNode);
gadgets.add(newGadgetNode.sootMethod); // Only recorded in gadget chain
            }
            if (!gadgetInfoRecord.gadgetNodesMap.containsKey(newGadgetNode.sootMethod)){
                gadgetInfoRecord.gadgetNodesMap.put(newGadgetNode.sootMethod, newGadgetNode);
            }
        }else {
            if (!implicitGadgetNodes.containsKey(newGadgetNode.sootMethod)) {
                implicitGadgetNodes.put(newGadgetNode.sootMethod, newGadgetNode);
            }

            if (!gadgetInfoRecord.implicitGadgetNodesMap.containsKey(newGadgetNode.sootClass))
                gadgetInfoRecord.implicitGadgetNodesMap.put(newGadgetNode.sootClass, new LinkedHashMap<>());
            if (!gadgetInfoRecord.implicitGadgetNodesMap.get(newGadgetNode.sootClass).containsKey(newGadgetNode.sootMethod)){
                gadgetInfoRecord.implicitGadgetNodesMap.get(newGadgetNode.sootClass).put(newGadgetNode.sootMethod, newGadgetNode);
            }
        }
    }

    public GadgetNode getGadgetChain(SootMethod sootMethod, boolean inGadgetChain){
        if (inGadgetChain)
            return gadgetNodes.get(sootMethod);
        else return implicitGadgetNodes.get(sootMethod);
    }

    /**
     * 创建并添加 Gadget Node
     * @param invokedDescriptor
     * @return
     */
    public GadgetNode createAndAddGadgetNode(MethodDescriptor invokedDescriptor) {
        boolean inGadgetChain = gadgetInfoRecord.gadgets.contains(invokedDescriptor.sootMethod);
        GadgetNode newGadgetNode = getGadgetChain(invokedDescriptor.sootMethod, inGadgetChain);
        if (newGadgetNode != null)
            return newGadgetNode;

        newGadgetNode = new GadgetNode(invokedDescriptor.sootMethod, invokedDescriptor.getCurrentClass());
        addGadgetNode(newGadgetNode);
        return newGadgetNode;
    }

    public boolean equals(Object object){
        if (!(object instanceof ClassNode))
            return false;

        ClassNode classNode = (ClassNode) object;
        if (!sootClass.equals(classNode.sootClass))
            return false;

        if (rootClassNode != null & classNode.rootClassNode != null){
            if (!caller.equals(classNode.caller)
                    | !rootClassNode.equals(classNode.rootClassNode)
                    | !source.equals(classNode.source)
                    | !gadgetInfoRecord.equals(classNode.gadgetInfoRecord))
                return false;
        }
        if (rootClassNode != null & classNode.rootClassNode == null)
            return false;
        if (rootClassNode == null & classNode.rootClassNode != null)
            return false;
        return true;
    }

    public int hashCode(){
        int hashCode = 0;
        hashCode = sootClass.hashCode();
        if (caller != null)
            hashCode = hashCode^7 + caller.hashCode();
        if (source != null)
            hashCode = hashCode^7+ source.hashCode();
        return hashCode;
    }
}
