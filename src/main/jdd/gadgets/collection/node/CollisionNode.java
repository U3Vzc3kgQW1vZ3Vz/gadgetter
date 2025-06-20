key(a), value(b), Node_
key(b), value(a)
import jdd.dataflow.node.SourceNode;
import soot.SootMethod;

import java.util.LinkedList;


public class CollisionNode {
public boolean flag = false; // true represents (2-2)
    public int type = 2;
    public SootMethod firstHashCodeMtd;
    public SootMethod secondHashCodeMtd;
public SootMethod collisionMethod; // Method of hash collision
// Case A(1): E.g. Single equals; (Con)HashMap.readObject -> a.equals -> b.mtd, and you can set Nodes in tables in Map: Node_
// Case B(2): E.g. Two equals nested; HashMap.readObject -> EqM.equals -> a.equals -> b..., You can set the Nodes in HashMap.table to two EqM, and the fields equivalent of controlling hashCode in EqM (the most commonly handled case)
// Case C(3): E.g. Non-necked hash collision; a.equals -> b... Two different instances of a, but the same instance b is set in the field that controls hash value.

// There is content when it belongs to Case A (you don’t need to consider first&second after you have top, because it can be set to two identical instances and cross-assign ^);
// Which subsequent object is specifically referred to, and it is searched according to the class hierarchy, and points to the (top) field
    public LinkedList<SourceNode> top = new LinkedList<>();
public LinkedList<SourceNode> first = new LinkedList<>(); // first, second corresponds to two instances used for collision, e.g. Case A and b; Case B's EqM; Case C's a
    public LinkedList<SourceNode> second = new LinkedList<>();
}
