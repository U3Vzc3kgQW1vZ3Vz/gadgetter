package java.cfg;
import lombok.Getter;
import lombok.Setter;
import soot.SootMethod;
import soot.Unit;
import soot.jimple.toolkits.callgraph.Edge;

import java.util.HashSet;
import java.util.Iterator;

@Getter
@Setter
public class Node {
    public Unit unit;
public HashSet<Node> precursorNodes = new HashSet<>();//The direct predecessor node that saves the statement
public HashSet<Node> successorNodes = new HashSet<>();//Save the successor of the statement
    public String tag;
public boolean isExpand=false;//If the node is a method, the method marked there is expanded
public SootMethod sootMethod; // The SootMethod to which the Node belongs

public HashSet<Node> originPreNode=new HashSet<>();// Used to save the initial predecessor node
public HashSet<Node> originSuccorNode=new HashSet<>();// Used to save the initial successor node

    public Node(Unit unit) {
        this.unit = unit;
    }

    public Node(Unit unit, SootMethod sootMethod){
        this.unit = unit;
        this.sootMethod = sootMethod;
    }

    public Node(String tag) {
        this.tag = tag;
    }

    public String toString(){
        if(this.unit == null) return "<Null Unit>";
        return this.unit.toString();
    }


}
