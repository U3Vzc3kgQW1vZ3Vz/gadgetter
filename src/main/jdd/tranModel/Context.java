package jdd.tranModel;

import soot.SootClass;
import soot.SootMethod;

/**
 * This class is used to record a sootMethod and declare its sootClass
 * Used in TransformableNode
 */
public class Context {
    public SootMethod method;
    public SootClass sootClass;
}
