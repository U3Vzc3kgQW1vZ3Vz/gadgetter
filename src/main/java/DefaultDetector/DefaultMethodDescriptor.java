package java.DefaultDetector;

import soot.SootMethod;

/**
 * Method description class, used to record the detection results of a method during detection, avoiding multiple detections.
 */
public class DefaultMethodDescriptor implements IMethodDescriptor{

    @Override
    public boolean isCompletelyDescribed() {
        return false;
    }

    @Override
    public void forceSetDescribed() {

    }

    public enum State{
        YES, NO, UNKNOWN
    }

    public SootMethod sootMethod;

    public DefaultMethodDescriptor(SootMethod method){
        this.sootMethod = method;
    }
}
