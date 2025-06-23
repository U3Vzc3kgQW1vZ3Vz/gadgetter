package callgraph.DefaultDetector;
/**
 * The interface described by the method, the method description of a specific scenario can be used to implement the interface.
 */
public interface IMethodDescriptor {
    boolean isCompletelyDescribed();
    void forceSetDescribed();

    /**
     * Used to limit the number of call stack layers
     */
    class BaseStateFlag{
        public int distance;
        public boolean flag;

        public BaseStateFlag(){
            distance = Integer.MAX_VALUE;
            flag = false;
        }

        public boolean isTrue(){
            return flag;
        }

        public void setTrue(){
            flag = true;
        }

        public int getDistance(){
            return distance;
        }

        public boolean updateDistance(BaseStateFlag calleeFlag){
            if(calleeFlag.distance == Integer.MAX_VALUE) return false;
            if(calleeFlag.distance + 1 < this.distance){
                this.distance = calleeFlag.distance + 1;
                return true;
            }
            return false;
        }
    }
}
