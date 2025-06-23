package callgraph.utilClass;

import java.util.HashSet;
import java.util.Random;
import java.util.Set;

public class Util {
public static boolean isStandardLibrary(String methodSignature) {//How to determine whether it is a standard library
        if (methodSignature.startsWith("java") || methodSignature.startsWith("android") || methodSignature.startsWith("androidx") || methodSignature.startsWith("kotlin"))
            return true;
        return false;
    }

public static Set<Integer> random(int low,int high,int size){//Get different numbers of the specified number of the specified range
        HashSet<Integer>  set=new HashSet<>();
        Random rand=new Random();
        while (set.size()<size){
            int num = rand.nextInt();
            if(num>=low&&num<high){
                set.add(num);
            }
        }
        return set;
    }
}
