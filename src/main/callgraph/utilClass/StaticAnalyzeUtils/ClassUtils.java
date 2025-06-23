package callgraph.utilClass.StaticAnalyzeUtils;

import lombok.extern.slf4j.Slf4j;
import soot.Scene;
import soot.SootClass;

import java.util.*;

/**
 * Basic static analysis capabilities
 */
@Slf4j
public class ClassUtils {
    public static HashSet<SootClass> forceGetConcreteClass(SootClass sootClass, int num){
// BFS search for concrete subclass , return num classes at most
        HashSet<SootClass> concreteClasses = new HashSet<>();
        Queue<SootClass> queue = new LinkedList<>();
        queue.add(sootClass);
        while(!queue.isEmpty() && num > 0){
            SootClass c = queue.poll();
            if(c.isConcrete()) {
                concreteClasses.add(c);
                num--;
            }
            else{
                queue.addAll(Scene.v().getActiveHierarchy().getDirectSubclassesOf(sootClass));
            }
        }
        return concreteClasses;
    }

    public static SootClass forceGetConcreteClassOnlyOne(SootClass sootClass){
        HashSet<SootClass> concreteClasses = forceGetConcreteClass(sootClass, 1);
        if(concreteClasses.size() > 0) return concreteClasses.iterator().next();
        return null;
    }

    public static LinkedHashSet<SootClass> getAllSupers(SootClass sootClass){
        LinkedHashSet<SootClass> res = new LinkedHashSet<>();
        getAllSuperClassAndInterfaces(sootClass, res);
        return res;
    }

    /**
     * Get all parent classes & interfaces
     */
    private static void getAllSuperClassAndInterfaces(SootClass sootClass, LinkedHashSet<SootClass> result){
        if(result.contains(sootClass)) return;
        if (sootClass.resolvingLevel()<1) return;
        result.add(sootClass);
        if(sootClass.isInterface()) {
            if (!sootClass.hasSuperclass())  return;
            for(SootClass superClass : Scene.v().getActiveHierarchy().getSuperinterfacesOf(sootClass)) {
                getAllSuperClassAndInterfaces(superClass, result);
            }
        }else if (sootClass.hasSuperclass()){
            for(SootClass superClass : Scene.v().getActiveHierarchy().getSuperclassesOf(sootClass)) {
                getAllSuperClassAndInterfaces(superClass, result);
            }
        }
        if (sootClass.getInterfaceCount() > 0){
            for (SootClass interfaceClass : sootClass.getInterfaces()){
                getAllSuperClassAndInterfaces(interfaceClass, result);
            }
        }
    }

    public static HashSet<SootClass> AllInterfaces(SootClass sootClass){
        LinkedHashSet<SootClass> res = new LinkedHashSet<>();
        getAllSuperClassAndInterfaces(sootClass, res);
        return res;
    }

    private static void getAllInterfaces(SootClass sootClass, HashSet<SootClass> result){
        if(result.contains(sootClass)) return;
        result.add(sootClass);
        if(sootClass.isInterface()) {
            for(SootClass superClass : Scene.v().getActiveHierarchy().getSuperinterfacesOf(sootClass)) {
                getAllInterfaces(superClass, result);
            }
        }else {
            for(SootClass superClass : Scene.v().getActiveHierarchy().getSuperinterfacesOf(sootClass)) {
                getAllInterfaces(superClass, result);
            }
        }
    }

// The packaging of getAllSubClassAndInterfaces
    public static HashSet<SootClass> getAllSubs(SootClass sootClass){
        HashSet<SootClass> res = new HashSet<>();
        getAllSubClassAndInterfaces(sootClass, res);
        return res;
    }

    /**
     * Find all subclasses that implement sootClass
     * @param sootClass Target CLass
     * @param result HashSet that saves the result
     */
    private static void getAllSubClassAndInterfaces(SootClass sootClass, HashSet<SootClass> result){
        if(result.contains(sootClass)) return;
        if (sootClass.resolvingLevel()<1) return;

result.add(sootClass); // ToDo: Weird way to write
// If it is an interface, then it will obtain its subinterface and implementation class and process it recursively.
// If it is not an interface, then the subclass of the current class is retrieved and processed recursively
        if(sootClass.isInterface()) {
            for(SootClass superClass : Scene.v().getActiveHierarchy().getSubinterfacesOf(sootClass)) {
                getAllSubClassAndInterfaces(superClass, result);
            }
            for(SootClass superClass : Scene.v().getActiveHierarchy().getImplementersOf(sootClass)) {
                getAllSubClassAndInterfaces(superClass, result);
            }
        } else  {
            try {
                for (SootClass superClass : Scene.v().getActiveHierarchy().getSubclassesOf(sootClass)) {
                    getAllSubClassAndInterfaces(superClass, result);
                }
            }catch (NullPointerException e){
//                log.info(sootClass.getName() + " does not have any sub-classes!");
            }
        }
    }

    /**
     * The breadth priority order gets all parent classes layer by layer. In most cases (not considering the interface Default method), it should be a chain
     * Includes sootClass
     */
    public static LinkedList<SootClass> getAllSupers_BFS(SootClass sootClass){
        LinkedList<SootClass> ret = new LinkedList<>();
        Queue<SootClass> waiting = new LinkedList<>();
        waiting.add(sootClass);
        while(!waiting.isEmpty()){
            SootClass clazz = waiting.poll();
            ret.add(clazz);
            if(!sootClass.isInterface()){
                if(sootClass.hasSuperclass() && !waiting.contains(sootClass.getSuperclass()) && !ret.contains(sootClass.getSuperclass()))
                    waiting.add(sootClass.getSuperclass());
            }else if (sootClass.isInterface()){
                for (SootClass superClass: sootClass.getInterfaces()) {
                    if (waiting.contains(superClass) | ret.contains(superClass))
                        continue;
                    waiting.add(superClass);
                }
            }
        }
        return ret;
    }

    /**
     * Breadth priority order to obtain all subclasses layer by layer
     */
    public static List<SootClass> getAllSubs_BFS(SootClass sootClass){
        List<SootClass> ret = new LinkedList<>();
        Queue<SootClass> waiting = new LinkedList<>();
        waiting.add(sootClass);
        while(!waiting.isEmpty()){
            SootClass clazz = waiting.poll();
            ret.add(clazz);
            if(sootClass.isInterface()) {
                for(SootClass subClass : Scene.v().getActiveHierarchy().getDirectSubinterfacesOf(sootClass)) {
                    if(!waiting.contains(subClass) && !ret.contains(subClass)) waiting.add(subClass);
                }
                for(SootClass subClass : Scene.v().getActiveHierarchy().getDirectImplementersOf(sootClass)) {
                    if(!waiting.contains(subClass) && !ret.contains(subClass)) waiting.add(subClass);
                }
            }
            else  {
                for(SootClass subClass : Scene.v().getActiveHierarchy().getDirectSubclassesOf(sootClass)) {
                    if(!waiting.contains(subClass) && !ret.contains(subClass)) waiting.add(subClass);
                }
            }
        }
        return ret;
    }
}
