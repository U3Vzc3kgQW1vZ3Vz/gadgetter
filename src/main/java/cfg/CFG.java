package java.cfg;

import java.cg.CG;
import heros.flowfunc.Identity;
import lombok.extern.slf4j.Slf4j;
import soot.*;
import soot.jimple.*;
import soot.jimple.toolkits.callgraph.Edge;
import soot.jimple.toolkits.ide.DefaultJimpleIFDSTabulationProblem;
import soot.toolkits.graph.BriefUnitGraph;
import soot.toolkits.graph.UnitGraph;
import java.util.Util;

import java.util.*;
import java.util.function.Function;

/**
 * 控制流图（Control Flow Graph）
 *
 * @since 2.0
 */
@Slf4j
public class CFG {

    public Node headNode = null;

    public LinkedHashMap<Unit, Node> allNodes = new LinkedHashMap<>();

    public int maxDepth = 5;

public HashSet<String> selfDefinedToExpandMethodSet = null;//User custom defined method that should be expanded

    public boolean isUseStandardLib = false;

    public SootMethod entryPoint;

    public static int pathCount=0;

    public CG cg=null;

    /**
     * 初始化CFG，详尽的构造器。
     * 不会构建CFG图，构建应使用buildCFG()
     *
     * <br><b>示例</b><br>
     * CFG cfg = new CFG(entryPoint, maxDepth, selfDefinedToExpandMethodSet, isUseStandardLib);<br>
     * cfg.buildCFG();<br>
     *
     * @param entryPoint                   入口方法
     * @param maxDepth                     展开函数的最大深度
     * @param selfDefinedToExpandMethodSet 自定义展开条件
     * @param isUseStandardLib             是否展开标准库
     */
    public CFG(SootMethod entryPoint, int maxDepth, HashSet<String> selfDefinedToExpandMethodSet, boolean isUseStandardLib) {
        this.entryPoint = entryPoint;
        this.maxDepth = maxDepth;
        this.selfDefinedToExpandMethodSet = selfDefinedToExpandMethodSet;
        this.isUseStandardLib = isUseStandardLib;
        if(cg==null){
            log.info("Warning: "+"You haven't set cg for the ICFG, it won't be precise");
        }
    }

    /**
     * 初始化CFG。
     * 不会构建CFG图，构建应使用buildCFG()
     *
     * <br><b>示例</b><br>
     * CFG cfg = new CFG(entryPoint, maxDepth);<br>
     * cfg.buildCFG();<br>
     *
     * @param entryPoint                   入口方法
     * @param maxDepth                     展开函数的最大深度
     */
    public CFG(SootMethod entryPoint, int maxDepth) {
        this.entryPoint = entryPoint;
        this.maxDepth = maxDepth;
    }

    /**
     * 初始化CFG，精简的构造器。
     * 不会构建CFG图，构建应使用buildCFG()<br>
     *
     * <br><b>示例</b><br>
     * CFG cfg = new CFG(entryPoint);<br>
     * cfg.buildCFG();<br>
     *
     * @param entryPoint                   入口方法
     */
    public CFG(SootMethod entryPoint){
        this.entryPoint = entryPoint;
    }

    /**
     * 过程内的，sft use
     *
     * @param sootMethod
     * @param innerProcess
     */
    public CFG(SootMethod sootMethod, boolean innerProcess){
        this.entryPoint = sootMethod;
        if(innerProcess){
            this.selfDefinedToExpandMethodSet = new HashSet<>();
        }
    }

    /**
     * 构建cfg
     *
     * @return {@link Node} 头节点
     */
    public Node buildCFG(){
        buildGraph(entryPoint,new HashSet<>(),0);
        return headNode;
    }

    public void setCG(CG cg){
// Specify cg for this ICFG
        this.cg=cg;
    }

    public HeadAndTail buildGraph(SootMethod sootMethod, Set<String> visit, int depth) {
        if (depth > maxDepth)
            return null;
        Body body;
        try {
            body = sootMethod.retrieveActiveBody();
        }catch (Exception e){
// ToDo: There are many cases where the run method of anonymous inner class cannot retrieveActiveBody
            if(!sootMethod.getName().equals("run")) {
            }

            return null;
        }

        if (body != null) {
            UnitGraph unitGraph = new BriefUnitGraph(body);
            for (Unit unit : unitGraph.getBody().getUnits()) {
                allNodes.put(unit, new Node(unit,sootMethod));
                if(headNode == null) headNode = allNodes.get(unit);
            }
            for (Unit unit : unitGraph.getBody().getUnits()) {
                Node node = getNodeByUnit(unit);
                for (Unit preUnit : unitGraph.getPredsOf(unit)) {
                    Node preNode = getNodeByUnit(preUnit);
                    if (!preNode.successorNodes.contains(node)) {

// cfg in process
                        if (selfDefinedToExpandMethodSet!=null && selfDefinedToExpandMethodSet.isEmpty()){
                            preNode.successorNodes.add(node);
                            node.precursorNodes.add(preNode);
                            continue;
                        }

                        Stmt stmt = (Stmt) preNode.unit;
                        if (stmt.containsInvokeExpr() && (!(stmt instanceof IfStmt)) && (!(stmt instanceof GotoStmt))) {
                            SootMethod method=null;
                            if(cg==null) {
// If cg is not built for ICFG in advance, on-the-fly build ICFG, the result is inaccurate
                                 method = stmt.getInvokeExpr().getMethod();
                            }else {
// The method of using the graph construction in soot may also cause false positives due to the exact readability problem. This situation is what we expected.
// This situation was not considered in the subsequent data flow analysis. In order to reduce a large number of modifications, we only take one method by default, but the accuracy still requires
// much higher than the previous method
                                Iterator<Edge> edgeIterator = Scene.v().getCallGraph().edgesOutOf(preNode.unit);
                                if (edgeIterator.hasNext()){
                                    method=edgeIterator.next().tgt();
                                }
                            }
                            if(method == null) {
                                preNode.successorNodes.add(node);
                                node.precursorNodes.add(preNode);
                                continue;
                            }
                            if (selfDefinedToExpandMethodSet!=null&&!selfDefinedToExpandMethodSet.contains(method.getSignature())) {
//If the user-defined method collection that needs to be expanded does not contain this method
                                preNode.successorNodes.add(node);
                                node.precursorNodes.add(preNode);
                                continue;
                            }
if (visit.contains(method.getSignature())) {//If this method contains a method that exists on the path, it means there is a loop
                                preNode.successorNodes.add(node);
                                node.precursorNodes.add(preNode);
                                continue;
                            }
if (!method.isConcrete()) {//If the method is not specific
                                preNode.successorNodes.add(node);
                                node.precursorNodes.add(preNode);
                                continue;
                            }
if (Util.isStandardLibrary(method.getDeclaringClass().getName())&&isUseStandardLib) {// Whether the standard library used to indicate whether the Android standard library needs to be expanded
                                preNode.successorNodes.add(node);
                                node.precursorNodes.add(preNode);
                                continue;
                            }
                            Set<String> addVisit = new HashSet<>();
                            addVisit.addAll(visit);
                            addVisit.add(method.getSignature());
                            HeadAndTail headAndTail = buildGraph(method, addVisit, depth + 1);
                            if (headAndTail == null) {
                                preNode.successorNodes.add(node);
                                node.precursorNodes.add(preNode);
                                continue;
                            }

                            preNode.originSuccorNode.add(node);
                            node.originPreNode.add(preNode);

                            Node beginNode = new Node("BEGIN");
                            preNode.successorNodes.add(beginNode);
preNode.isExpand=true;//The method to mark this is expanded
                            beginNode.precursorNodes.add(preNode);
                            for (Node head : headAndTail.headNodes) {
                                beginNode.successorNodes.add(head);
                                head.precursorNodes.add(beginNode);
                            }

                            Node endNode = new Node("END");
                            for (Node tail : headAndTail.tailNodes) {
                                tail.successorNodes.add(endNode);
                                endNode.precursorNodes.add(tail);
                            }

                            endNode.successorNodes.add(node);
                            node.precursorNodes.add(endNode);

} else {//If the predecessor is not a calling method, its successor node is the node
                            preNode.successorNodes.add(node);
                            node.precursorNodes.add(preNode);
                        }
                    }
                }
            }
HeadAndTail headAndTail = new HeadAndTail();//Return the head and end of the expansion statement
            for (Unit unit : unitGraph.getHeads()) {
                headAndTail.headNodes.add(getNodeByUnit(unit));
// headNode = getNodeByUnit(unit);//Get the head node of the entire graph
            }
            for (Unit unit : unitGraph.getTails())
                headAndTail.tailNodes.add(getNodeByUnit(unit));
            return headAndTail;

        } else {
            return null;
        }
    }

    public Node getNodeByUnit(Unit unit) {
        return allNodes.get(unit);
    }

    /**
     * 重置这个cfg图
     */
    public void reset() {
        headNode = null;
        allNodes.clear();
    }

    static class HeadAndTail {
        public HashSet<Node> headNodes = new HashSet<>();
        public HashSet<Node> tailNodes = new HashSet<>();
    }

    /**
     * 找到语句之间的所有路径，为了防止内存溢出，后三个参数用来限制深度优先搜索，我们提供推荐值。
     *
     * @param srcNode       源语句节点
     * @param trgNode       目的语句节点
     * @param maxPathLength 搜索时的最大路径长度，超过此长度的路径不再继续搜索。
     * @param maxPathNum    总的存储的路径上限
     * @param maxTarPathNum 递归查找中递归的路径的上限
     * @return {@link List}&lt;{@link Path}&gt;
     */
    public static List<Path> findAllPathsBetweenUnits(Node srcNode,Node trgNode,int maxPathLength,int maxPathNum,int maxTarPathNum){
//Return all paths between two statements, CFG is a DAG
//We set the maximum length of the path. When the searched path length is greater than this value, the target node has not been reached, and the path is abandoned and no longer searches downward.
//We set the maximum limit for the number of all paths between two points to meet the requirements and reach the maximum length. After we retrieve so many paths, we no longer look for them.
HashMap<Node,List<Path>> node2Path=new HashMap<>();// Used to save all paths from node to target node
        HashMap<Node,Set<Node>> visitNode=new HashMap<>();
pathCount=0;//Initialize global variables
        List<Path> result = dnfSearchPath(srcNode, trgNode, maxPathLength, maxPathNum, 0, new HashSet<Node>(), node2Path,visitNode,new HashSet<Node>(), maxTarPathNum);
        return result;
    }

    public static List<Path> dnfSearchPath(Node node,Node trgNode,int maxPathLength,int maxPathNum,int depth,HashSet<Node> visit,HashMap<Node,List<Path>> node2Path,HashMap<Node,Set<Node>> visitNode,HashSet<Node> mark,int maxTarPathNum){
// In-depth search of all paths that meet the conditions, we must ensure that all nodes only access once
if(pathCount>maxPathNum)//If the retrieved path exceeds the maximum limit we set, we also give up on searching
            return null;
if(visit.contains(node)){//Prevent rings
            pathCount++;
            return null;
        }
if(depth>=maxPathLength) {//If the depth of the path has reached the maximum limit we set, we will give up
            pathCount++;
            return null;
        }
if(node==trgNode){//If the target node is found, return
            pathCount++;
            Path path =new Path();
            path.nodes.add(node);
// log.info("find the target node"+node.unit);
            List<Path> result=new ArrayList<>();
            result.add(path);
            node2Path.put(node,result);
            return result;
}else {//If it is not found, you need to continue searching downwards
if(node.successorNodes.isEmpty()){//If the node has no successor
                pathCount++;
                return null;
            }else {
                HashSet<Node> addVisit = new HashSet<>(visit);
                addVisit.add(node);
                List<Path> result=new ArrayList<>();
for (Node succor: node.successorNodes) {//Find all paths to the target node from the child node
                    int beginSize=result.size();
if(mark.contains(succor)&&node2Path.containsKey(succor)) {//If the node has visited and it contains the path to the target node, we will directly use it to save the recorded information before it
addNode2Path(result,node2Path.get(succor),node);//Combines the current node with its previous path
}else if(!mark.contains(node)){//If we have not visited this node, we will query the path to the target node
                        List<Path> paths = dnfSearchPath(succor, trgNode, maxPathLength, maxPathNum, depth + 1, addVisit, node2Path,visitNode,mark,maxTarPathNum);
if(paths!=null){//If there is a path between the child node and the target node, record the path and the machine.
                            addNode2Path(result,paths,node);
                        }
                    }
                    int endSize=result.size();
if(beginSize!=endSize&&endSize!=0) {//If there is a path from this child node to the destination node
//Carry some memory processing work
                        Set<Node> father = new HashSet<>();
                        father.add(node);
if (!visitNode.containsKey(succor)) {//visitNode is used to record the number of accesses in the parent node of the node
                            visitNode.put(succor, father);
                        } else {
                            visitNode.get(succor).add(node);
                        }
if (visitNode.get(succor).size() == succor.precursorNodes.size()) {//If all parent nodes have access to the node, it means that all parent nodes have recorded the path to the target node, we should delete the path saved by these nodes
                            if (node2Path.get(succor) != null) {
                                node2Path.remove(succor);
                            }
                        }
                    }
                }
mark.add(node);//The path information that marks the node has been found
if(result.size()!=0) {//If there is a path to the target node, save the obtained path
// log.info("number of paths is: "+result.size());
if(result.size()>maxTarPathNum){//If the number of paths from this node to the target node is greater than our maximum number, we will randomly select half of the maximum number among these paths
                        List<Path> reducePath=new ArrayList<>();
                        for(int index=0;index<maxTarPathNum/2;index++){
                            reducePath.add(result.get(index));
                        }
                        node2Path.put(node,reducePath);
                        return reducePath;
                    }
                    node2Path.put(node,result);
                    return result;
                }
// log.info("The path from this node to the target node is empty");
                return null;
            }
        }
    }

public static List<Path> addNode2Path(List<Path> result,List<Path> pathList,Node node){//Add the specified node to the end of each path
        for(Path path:pathList){
            Path newPath=new Path();
            newPath.nodes.add(node);
            newPath.nodes.addAll(path.nodes);
            result.add(newPath);
        }
        return result;
    }

    /**
     * 寻找CFG中所有满足特定要求的语句<br>
     * 可以通过重载filter中的apply函数实现自定义的过滤器
     * <br><b>示例</b>
     * <pre>
     * {@code
* //The following example will use a permanently received filter to get all statements in the CFG.
     * HashSet<Unit> registerReceiverUnits = cfg.findUnitWithFilter(new Function<Unit, Boolean>(){
     *       @Override
     *       public Boolean apply(Unit unit) {
     *          return true;
     *       }
     * });
     * }
     * </pre>
     *
     * @param filter 过滤器函数
     * @return {@link HashSet}&lt;{@link Unit}&gt;
     */
    public HashSet<Unit> findUnitWithFilter(Function<Unit, Boolean> filter) {
        HashSet<Unit> ret = new HashSet<>();
        for(Unit unit : allNodes.keySet()){
            if(filter.apply(unit))
                ret.add(unit);
        }
        return ret;
    }

    /**
     * 寻找CFG中所有满足特定要求的语句,返回它们所在的node<br>
     * 可以通过重载filter中的apply函数实现自定义的过滤器
     *
     * @param filter 过滤器函数
     * @return {@link HashSet}&lt;{@link Node}&gt;
     */
    public HashSet<Node> findNodeWithFilter(Function<Node, Boolean> filter) {
        HashSet<Node> ret = new HashSet<>();
        for(Node node : allNodes.values()){
            if(filter.apply(node))
                ret.add(node);
        }
        return ret;
    }


    /**
     * 输出一个节点附近的节点，reverse为false时，打印该语句后继的count条语句；reverse为true时打印该语句前驱的count条语句。
     * 输出结果从起始语句到结束语句缩进的空格数递减。
     *
     * @param node    节点
     * @param count   打印的范围
     * @param reverse 选择前驱或后继
     */
    public void printNearbyNodes(Node node, int count, boolean reverse){
        if(count == 0)return;
        String out = String.format("%" + (count + node.toString().length()) + "s\n", node.toString());
        System.out.print(out);
        if(!reverse){
            for(Node node1 : node.successorNodes){
                printNearbyNodes(node1, count - 1, false);
            }
        }
        else{
            for(Node node1 : node.precursorNodes){
                printNearbyNodes(node1, count - 1, true);
            }
        }
    }

    public void printStackTrace(Node node){
        int lev = 0;
        int count = 0;
        Stack<String> stack = new Stack<>();
        while (node.precursorNodes.size() > 0){
            Node preNode = node.precursorNodes.iterator().next();
            if(node.tag != null && node.tag.equals("BEGIN")){
                String unitStr = preNode.unit.toString();
                stack.push(String.format("%" + (lev + unitStr.length()) + "s\n", unitStr));
                if(lev > 0) lev -= 3;
            }
            else if(node.tag != null && node.tag.equals("END")){
                lev += 3;
            }
            node = preNode;
            if(count++ > 200){
                log.info("Out of limit, terminated");
                break;
            }
        }
        while(!stack.empty()){
            log.info(stack.pop());
        }
    }

    /**
     * 获取方法中可以被用户获取的输入，作为正向污点分析的起点
     * （1.参数 2.getIntent()）
     * 需解决的特殊情况：getIntent()函数并不一定在函数开始时初始化，而是在某些callee中初始化;
     * @return
     */
    public HashMap<Node, ValueBox> fetchControlledInputData(){
        HashMap<Node, ValueBox> result = new HashMap<>();
        try {
            Body body = entryPoint.retrieveActiveBody();
            for (Unit unit:body.getUnits()){
                if (unit instanceof IdentityStmt){
                    Value param = ((IdentityStmt) unit).getRightOp();
                    if (param.getType().toString().equals("android.content.Context")) {}
                    else {
                        result.put(getNodeByUnit(unit),((IdentityStmt) unit).getLeftOpBox());
                    }
                }else if (((Stmt)unit).containsInvokeExpr() && unit instanceof AssignStmt){
                    SootMethod invokeMethod = ((Stmt) unit).getInvokeExpr().getMethod();
                    if (invokeMethod.getSubSignature().equals("android.content.Intent getIntent()"))
                        result.put(getNodeByUnit(unit),((AssignStmt) unit).getLeftOpBox());
                }
            }
        }catch (Exception e){
            return result;
        }
        return result;
    }
}
