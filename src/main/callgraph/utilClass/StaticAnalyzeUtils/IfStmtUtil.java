package callgraph.utilClass.StaticAnalyzeUtils;

import callgraph.cfg.Node;
import soot.ValueBox;

import java.util.regex.Pattern;
/**
 * Basic static analysis capabilities
 */
public class IfStmtUtil {
    public static ValueBox getConditionExprBox(Node node){
        for(ValueBox valueBox : node.unit.getUseBoxes()){
            if(valueBox.toString().contains("ConditionExprBox")) return valueBox;
        }
        return null;
    }

    public static ValueBox tryGetImmediateNum(Node node){
        String pattern = ".*\\(.*[a-zA-Z].*\\).*";
        for(ValueBox valueBox : node.unit.getUseBoxes()){
            if(valueBox.toString().contains("ImmediateBox")) {
                if(Pattern.matches(pattern, valueBox.toString())) continue;
                return valueBox;
            }
        }
        return null;
    }
}
