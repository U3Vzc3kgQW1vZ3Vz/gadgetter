package jdd.container;

import jdd.tranModel.Rules.AliasAndPointerRule;
import jdd.tranModel.Rules.JoinRule;
import jdd.tranModel.Rules.TaintGenerateRule;
import jdd.tranModel.Rules.TaintSpreadRule;
import jdd.tranModel.Transformable;
import jdd.gadgets.collection.node.ConditionUtils;
import jdd.gadgets.collection.rule.ConditionCheck;
import jdd.gadgets.collection.rule.DependenceCheck;
import jdd.gadgets.collection.rule.SinkCheck;
import jdd.rules.sinks.*;
import jdd.structure.RuleDataStructure;
import jdd.util.DataSaveLoadUtil;

import java.io.IOException;

public class RulesContainer {
public static RuleDataStructure ruleDataStructure = null; // The default is not null after initialization

    public static void reset(){
        ruleDataStructure = null;
    }

    public static void init() throws IOException {
        DataSaveLoadUtil.loadRuleDataStructure();
// Assign Rules[gadget chains detection]
        loadCheckRules();
// Loading taint propagation Rules
        loadTransRules();
        loadIOCDInferRules();
        loadBasicConfigOfCheckRules();
    }

    public static void loadCheckRules(){
        ClassLoaderCheckRule.init();
        ExecCheckRule.init();
        FileCheckRule.init();
        InvokeCheckRule.init();
        JNDICheckRule.init();
        SecondDesCheckRule.init();
        CustomCheckRule.init();

// ConditionNode.init()

    }

    public static void loadTransRules(){
        Transformable.clearRules();
Transformable.addRule(new JoinRule()); // This must be the first to join
// TransformableNode.addRule(new PointToRule());
        Transformable.addRule(new TaintSpreadRule());
        Transformable.addRule(new AliasAndPointerRule());
        Transformable.addRule(new TaintGenerateRule());
    }

    public static void loadIOCDInferRules(){
        Transformable.clearInferRules();
        Transformable.addInferRule(new DependenceCheck());
        Transformable.addInferRule(new ConditionCheck());
        Transformable.addInferRule(new SinkCheck());

        Transformable.clearExtraInferRules();
        Transformable.addExtraInferRule(new DependenceCheck());
        Transformable.addExtraInferRule(new ConditionCheck());
    }

    public static void loadBasicConfigOfCheckRules(){
        ConditionUtils.init();
    }
}
