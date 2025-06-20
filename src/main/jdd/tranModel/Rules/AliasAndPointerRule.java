package jdd.tranModel.Rules;

import jdd.PointToAnalyze.pointer.Pointer;
import soot.*;
import jdd.tranModel.Rule;
import jdd.tranModel.Taint.Taint;
import jdd.tranModel.Transformable;
import jdd.tranModel.TransformableNode;
import jdd.container.BasicDataContainer;
import jdd.container.FieldsContainer;
import jdd.dataflow.node.MethodDescriptor;
import soot.jimple.*;
import soot.jimple.internal.JAssignStmt;
import soot.jimple.internal.JIdentityStmt;
import soot.jimple.internal.JInstanceFieldRef;
import jdd.util.ClassRelationshipUtils;
import jdd.markers.RelationShip;
import jdd.util.Utils;

public class AliasAndPointerRule implements Rule {

    @Override
    public void apply(Transformable transformable, MethodDescriptor descriptor) {
        TransformableNode tfNode = (TransformableNode) transformable;

        Stmt stmt = (Stmt) tfNode.node.unit;
        if (stmt instanceof AssignStmt){
            AssignStmt assignStmt = (AssignStmt) stmt;
            Value left = assignStmt.getLeftOp();
            Value right = assignStmt.getRightOp();

            if (right instanceof JInstanceFieldRef){
// a = taint.field
                JInstanceFieldRef jInstanceFieldRef = (JInstanceFieldRef) right;
                Value object = jInstanceFieldRef.getBase();
                SootField sootField = jInstanceFieldRef.getField();
// Create a taint (stored in allTaints: Record all "defiles", and the taints are not actually contaminated)
                Taint leftTaint = descriptor.getOrCreateTaint(left,null);
                Taint rightTaint = descriptor.getOrCreateTaint(object, Utils.toLinkedList(sootField));

                if (BasicDataContainer.openAliasAnalysis) {
                    leftTaint.aliases.add(rightTaint);
                }

// Supplementary alias pointer information
                recordPointer(rightTaint,leftTaint, descriptor);
            }
            else if (right instanceof StaticFieldRef){
                SootField sootField = ((StaticFieldRef) right).getField();
                Pointer pointer = FieldsContainer.getFieldPointer(sootField, descriptor.getCurrentClass());
if (pointer != null){ // If it is not a constant, record pointer information
                    descriptor.pointTable.setPointer(left, pointer);
                }

                if (BasicDataContainer.openAliasAnalysis){
                    Taint leftTaint = descriptor.getOrCreateTaint(left,null);
                    Taint rightTaint = descriptor.getOrCreateTaint(descriptor.paramIdMapLocalValue.get(-1), Utils.toLinkedList(sootField));
                    leftTaint.aliases.add(rightTaint);
                }

            }
            else if (left instanceof JInstanceFieldRef){
                JInstanceFieldRef jInstanceFieldRef = (JInstanceFieldRef) left;
                Value object = jInstanceFieldRef.getBase();
                SootField sootField = jInstanceFieldRef.getField();

                Taint rightTaint = descriptor.getOrCreateTaint(right,null);
                Taint leftTaint = descriptor.getOrCreateTaint(object,Utils.toLinkedList(sootField));
                if (BasicDataContainer.openAliasAnalysis)
                    leftTaint.aliases.add(rightTaint);

                recordPointer(rightTaint,leftTaint,descriptor);

            }
            else if (left instanceof StaticFieldRef){
                SootField sootField = ((StaticFieldRef) left).getField();
                if (BasicDataContainer.openAliasAnalysis){
                    Taint leftTaint = descriptor.getOrCreateTaint(left,null);
                    Taint rightTaint = descriptor.getOrCreateTaint(descriptor.paramIdMapLocalValue.get(-1), Utils.toLinkedList(sootField));
                    leftTaint.aliases.add(rightTaint);
                }

                Pointer pointer = FieldsContainer.getFieldPointer(sootField, descriptor.getCurrentClass());
                if (pointer != null)
                    descriptor.pointTable.setPointer(left, pointer);
            }

            else if (right instanceof NewExpr){
                RefType refType = ((NewExpr) right).getBaseType();
                Type type = ((NewExpr) right).getType();
                Pointer pointer = new Pointer(type, refType);
                descriptor.pointTable.setPointer(left, pointer);
            }
// Force type conversion
            else if (right instanceof CastExpr){
                Value rightValue = ((CastExpr)right).getOp();
                Pointer pointer = new Pointer(((CastExpr)right).getCastType());
                descriptor.pointTable.setPointer(left, pointer);
// If the type of right and cast are not fully compatible, the record will be added.
                if (descriptor.pointTable.contains(rightValue)) {
                    SootClass castClass = Utils.toSootClass(((CastExpr) right).getCastType());
                    Pointer pointerRight = descriptor.pointTable.getPointer(rightValue);
                    SootClass rightValueType = Utils.toSootClass(pointerRight.getType());
                    if (ClassRelationshipUtils.getExtentRelationshipAmongClasses(castClass, rightValueType).equals(RelationShip.HAS_SAME_SUB)){
                        pointer.addExtraType(pointerRight.getType());
                    }
                }

                if (BasicDataContainer.openAliasAnalysis){
                    Taint rightTaint = descriptor.getOrCreateTaint(right,null);
                    Taint leftTaint = descriptor.getOrCreateTaint(left,null);
                    leftTaint.aliases.add(rightTaint);
                }
            }
            else if (stmt.containsInvokeExpr()){
                Pointer pointer = new Pointer( stmt.getInvokeExpr().getMethod().getReturnType());
                descriptor.pointTable.setPointer(left,pointer);
            }
            else {
                if (right instanceof ArrayRef)
                    right = ((ArrayRef) right).getBase();
                if (left instanceof ArrayRef)
                    left = ((ArrayRef) left).getBase();
                recordPointer(right,left,descriptor);
                if (BasicDataContainer.openAliasAnalysis){
                    Taint rightTaint = descriptor.getOrCreateTaint(right,null);
                    Taint leftTaint = descriptor.getOrCreateTaint(left,null);
                    leftTaint.aliases.add(rightTaint);
                }
            }
        }

        if (stmt instanceof JIdentityStmt){
            JIdentityStmt jIdentityStmt = (JIdentityStmt) stmt;
            Value left = jIdentityStmt.getLeftOp();
            Value right = jIdentityStmt.getRightOp();

            recordPointer(right, left, descriptor);

            if (BasicDataContainer.openAliasAnalysis){
                Taint rightTaint = descriptor.getOrCreateTaint(right,null);
                Taint leftTaint = descriptor.getOrCreateTaint(left,null);
                leftTaint.aliases.add(rightTaint);
            }
        }

        if (stmt instanceof JAssignStmt){
        }
        if (stmt instanceof NewExpr){

        }
    }

    public static void recordPointer(Value from, Value to, MethodDescriptor descriptor){
        if (!descriptor.pointTable.setPointer(from, to)){
            Pointer pointer = new Pointer(from.getType());
            descriptor.pointTable.setPointer(to,pointer);
        }
    }

    public static void recordPointer(Taint from, Taint to, MethodDescriptor descriptor){
        if (!descriptor.pointTable.setPointer(from,to)){
            Pointer pointer = new Pointer(from.getType());
            descriptor.pointTable.setPointer(to,pointer);
        }
    }
}
