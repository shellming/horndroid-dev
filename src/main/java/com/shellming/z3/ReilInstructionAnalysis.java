package com.shellming.z3;

import com.google.security.zynamics.binnavi.API.disassembly.Operand;
import com.google.security.zynamics.binnavi.API.reil.OperandType;
import com.google.security.zynamics.binnavi.API.reil.ReilInstruction;
import com.google.security.zynamics.binnavi.API.reil.ReilOperand;
import com.microsoft.z3.BitVecExpr;
import com.microsoft.z3.BoolExpr;
import z3.Z3Engine;

import java.util.HashMap;
import java.util.Map;

/**
 * Created by ruluo1992 on 12/4/2016.
 */
public class ReilInstructionAnalysis {
    final private long codeAddress;
    final private ReilEngine engine;
    final private ReilInstruction instruction;
    final private RFunction function;
    final private ReilVariable var;
    final private Z3Engine z3Engine;
    final private Long nextCode;
    public ReilInstructionAnalysis(ReilInstruction reilInstruction, RFunction function, ReilEngine engine, Long nextCode) {
        codeAddress = reilInstruction.getAddress().toLong();
        this.engine = engine;
        this.instruction = reilInstruction;
        this.function = function;
        this.var = engine.getVar();
        this.z3Engine = engine.getZ3Engine();
        this.nextCode = nextCode;
    }

    public void createHornClauses() {
        String opcode = instruction.getMnemonic();

        ReilOperand op1 = instruction.getFirstOperand();
        ReilOperand op2 = instruction.getSecondOperand();
        ReilOperand op3 = instruction.getThirdOperand();
        // idx值有可能为null
        Integer idx1 = function.getRegIdx(op1.toString());
        Integer idx2 = function.getRegIdx(op2.toString());
        Integer idx3 = function.getRegIdx(op3.toString());

        Map<Integer, BitVecExpr> regUpdate = new HashMap<>();
        Map<Integer, BoolExpr> regUpdateL = new HashMap<>();
        Map<Integer, BoolExpr> regUpdateB = new HashMap<>();
        String f = function.getFunName();
        int regNums = function.getRegNums();
        int size = engine.getBvSize();
        BoolExpr h, b;
        BitVecExpr v1, v2;
        BoolExpr l1, l2;
        Long simV1, simV2, simV3;
        switch (opcode) {
            case "add":
                h = engine.rPred(f, codeAddress, regUpdate, regUpdateL, regUpdateB, regNums);
                // add 前两个操作数类型只有两种可能：寄存器和字面量，第三个必然是寄存器
                if (op1.getType() == OperandType.REGISTER) {
                    v1 = var.getV(idx1);
                    l1 = var.getL(idx1);
                    simV1 = engine.getRegSimVal(op1.toString());
                } else {
                    v1 = z3Engine.mkBitVector(Long.valueOf(op1.getValue()), size);
                    l1 = z3Engine.mkFalse();
                    simV1 = Long.valueOf(op1.getValue());
                }
                if (op2.getType() == OperandType.REGISTER) {
                    v2 = var.getV(idx2);
                    l2 = var.getL(idx2);
                    simV2 = engine.getRegSimVal(op2.toString());
                } else {
                    v2 = z3Engine.mkBitVector(Integer.valueOf(op2.getValue()), size);
                    l2 = z3Engine.mkFalse();
                    simV2 = Long.valueOf(op2.getValue());
                }
                regUpdate.put(idx3,
                        z3Engine.bvadd(
                                v1, v2
                        )
                );
                regUpdateL.put(idx3,
                        z3Engine.or(
                                l1, l2
                        )
                );
                b = engine.rPred(f, nextCode, regUpdate, regUpdateL, regUpdateB, regNums);
                z3Engine.addRule(z3Engine.implies(h, b), null);
                if (simV1 != null && simV2 != null) {
                    engine.setRegSimVal(op3.toString(), simV1 + simV2);
                }
                break;
            case "sub":
                h = engine.rPred(f, codeAddress, regUpdate, regUpdateL, regUpdateB, regNums);
                // sub 前两个操作数类型只有两种可能：寄存器和字面量，第三个必然是寄存器
                if (op1.getType() == OperandType.REGISTER) {
                    v1 = var.getV(idx1);
                    l1 = var.getL(idx1);
                    simV1 = engine.getRegSimVal(op1.toString());
                } else {
                    v1 = z3Engine.mkBitVector(Long.valueOf(op1.getValue()), size);
                    l1 = z3Engine.mkFalse();
                    simV1 = Long.valueOf(op1.getValue());
                }
                if (op2.getType() == OperandType.REGISTER) {
                    v2 = var.getV(idx2);
                    l2 = var.getL(idx2);
                    simV2 = engine.getRegSimVal(op2.toString());
                } else {
                    v2 = z3Engine.mkBitVector(Integer.valueOf(op2.getValue()), size);
                    l2 = z3Engine.mkFalse();
                    simV2 = Long.valueOf(op2.getValue());
                }
                regUpdate.put(idx3,
                        z3Engine.bvsub(
                                v1, v2
                        )
                );
                regUpdateL.put(idx3,
                        z3Engine.or(
                                l1, l2
                        )
                );
                b = engine.rPred(f, nextCode, regUpdate, regUpdateL, regUpdateB, regNums);
                z3Engine.addRule(z3Engine.implies(h, b), null);
                if (simV1 != null && simV2 != null) {
                    engine.setRegSimVal(op3.toString(), simV1 - simV2);
                }
                break;
            case "mul":
                h = engine.rPred(f, codeAddress, regUpdate, regUpdateL, regUpdateB, regNums);
                // mul 前两个操作数类型只有两种可能：寄存器和字面量，第三个必然是寄存器
                if (op1.getType() == OperandType.REGISTER) {
                    v1 = var.getV(idx1);
                    l1 = var.getL(idx1);
                    simV1 = engine.getRegSimVal(op1.toString());
                } else {
                    v1 = z3Engine.mkBitVector(Long.valueOf(op1.getValue()), size);
                    l1 = z3Engine.mkFalse();
                    simV1 = Long.valueOf(op1.getValue());
                }
                if (op2.getType() == OperandType.REGISTER) {
                    v2 = var.getV(idx2);
                    l2 = var.getL(idx2);
                    simV2 = engine.getRegSimVal(op2.toString());
                } else {
                    v2 = z3Engine.mkBitVector(Integer.valueOf(op2.getValue()), size);
                    l2 = z3Engine.mkFalse();
                    simV2 = Long.valueOf(op2.getValue());
                }
                regUpdate.put(idx3,
                        z3Engine.bvmul(
                                v1, v2
                        )
                );
                regUpdateL.put(idx3,
                        z3Engine.or(
                                l1, l2
                        )
                );
                b = engine.rPred(f, nextCode, regUpdate, regUpdateL, regUpdateB, regNums);
                z3Engine.addRule(z3Engine.implies(h, b), null);
                if (simV1 != null && simV2 != null) {
                    engine.setRegSimVal(op3.toString(), simV1 * simV2);
                }
                break;
            case "div":
                h = engine.rPred(f, codeAddress, regUpdate, regUpdateL, regUpdateB, regNums);
                // div 前两个操作数类型只有两种可能：寄存器和字面量，第三个必然是寄存器
                if (op1.getType() == OperandType.REGISTER) {
                    v1 = var.getV(idx1);
                    l1 = var.getL(idx1);
                    simV1 = engine.getRegSimVal(op1.toString());
                } else {
                    v1 = z3Engine.mkBitVector(Long.valueOf(op1.getValue()), size);
                    l1 = z3Engine.mkFalse();
                    simV1 = Long.valueOf(op1.getValue());
                }
                if (op2.getType() == OperandType.REGISTER) {
                    v2 = var.getV(idx2);
                    l2 = var.getL(idx2);
                    simV2 = engine.getRegSimVal(op2.toString());
                } else {
                    v2 = z3Engine.mkBitVector(Integer.valueOf(op2.getValue()), size);
                    l2 = z3Engine.mkFalse();
                    simV2 = Long.valueOf(op2.getValue());
                }
                regUpdate.put(idx3,
                        z3Engine.bvudiv(
                                v1, v2
                        )
                );
                regUpdateL.put(idx3,
                        z3Engine.or(
                                l1, l2
                        )
                );
                b = engine.rPred(f, nextCode, regUpdate, regUpdateL, regUpdateB, regNums);
                z3Engine.addRule(z3Engine.implies(h, b), null);
                if (simV1 != null && simV2 != null) {
                    engine.setRegSimVal(op3.toString(), simV1 / simV2);
                }
                break;
            case "mod":
                h = engine.rPred(f, codeAddress, regUpdate, regUpdateL, regUpdateB, regNums);
                // div 前两个操作数类型只有两种可能：寄存器和字面量，第三个必然是寄存器
                if (op1.getType() == OperandType.REGISTER) {
                    v1 = var.getV(idx1);
                    l1 = var.getL(idx1);
                    simV1 = engine.getRegSimVal(op1.toString());
                } else {
                    v1 = z3Engine.mkBitVector(Long.valueOf(op1.getValue()), size);
                    l1 = z3Engine.mkFalse();
                    simV1 = Long.valueOf(op1.getValue());
                }
                if (op2.getType() == OperandType.REGISTER) {
                    v2 = var.getV(idx2);
                    l2 = var.getL(idx2);
                    simV2 = engine.getRegSimVal(op2.toString());
                } else {
                    v2 = z3Engine.mkBitVector(Integer.valueOf(op2.getValue()), size);
                    l2 = z3Engine.mkFalse();
                    simV2 = Long.valueOf(op2.getValue());
                }
                regUpdate.put(idx3,
                        engine.bvsmod(
                                v1, v2
                        )
                );
                regUpdateL.put(idx3,
                        z3Engine.or(
                                l1, l2
                        )
                );
                b = engine.rPred(f, nextCode, regUpdate, regUpdateL, regUpdateB, regNums);
                z3Engine.addRule(z3Engine.implies(h, b), null);
                if (simV1 != null && simV2 != null) {
                    engine.setRegSimVal(op3.toString(), simV1 % simV2);
                }
                break;
            case "bsh":
                h = engine.rPred(f, codeAddress, regUpdate, regUpdateL, regUpdateB, regNums);
                // bsh 第二个操作数只可能为字面量，若为正数，则左移，否则右移
                if (op1.getType() == OperandType.REGISTER) {
                    v1 = var.getV(idx1);
                    l1 = var.getL(idx1);
                    simV1 = engine.getRegSimVal(op1.toString());
                } else {
                    v1 = z3Engine.mkBitVector(Long.valueOf(op1.getValue()), size);
                    l1 = z3Engine.mkFalse();
                    simV1 = Long.valueOf(op1.getValue());
                }
                simV2 = Long.valueOf(op2.getValue());
                v2 = z3Engine.mkBitVector(simV2 > 0 ? simV2 : -1 * simV2, size);
                l2 = z3Engine.mkFalse();
                if (simV2 > 0) {
                    regUpdate.put(idx3,
                            z3Engine.bvshl(
                                    v1, v2
                            )
                    );
                    if (simV1 != null && simV2 != null) {
                        engine.setRegSimVal(op3.toString(), simV1 << simV2);
                    }
                } else {
                    regUpdate.put(idx3,
                            z3Engine.bvlshr( // 逻辑移位，不考虑正负号
                                    v1, v2
                            )
                    );
                    if (simV1 != null && simV2 != null) {
                        engine.setRegSimVal(op3.toString(), simV1 >> (-1 *simV2));
                    }
                }
                regUpdateL.put(idx3,
                        z3Engine.or(
                                l1, l2
                        )
                );
                b = engine.rPred(f, nextCode, regUpdate, regUpdateL, regUpdateB, regNums);
                z3Engine.addRule(z3Engine.implies(h, b), null);
                break;
        }

    }
}
