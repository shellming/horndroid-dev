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
    final private Map<Long, String> addr2fun;
    final private Map<String, RFunction> name2fun;
    public ReilInstructionAnalysis(ReilInstruction reilInstruction, RFunction function, ReilEngine engine, Long nextCode,
                                   Map<Long, String> addr2fun, Map<String, RFunction> name2fun) {
        codeAddress = reilInstruction.getAddress().toLong();
        this.engine = engine;
        this.instruction = reilInstruction;
        this.function = function;
        this.var = engine.getVar();
        this.z3Engine = engine.getZ3Engine();
        this.nextCode = nextCode;
        this.addr2fun = addr2fun;
        this.name2fun = name2fun;
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
                } else {
                    engine.setRegSimVal(op3.toString(), null);
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
                } else {
                    engine.setRegSimVal(op3.toString(), null);
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
                } else {
                    engine.setRegSimVal(op3.toString(), null);
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
                } else {
                    engine.setRegSimVal(op3.toString(), null);
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
                }  else {
                    engine.setRegSimVal(op3.toString(), null);
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
                if (simV1 != null && simV2 != null) {
                    if (simV2 < 0) {
                        engine.setRegSimVal(op3.toString(), simV1 >> simV2);
                    } else {
                        engine.setRegSimVal(op3.toString(), simV1 << simV2);
                    }
                } else {
                    engine.setRegSimVal(op3.toString(), null);
                }
                break;
            case "and":
                h = engine.rPred(f, codeAddress, regUpdate, regUpdateL, regUpdateB, regNums);
                // and 前两个操作数类型只有两种可能：寄存器和字面量，第三个必然是寄存器
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
                        z3Engine.bvand(
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
                    engine.setRegSimVal(op3.toString(), simV1 & simV2);
                } else {
                    engine.setRegSimVal(op3.toString(), null);
                }
                break;
            case "or":
                h = engine.rPred(f, codeAddress, regUpdate, regUpdateL, regUpdateB, regNums);
                // and 前两个操作数类型只有两种可能：寄存器和字面量，第三个必然是寄存器
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
                        z3Engine.bvor(
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
                    engine.setRegSimVal(op3.toString(), simV1 | simV2);
                } else {
                    engine.setRegSimVal(op3.toString(), null);
                }
                break;
            case "xor":
                h = engine.rPred(f, codeAddress, regUpdate, regUpdateL, regUpdateB, regNums);
                // xor 前两个操作数类型只有两种可能：寄存器和字面量，第三个必然是寄存器
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
                        z3Engine.bvxor(
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
                    engine.setRegSimVal(op3.toString(), simV1 ^ simV2);
                } else {
                    engine.setRegSimVal(op3.toString(), null);
                }
                break;
            case "bisz":
                h = engine.rPred(f, codeAddress, regUpdate, regUpdateL, regUpdateB, regNums);
                // BISZ 仅有两个操作数，op2 位 EMPTY，op1为寄存器或立即数，op3为寄存器
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
                        (BitVecExpr) z3Engine.ite(
                                z3Engine.eq(        //if
                                        v1,
                                        z3Engine.mkBitVector(0, size)
                                ),
                                z3Engine.mkBitVector(1, size), //then
                                z3Engine.mkBitVector(0, size) // else
                        )
                );
                regUpdateL.put(idx3,
                        l1
                );
                b = engine.rPred(f, nextCode, regUpdate, regUpdateL, regUpdateB, regNums);
                z3Engine.addRule(z3Engine.implies(h, b), null);
                engine.setRegSimVal(op3.toString(), null);
                break;

            case "jcc":
                Long jump = null;
                // JCC 仅有两个操作数，op2 位 EMPTY，op1为寄存器或立即数，op3为地址或立即数或寄存器，地址存储同一条原始指令内部的偏移
                // op1为非零时则跳转，否则执行下一条指令
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
                    simV2 = engine.getRegSimVal(op2.toString());  // 获取估算出的寄存器值，若该值为空，则忽略该条跳转指令
                    if (simV2 != null) {
                        jump = simV2 << 8; // reil 地址
                    }
                } else if (op2.getType() == OperandType.INTEGER_LITERAL) {
                    v2 = z3Engine.mkBitVector(Integer.valueOf(op2.getValue()), size);
                    l2 = z3Engine.mkFalse();
                    simV2 = Long.valueOf(op2.getValue());
                    jump = simV2 << 8;
                } else { // 操作数类型为偏移值，此时计算指令偏移
                    // 偏移值一般以 指令地址.偏移值 的格式存储
                    String a = op2.getValue();
                    String[] parts = a.split("\\.");
                    Long a1 = Long.valueOf(parts[0]);
                    Long a2 = Long.valueOf(parts[1]);
                    jump = a1 << 8 + a2;
                }
                if (jump == null) { // 如果无法确定jump地址，则无条件执行下一条指令
                    h = engine.rPred(f, codeAddress, regUpdate, regUpdateL, regUpdateB, regNums);
                    b = engine.rPred(f, nextCode, regUpdate, regUpdateL, regUpdateB, regNums);
                    z3Engine.addRule(z3Engine.implies(h, b), null);
                    break;
                }
                // 如果为普通跳转
                if (!this.instruction.getMetaData().containsKey("isCall")) {
                    // 处理为0的情况，执行下一条语句
                    h = z3Engine.and(
                            engine.rPred(f, codeAddress, regUpdate, regUpdateL, regUpdateB, regNums),
                            z3Engine.eq(
                                    v1,
                                    z3Engine.mkBitVector(0, size)
                            )
                    );
                    b = engine.rPred(f, nextCode, regUpdate, regUpdateL, regUpdateB, regNums);
                    z3Engine.addRule(z3Engine.implies(h, b), null);

                    // 处理非0的情况，跳转到 jump 地址（仍在函数内，不需要做寄存器值的转换）
                    h = z3Engine.and(
                            engine.rPred(f, codeAddress, regUpdate, regUpdateL, regUpdateB, regNums),
                            z3Engine.not(z3Engine.eq(
                                    v1,
                                    z3Engine.mkBitVector(0, size)
                            ))
                    );
                    b = engine.rPred(f, jump, regUpdate, regUpdateL, regUpdateB, regNums);
                    z3Engine.addRule(z3Engine.implies(h, b), null);
                } else {  // 如果为函数跳转
                    String funName = addr2fun.get(jump);
                    if (funName == null) { // 无法确定目标函数，无条件执行下一条指令
                        h = engine.rPred(f, codeAddress, regUpdate, regUpdateL, regUpdateB, regNums);
                        b = engine.rPred(f, nextCode, regUpdate, regUpdateL, regUpdateB, regNums);
                        z3Engine.addRule(z3Engine.implies(h, b), null);
                        break;
                    }
                    // 处理为0的情况，执行下一条语句
                    h = z3Engine.and(
                            engine.rPred(f, codeAddress, regUpdate, regUpdateL, regUpdateB, regNums),
                            z3Engine.eq(
                                    v1,
                                    z3Engine.mkBitVector(0, size)
                            )
                    );
                    b = engine.rPred(f, nextCode, regUpdate, regUpdateL, regUpdateB, regNums);
                    z3Engine.addRule(z3Engine.implies(h, b), null);
                    // 处理非0的情况，跳转到 jump 地址（在另外的函数中，需要做寄存器地址转换）
                    h = z3Engine.and(
                            engine.rPred(f, codeAddress, regUpdate, regUpdateL, regUpdateB, regNums),
                            z3Engine.not(z3Engine.eq(
                                    v1,
                                    z3Engine.mkBitVector(0, size)
                            ))
                    );
                    RFunction funTo = name2fun.get(funName);
                    Map<Integer, BitVecExpr> newRegV = updateRegisterV(function, funTo, size);
                    Map<Integer, BoolExpr> newRegL = updateRegisterL(function, funTo);
                    Map<Integer, BoolExpr> newRegB = updateRegisterB(function, funTo);

                    b = engine.rPred(f, jump, newRegV, newRegL, newRegB, funTo.getRegNums());
                    z3Engine.addRule(z3Engine.implies(h, b), null);

                    // TODO 对 source、sink函数做额外处理

                    BoolExpr subh = engine.rPred(f, codeAddress, regUpdate, regUpdateL, regUpdateB, regNums);
                    h = z3Engine.and(
                            subh,
                            engine.resPred(funName, newRegV, newRegL, newRegB, funTo.getRegNums())
                    );
                    b = engine.rPred(f, nextCode, regUpdate, regUpdateL, regUpdateB, regNums);
                    z3Engine.addRule(z3Engine.implies(h, b), null);
                    break;
                }
//                regUpdateL.put(idx3,
//                        l1
//                );
//                b = engine.rPred(f, nextCode, regUpdate, regUpdateL, regUpdateB, regNums);
//                z3Engine.addRule(z3Engine.implies(h, b), null);
//                engine.setRegSimVal(op3.toString(), null);
                break;
            case "str":
                h = engine.rPred(f, codeAddress, regUpdate, regUpdateL, regUpdateB, regNums);
                // str 仅有两个操作数，op2 位 EMPTY，op1为寄存器或立即数，op3为寄存器
                if (op1.getType() == OperandType.REGISTER) {
                    v1 = var.getV(idx1);
                    l1 = var.getL(idx1);
                    simV1 = engine.getRegSimVal(op1.toString());
                } else {
                    v1 = z3Engine.mkBitVector(Long.valueOf(op1.getValue()), size);
                    l1 = z3Engine.mkFalse();
                    simV1 = Long.valueOf(op1.getValue());
                }
                regUpdate.put(idx3,
                        v1
                );
                regUpdateL.put(idx3,
                        l1
                );
                b = engine.rPred(f, nextCode, regUpdate, regUpdateL, regUpdateB, regNums);
                z3Engine.addRule(z3Engine.implies(h, b), null);
                if (simV1 != null) {
                    engine.setRegSimVal(op3.toString(), simV1);
                } else {
                    engine.setRegSimVal(op3.toString(), null);
                }
                break;
        }

    }

    public boolean isSink(RFunction function) {
        return false;
    }

    public Map<Integer, BitVecExpr> updateRegisterV(RFunction from, RFunction to, int size) {
        Map<Integer, BitVecExpr> regUp = new HashMap<>();
        for (int i = 0; i < to.getRegNums(); i++) {
            String name = to.getRegName(i);
            Integer oldIdx = from.getRegIdx(name);
            if (oldIdx != null) {
                regUp.put(i, var.getV(oldIdx));
            } else {
                regUp.put(i, z3Engine.mkBitVector(0, size));
            }
        }
        return regUp;
    }

    public Map<Integer, BoolExpr> updateRegisterL(RFunction from, RFunction to) {
        Map<Integer, BoolExpr> regUp = new HashMap<>();
        for (int i = 0; i < to.getRegNums(); i++) {
            String name = to.getRegName(i);
            Integer oldIdx = from.getRegIdx(name);
            if (oldIdx != null) {
                regUp.put(i, var.getL(oldIdx));
            } else {
                regUp.put(i, z3Engine.mkFalse());
            }
        }
        return regUp;
    }

    public Map<Integer, BoolExpr> updateRegisterB(RFunction from, RFunction to) {
        Map<Integer, BoolExpr> regUp = new HashMap<>();
        for (int i = 0; i < to.getRegNums(); i++) {
            String name = to.getRegName(i);
            Integer oldIdx = from.getRegIdx(name);
            if (oldIdx == null) {
                regUp.put(i, var.getB(oldIdx));
            } else {
                regUp.put(i, z3Engine.mkFalse());
            }
        }
        return regUp;
    }
}
