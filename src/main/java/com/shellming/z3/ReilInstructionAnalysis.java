package com.shellming.z3;

import com.google.security.zynamics.binnavi.API.disassembly.Operand;
import com.google.security.zynamics.binnavi.API.reil.OperandType;
import com.google.security.zynamics.binnavi.API.reil.ReilInstruction;
import com.google.security.zynamics.binnavi.API.reil.ReilOperand;
import com.microsoft.z3.BitVecExpr;
import com.microsoft.z3.BoolExpr;
import z3.Z3Engine;
import z3.Z3Query;
import z3.Z3Variable;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
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
    final private Boolean isReturn;
    public ReilInstructionAnalysis(ReilInstruction reilInstruction, RFunction function, ReilEngine engine, Long nextCode,
                                   Map<Long, String> addr2fun, Map<String, RFunction> name2fun, Boolean isReturn) {
        codeAddress = reilInstruction.getAddress().toLong();
        this.engine = engine;
        this.instruction = reilInstruction;
        this.function = function;
        this.var = engine.getVar();
        this.z3Engine = engine.getZ3Engine();
        this.nextCode = nextCode;
        this.addr2fun = addr2fun;
        this.name2fun = name2fun;
        this.isReturn = isReturn;
    }

    public void createHornClauses() {
        String opcode = instruction.getMnemonic();

        ReilOperand op1 = instruction.getFirstOperand();
        ReilOperand op2 = instruction.getSecondOperand();
        ReilOperand op3 = instruction.getThirdOperand();

        String f = function.getFunName();
        int size = engine.getBvSize();
        BoolExpr h, b;
        BitVecExpr v1, v2, v3;
        BoolExpr l1, l2, l3;
        BoolExpr b1, b2, b3;
        List<BoolExpr> conditions = new ArrayList<>();  // 保存前提条件 ，R_1 & REG_a(A, B, C) => Reg_c(xxxxx)
        String name1, name2, name3;
        int hash1, hash2, hash3;
        BoolExpr result;
        Long simV1, simV2, simV3;
        if (isReturn) {
            int hash = "r0".hashCode();
            h = z3Engine.and(
                    engine.regPred("r0", var.getV(hash), var.getL(hash), var.getB(hash)),
                    engine.rPred(f, codeAddress)
            );
            b = engine.resPred(f, var.getV(hash), var.getL(hash), var.getB(hash));
            z3Engine.addRule(z3Engine.implies(h, b), null);
            return;
        }
        switch (opcode) {
            case "add":
                h = engine.rPred(f, codeAddress);
                b = engine.rPred(f, nextCode);
                z3Engine.addRule(z3Engine.implies(h, b), null);
                // add 前两个操作数类型只有两种可能：寄存器和字面量，第三个必然是寄存器
                if (op1.getType() == OperandType.REGISTER) {
                    name1 = op1.toString();
                    hash1 = name1.hashCode();
                    v1 = var.getV(hash1);
                    l1 = var.getL(hash1);
                    conditions.add(engine.regPred(name1, null, null, null));
                } else {
                    v1 = z3Engine.mkBitVector(Long.valueOf(op1.getValue()), size);
                    l1 = z3Engine.mkFalse();
                }
                if (op2.getType() == OperandType.REGISTER) {
                    name2 = op2.toString();
                    hash2 = name2.hashCode();
                    v2 = var.getV(hash2);
                    l2 = var.getL(hash2);
                    conditions.add(engine.regPred(name2, null, null, null));
                } else {
                    v2 = z3Engine.mkBitVector(Long.valueOf(op2.getValue()), size);
                    l2 = z3Engine.mkFalse();
                }
                name3 = op3.toString();

                result = engine.regPred(
                        name3,
                        z3Engine.bvadd(v1, v2),
                        z3Engine.or(l1, l2),
                        z3Engine.mkFalse()
                );
                conditions.add(h);
                z3Engine.addRule(z3Engine.implies(
                        z3Engine.and(
                                conditions.toArray(new BoolExpr[0])
                        ),
                        result
                ), null);

                break;
            case "sub":
                h = engine.rPred(f, codeAddress);
                b = engine.rPred(f, nextCode);
                z3Engine.addRule(z3Engine.implies(h, b), null);
                // sub 前两个操作数类型只有两种可能：寄存器和字面量，第三个必然是寄存器
                if (op1.getType() == OperandType.REGISTER) {
                    name1 = op1.toString();
                    hash1 = name1.hashCode();
                    v1 = var.getV(hash1);
                    l1 = var.getL(hash1);
                    conditions.add(engine.regPred(name1, null, null, null));
                } else {
                    v1 = z3Engine.mkBitVector(Long.valueOf(op1.getValue()), size);
                    l1 = z3Engine.mkFalse();
                }
                if (op2.getType() == OperandType.REGISTER) {
                    name2 = op2.toString();
                    hash2 = name2.hashCode();
                    v2 = var.getV(hash2);
                    l2 = var.getL(hash2);
                    conditions.add(engine.regPred(name2, null, null, null));
                } else {
                    v2 = z3Engine.mkBitVector(Long.valueOf(op2.getValue()), size);
                    l2 = z3Engine.mkFalse();
                }
                name3 = op3.toString();

                result = engine.regPred(
                        name3,
                        z3Engine.bvsub(v1, v2),
                        z3Engine.or(l1, l2),
                        z3Engine.mkFalse()
                );
                conditions.add(h);
                z3Engine.addRule(z3Engine.implies(
                        z3Engine.and(
                                conditions.toArray(new BoolExpr[0])
                        ),
                        result
                ), null);

                break;
            case "mul":
                h = engine.rPred(f, codeAddress);
                b = engine.rPred(f, nextCode);
                z3Engine.addRule(z3Engine.implies(h, b), null);
                // mul 前两个操作数类型只有两种可能：寄存器和字面量，第三个必然是寄存器
                if (op1.getType() == OperandType.REGISTER) {
                    name1 = op1.toString();
                    hash1 = name1.hashCode();
                    v1 = var.getV(hash1);
                    l1 = var.getL(hash1);
                    conditions.add(engine.regPred(name1, null, null, null));
                } else {
                    v1 = z3Engine.mkBitVector(Long.valueOf(op1.getValue()), size);
                    l1 = z3Engine.mkFalse();
                }
                if (op2.getType() == OperandType.REGISTER) {
                    name2 = op2.toString();
                    hash2 = name2.hashCode();
                    v2 = var.getV(hash2);
                    l2 = var.getL(hash2);
                    conditions.add(engine.regPred(name2, null, null, null));
                } else {
                    v2 = z3Engine.mkBitVector(Long.valueOf(op2.getValue()), size);
                    l2 = z3Engine.mkFalse();
                }
                name3 = op3.toString();

                result = engine.regPred(
                        name3,
                        z3Engine.bvmul(v1, v2),
                        z3Engine.or(l1, l2),
                        z3Engine.mkFalse()
                );
                conditions.add(h);
                z3Engine.addRule(z3Engine.implies(
                        z3Engine.and(
                                conditions.toArray(new BoolExpr[0])
                        ),
                        result
                ), null);

                break;
            case "div":
                h = engine.rPred(f, codeAddress);
                b = engine.rPred(f, nextCode);
                z3Engine.addRule(z3Engine.implies(h, b), null);
                // div 前两个操作数类型只有两种可能：寄存器和字面量，第三个必然是寄存器
                if (op1.getType() == OperandType.REGISTER) {
                    name1 = op1.toString();
                    hash1 = name1.hashCode();
                    v1 = var.getV(hash1);
                    l1 = var.getL(hash1);
                    conditions.add(engine.regPred(name1, null, null, null));
                } else {
                    v1 = z3Engine.mkBitVector(Long.valueOf(op1.getValue()), size);
                    l1 = z3Engine.mkFalse();
                }
                if (op2.getType() == OperandType.REGISTER) {
                    name2 = op2.toString();
                    hash2 = name2.hashCode();
                    v2 = var.getV(hash2);
                    l2 = var.getL(hash2);
                    conditions.add(engine.regPred(name2, null, null, null));
                } else {
                    v2 = z3Engine.mkBitVector(Long.valueOf(op2.getValue()), size);
                    l2 = z3Engine.mkFalse();
                }
                name3 = op3.toString();

                result = engine.regPred(
                        name3,
                        z3Engine.bvudiv(v1, v2),
                        z3Engine.or(l1, l2),
                        z3Engine.mkFalse()
                );
                conditions.add(h);
                z3Engine.addRule(z3Engine.implies(
                        z3Engine.and(
                                conditions.toArray(new BoolExpr[0])
                        ),
                        result
                ), null);

                break;
            case "mod":
                h = engine.rPred(f, codeAddress);
                b = engine.rPred(f, nextCode);
                z3Engine.addRule(z3Engine.implies(h, b), null);
                // mod 前两个操作数类型只有两种可能：寄存器和字面量，第三个必然是寄存器
                if (op1.getType() == OperandType.REGISTER) {
                    name1 = op1.toString();
                    hash1 = name1.hashCode();
                    v1 = var.getV(hash1);
                    l1 = var.getL(hash1);
                    conditions.add(engine.regPred(name1, null, null, null));
                } else {
                    v1 = z3Engine.mkBitVector(Long.valueOf(op1.getValue()), size);
                    l1 = z3Engine.mkFalse();
                }
                if (op2.getType() == OperandType.REGISTER) {
                    name2 = op2.toString();
                    hash2 = name2.hashCode();
                    v2 = var.getV(hash2);
                    l2 = var.getL(hash2);
                    conditions.add(engine.regPred(name2, null, null, null));
                } else {
                    v2 = z3Engine.mkBitVector(Long.valueOf(op2.getValue()), size);
                    l2 = z3Engine.mkFalse();
                }
                name3 = op3.toString();

                result = engine.regPred(
                        name3,
                        engine.bvsmod(v1, v2),
                        z3Engine.or(l1, l2),
                        z3Engine.mkFalse()
                );
                conditions.add(h);
                z3Engine.addRule(z3Engine.implies(
                        z3Engine.and(
                                conditions.toArray(new BoolExpr[0])
                        ),
                        result
                ), null);

                break;
            case "bsh":
                h = engine.rPred(f, codeAddress);
                b = engine.rPred(f, nextCode);
                z3Engine.addRule(z3Engine.implies(h, b), null);
                // bsh 第二个操作数只可能为字面量，若为正数，则左移，否则右移
                if (op1.getType() == OperandType.REGISTER) {
                    name1 = op1.toString();
                    hash1 = name1.hashCode();
                    v1 = var.getV(hash1);
                    l1 = var.getL(hash1);
                    conditions.add(engine.regPred(name1, null, null, null));
                } else {
                    v1 = z3Engine.mkBitVector(Long.valueOf(op1.getValue()), size);
                    l1 = z3Engine.mkFalse();
                }
                simV2 = Long.valueOf(op2.getValue());
                v2 = z3Engine.mkBitVector(simV2 > 0 ? simV2 : -1 * simV2, size);
                l2 = z3Engine.mkFalse();
                name3 = op3.toString();
                if (simV2 > 0) {
                    result = engine.regPred(
                            name3,
                            z3Engine.bvshl(v1, v2),
                            l1,
                            null
                    );
                } else {
                    result = engine.regPred(
                            name3,
                            z3Engine.bvlshr(v1, v2),  // 逻辑移位，不考虑正负号
                            l1,
                            null
                    );
                }
                conditions.add(h);
                z3Engine.addRule(z3Engine.implies(
                        z3Engine.and(
                                conditions.toArray(new BoolExpr[0])
                        ),
                        result
                ), null);

                break;
            case "and":
                h = engine.rPred(f, codeAddress);
                b = engine.rPred(f, nextCode);
                z3Engine.addRule(z3Engine.implies(h, b), null);
                // and 前两个操作数类型只有两种可能：寄存器和字面量，第三个必然是寄存器
                if (op1.getType() == OperandType.REGISTER) {
                    name1 = op1.toString();
                    hash1 = name1.hashCode();
                    v1 = var.getV(hash1);
                    l1 = var.getL(hash1);
                    conditions.add(engine.regPred(name1, null, null, null));
                } else {
                    v1 = z3Engine.mkBitVector(Long.valueOf(op1.getValue()), size);
                    l1 = z3Engine.mkFalse();
                }
                if (op2.getType() == OperandType.REGISTER) {
                    name2 = op2.toString();
                    hash2 = name2.hashCode();
                    v2 = var.getV(hash2);
                    l2 = var.getL(hash2);
                    conditions.add(engine.regPred(name2, null, null, null));
                } else {
                    v2 = z3Engine.mkBitVector(Long.valueOf(op2.getValue()), size);
                    l2 = z3Engine.mkFalse();
                }
                name3 = op3.toString();

                result = engine.regPred(
                        name3,
                        z3Engine.bvand(v1, v2),
                        z3Engine.or(l1, l2),
                        z3Engine.mkFalse()
                );
                conditions.add(h);
                z3Engine.addRule(z3Engine.implies(
                        z3Engine.and(
                                conditions.toArray(new BoolExpr[0])
                        ),
                        result
                ), null);

                break;
            case "or":
                h = engine.rPred(f, codeAddress);
                b = engine.rPred(f, nextCode);
                z3Engine.addRule(z3Engine.implies(h, b), null);
                // or 前两个操作数类型只有两种可能：寄存器和字面量，第三个必然是寄存器
                if (op1.getType() == OperandType.REGISTER) {
                    name1 = op1.toString();
                    hash1 = name1.hashCode();
                    v1 = var.getV(hash1);
                    l1 = var.getL(hash1);
                    conditions.add(engine.regPred(name1, null, null, null));
                } else {
                    v1 = z3Engine.mkBitVector(Long.valueOf(op1.getValue()), size);
                    l1 = z3Engine.mkFalse();
                }
                if (op2.getType() == OperandType.REGISTER) {
                    name2 = op2.toString();
                    hash2 = name2.hashCode();
                    v2 = var.getV(hash2);
                    l2 = var.getL(hash2);
                    conditions.add(engine.regPred(name2, null, null, null));
                } else {
                    v2 = z3Engine.mkBitVector(Long.valueOf(op2.getValue()), size);
                    l2 = z3Engine.mkFalse();
                }
                name3 = op3.toString();

                result = engine.regPred(
                        name3,
                        z3Engine.bvor(v1, v2),
                        z3Engine.or(l1, l2),
                        null
                );
                conditions.add(h);
                z3Engine.addRule(z3Engine.implies(
                        z3Engine.and(
                                conditions.toArray(new BoolExpr[0])
                        ),
                        result
                ), null);

                break;
            case "xor":
                h = engine.rPred(f, codeAddress);
                b = engine.rPred(f, nextCode);
                z3Engine.addRule(z3Engine.implies(h, b), null);
                // xor 前两个操作数类型只有两种可能：寄存器和字面量，第三个必然是寄存器
                if (op1.getType() == OperandType.REGISTER) {
                    name1 = op1.toString();
                    hash1 = name1.hashCode();
                    v1 = var.getV(hash1);
                    l1 = var.getL(hash1);
                    conditions.add(engine.regPred(name1, null, null, null));
                } else {
                    v1 = z3Engine.mkBitVector(Long.valueOf(op1.getValue()), size);
                    l1 = z3Engine.mkFalse();
                }
                if (op2.getType() == OperandType.REGISTER) {
                    name2 = op2.toString();
                    hash2 = name2.hashCode();
                    v2 = var.getV(hash2);
                    l2 = var.getL(hash2);
                    conditions.add(engine.regPred(name2, null, null, null));
                } else {
                    v2 = z3Engine.mkBitVector(Long.valueOf(op2.getValue()), size);
                    l2 = z3Engine.mkFalse();
                }
                name3 = op3.toString();

                result = engine.regPred(
                        name3,
                        z3Engine.bvxor(v1, v2),
                        z3Engine.or(l1, l2),
                        z3Engine.mkFalse()
                );
                conditions.add(h);
                z3Engine.addRule(z3Engine.implies(
                        z3Engine.and(
                                conditions.toArray(new BoolExpr[0])
                        ),
                        result
                ), null);

                break;
            case "bisz":
                h = engine.rPred(f, codeAddress);
                b = engine.rPred(f, nextCode);
                z3Engine.addRule(z3Engine.implies(h, b), null);
                // BISZ 仅有两个操作数，op2 位 EMPTY，op1为寄存器或立即数，op3为寄存器
                if (op1.getType() == OperandType.REGISTER) {
                    name1 = op1.toString();
                    hash1 = name1.hashCode();
                    v1 = var.getV(hash1);
                    l1 = var.getL(hash1);
                    conditions.add(engine.regPred(name1, null, null, null));
                } else {
                    v1 = z3Engine.mkBitVector(Long.valueOf(op1.getValue()), size);
                    l1 = z3Engine.mkFalse();
                }
                name3 = op3.toString();

                result = engine.regPred(
                        name3,
                        (BitVecExpr) z3Engine.ite(
                                z3Engine.eq(        //if
                                        v1,
                                        z3Engine.mkBitVector(0, size)
                                ),
                                z3Engine.mkBitVector(1, size), //then
                                z3Engine.mkBitVector(0, size) // else
                        ),
                        z3Engine.mkFalse(),
                        z3Engine.mkFalse()
                );
                conditions.add(h);
                z3Engine.addRule(z3Engine.implies(
                        z3Engine.and(
                                conditions.toArray(new BoolExpr[0])
                        ),
                        result
                ), null);
            case "jcc":
                Long jump = null;
                // JCC 仅有两个操作数，op2 位 EMPTY，op1为寄存器或立即数，op3为地址或立即数或寄存器，地址存储同一条原始指令内部的偏移
                // op1为非零时则跳转，否则执行下一条指令
                if (op1.getType() == OperandType.REGISTER) {
                    name1 = op1.toString();
                    hash1 = name1.hashCode();
                    v1 = var.getV(hash1);
                    l1 = var.getL(hash1);
                    conditions.add(engine.regPred(name1, null, null, null));
                } else {
                    v1 = z3Engine.mkBitVector(Long.valueOf(op1.getValue()), size);
                    l1 = z3Engine.mkFalse();
                }
                if (op3.getType() == OperandType.REGISTER) {
                    jump = null;  // 目标地址为寄存器，无法确定具体值，直接执行下一条
                } else if (op3.getType() == OperandType.INTEGER_LITERAL) {
                    simV3 = Long.valueOf(op3.getValue());
                    jump = simV3 << 8;
                } else { // 操作数类型为偏移值，此时计算指令偏移
                    // 偏移值一般以 指令地址.偏移值 的格式存储
                    String a = op3.getValue();
                    String[] parts = a.split("\\.");
                    Long a1 = Long.valueOf(parts[0]);
                    Long a2 = Long.valueOf(parts[1]);
                    jump = a1 << 8 + a2;
                }
                if (jump == null) { // 如果无法确定jump地址，则无条件执行下一条指令
                    h = engine.rPred(f, codeAddress);
                    b = engine.rPred(f, nextCode);
                    z3Engine.addRule(z3Engine.implies(h, b), null);
                    break;
                }
                // 处理为0的情况，不关心 jump 地址，直接执行下一条语句
                h = z3Engine.and(
                        engine.rPred(f, codeAddress),
                        z3Engine.eq(
                                v1,
                                z3Engine.mkBitVector(0, size)
                        )
                );
                b = engine.rPred(f, nextCode);
                z3Engine.addRule(z3Engine.implies(h, b), null);
                // 如果为普通跳转
                if (!this.instruction.getMetaData().containsKey("isCall")) {
                    // 处理非0的情况，跳转到 jump 地址（仍在函数内，不需要做寄存器值的转换）
                    h = z3Engine.and(
                            engine.rPred(f, codeAddress),
                            z3Engine.not(z3Engine.eq(
                                    v1,
                                    z3Engine.mkBitVector(0, size)
                            ))
                    );
                    b = engine.rPred(f, jump);
                    z3Engine.addRule(z3Engine.implies(h, b), null);
                } else {  // 如果为函数跳转
                    String funName = addr2fun.get(jump);
                    if (funName == null) { // 无法确定目标函数，无条件执行下一条指令
                        h = engine.rPred(f, codeAddress);
                        b = engine.rPred(f, nextCode);
                        z3Engine.addRule(z3Engine.implies(h, b), null);
                        break;
                    }
                    // 处理非0的情况，跳转到 jump 地址（如果为sink函数，则直接处理并执行下一条指令，不做跳转处理）
                    RFunction funTo = name2fun.get(funName);

                    if (isSink(funTo)) {
                        // TODO 处理 sink 函数
                        addQuery(z3Engine, engine.rPred(f, codeAddress), "native-code", f, String.valueOf(codeAddress), funTo.getFunName(),
                                true, funTo.getParamNum());
                    } else {
                        h = z3Engine.and(
                                engine.rPred(f, codeAddress),
                                z3Engine.not(z3Engine.eq(
                                        v1,
                                        z3Engine.mkBitVector(0, size)
                                ))
                        );
                        b = engine.rPred(funTo.getFunName(), jump);
                        z3Engine.addRule(z3Engine.implies(h, b), null);
                        BoolExpr subh = engine.rPred(f, codeAddress);
                        h = z3Engine.and(
                                subh,
                                engine.resPred(funName, null, null, null)  // 返回谓词
                        );
                        b = engine.rPred(f, nextCode);
                        z3Engine.addRule(z3Engine.implies(h, b), null);
                    }
                    break;
                }
                break;
            case "str":
                h = engine.rPred(f, codeAddress);
                b = engine.rPred(f, nextCode);
                z3Engine.addRule(z3Engine.implies(h, b), null);
                // str 仅有两个操作数，op2 位 EMPTY，op1为寄存器或立即数，op3为寄存器
                if (op1.getType() == OperandType.REGISTER) {
                    name1 = op1.toString();
                    hash1 = name1.hashCode();
                    v1 = var.getV(hash1);
                    l1 = var.getL(hash1);

                    conditions.add(engine.regPred(name1, null, null, null));
                } else {
                    v1 = z3Engine.mkBitVector(Long.valueOf(op1.getValue()), size);
                    l1 = z3Engine.mkFalse();
                }
                name3 = op3.toString();

                result = engine.regPred(
                        name3,
                        v1,
                        l1,
                        z3Engine.mkFalse()
                );
                conditions.add(h);
                z3Engine.addRule(z3Engine.implies(
                        z3Engine.and(
                                conditions.toArray(new BoolExpr[0])
                        ),
                        result
                ), null);
                break;
            case "ldm":
                h = engine.rPred(f, codeAddress);
                b = engine.rPred(f, nextCode);
                z3Engine.addRule(z3Engine.implies(h, b), null);
                // ldm 仅有两个操作数，op2 位 EMPTY，op1为寄存器或立即数，op3为寄存器
                if (op1.getType() == OperandType.REGISTER) {
                    name1 = op1.toString();
                    hash1 = name1.hashCode();
                    v1 = var.getV(hash1);
                    l1 = var.getL(hash1);
                    b1 = var.getB(hash1);
                    conditions.add(engine.sPred(v1, var.getSV(), var.getSL(), var.getSB()));
                    conditions.add(engine.regPred(name1, v1, l1, b1));
                } else {
                    v1 = z3Engine.mkBitVector(Long.valueOf(op1.getValue()), size);
                    conditions.add(engine.sPred(v1, var.getSV(), var.getSL(), var.getSB()));
                }
                name3 = op3.toString();
                result = engine.regPred(
                        name3,
                        var.getSV(),
                        var.getSL(),
                        var.getSB()
                );
                conditions.add(h);
                z3Engine.addRule(z3Engine.implies(
                        z3Engine.and(
                                conditions.toArray(new BoolExpr[0])
                        ),
                        result
                ), null);
                break;

            case "stm":
                h = engine.rPred(f, codeAddress);
                b = engine.rPred(f, nextCode);
                z3Engine.addRule(z3Engine.implies(h, b), null);
                // stm 仅有两个操作数，op2 位 EMPTY，op1为寄存器或立即数，表示要存储的值，op3为寄存器或寄存器，存储地址
                if (op1.getType() == OperandType.REGISTER) {
                    name1 = op1.toString();
                    hash1 = name1.hashCode();
                    v1 = var.getV(hash1);
                    l1 = var.getL(hash1);
                    b1 = var.getB(hash1);
                    conditions.add(engine.regPred(name1, v1, l1, b1));
                } else {
                    v1 = z3Engine.mkBitVector(Long.valueOf(op1.getValue()), size);
                    l1 = z3Engine.mkFalse();
                    b1 = z3Engine.mkFalse();
                }

                if (op3.getType() == OperandType.REGISTER) {
                    name3 = op3.toString();
                    hash3 = name3.hashCode();
                    v3 = var.getV(hash3);
                    l3 = var.getL(hash3);
                    b3 = var.getB(hash3);
                    conditions.add(engine.regPred(name3, v3, l3, b3));
                } else {
                    v3 = z3Engine.mkBitVector(Long.valueOf(op1.getValue()), size);
                }
                name3 = op3.toString();
                result = engine.sPred(
                        v3,
                        v1,
                        l1,
                        b1
                );
                conditions.add(h);
                z3Engine.addRule(z3Engine.implies(
                        z3Engine.and(
                                conditions.toArray(new BoolExpr[0])
                        ),
                        result
                ), null);
                break;
            // TODO 返回语句、更完善的内存模型、从 Java 调用、返回JAVA代码

        }

    }

    public boolean isSink(RFunction function) {
        return false;
    }

    private void addQuery(final Z3Engine z3, BoolExpr p, String className, String methodName, String pc, String sinkName, final boolean verboseResults, int paramNum){

        switch (paramNum) {
            case 3:
                BoolExpr q3 = z3.and(
                        p, engine.regPred("R3", null, null, null),
                        z3.eq(var.getL("R3".hashCode()), z3.mkTrue())
                );
                String d3 = "Test if register " + "R3" +  " leaks @line " + pc + " in method " +  methodName + " of the class " + className + " ---> sink " + sinkName;
                z3.addQuery(new Z3Query(q3, d3, verboseResults, className, methodName, pc, sinkName));
            case 2:
                BoolExpr q2 = z3.and(
                        p,engine.regPred("R2", null, null, null),
                        z3.eq(var.getL("R2".hashCode()), z3.mkTrue())
                );
                String d2 = "Test if register " + "R2" +  " leaks @line " + pc + " in method " +  methodName + " of the class " + className + " ---> sink " + sinkName;
                z3.addQuery(new Z3Query(q2, d2, verboseResults, className, methodName, pc, sinkName));
            case 1:
                BoolExpr q1 = z3.and(
                        p, engine.regPred("R1", null, null, null),
                        z3.eq(var.getL("R1".hashCode()), z3.mkTrue())
                );
                String d1 = "Test if register " + "R1" +  " leaks @line " + pc + " in method " +  methodName + " of the class " + className + " ---> sink " + sinkName;
                z3.addQuery(new Z3Query(q1, d1, verboseResults, className, methodName, pc, sinkName));
        }
    }
}
