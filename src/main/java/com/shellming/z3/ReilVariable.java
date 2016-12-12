package com.shellming.z3;

import com.google.security.zynamics.binnavi.API.reil.OperandSize;
import com.microsoft.z3.*;
import z3.VariableInject;

/**
 * Created by ruluo1992 on 12/11/2016.
 */
public class ReilVariable {
    private final int GUARD = 1000;

    private final Context ctx;
    private final BoolSort bool;

    private final BitVecSort bv64;
    private final BitVecSort bv32;
    private final BitVecSort bv16;
    private final BitVecSort bv8;

    private final BitVecExpr rez, rezp, buf, bufp, f, fpp, vfp, cn, val;
    private final BoolExpr lrez, brez, lrezp, lbuf, lbufp, lfp, bfp, lf, bf, lval, bval;
    private final IntExpr fnum, cnum;

    public ReilVariable(Context ctx, int bvSize) throws Z3Exception {
        this.ctx = ctx;

        this.bool = ctx.mkBoolSort();
        this.bv64 = ctx.mkBitVecSort(64);
        this.bv32 = ctx.mkBitVecSort(32);
        this.bv16 = ctx.mkBitVecSort(16);
        this.bv8 = ctx.mkBitVecSort(8);
        IntSort integer = ctx.mkIntSort();

        this.rez = (BitVecExpr) ctx.mkBound(0, bv64);
        this.rezp = (BitVecExpr) ctx.mkBound(1, bv64);
        this.buf = (BitVecExpr) ctx.mkBound(2, bv64);
        this.bufp = (BitVecExpr) ctx.mkBound(3, bv64);
        this.lrez = (BoolExpr) ctx.mkBound(4, bool);
        this.brez = (BoolExpr) ctx.mkBound(5, bool);
        this.lrezp = (BoolExpr) ctx.mkBound(6, bool);
        this.lbuf = (BoolExpr) ctx.mkBound(7, bool);
        this.lbufp = (BoolExpr) ctx.mkBound(8, bool);
        this.fnum = (IntExpr) ctx.mkBound(9, integer);
        this.f = (BitVecExpr) ctx.mkBound(10, bv64);
        this.fpp = (BitVecExpr) ctx.mkBound(11, bv64);
        this.vfp = (BitVecExpr) ctx.mkBound(12, bv64);
        this.lfp = (BoolExpr) ctx.mkBound(13, bool);
        this.bfp = (BoolExpr) ctx.mkBound(14, bool);
        this.cn = (BitVecExpr) ctx.mkBound(15, bv64);
        this.lf = (BoolExpr) ctx.mkBound(16, bool);
        this.bf = (BoolExpr) ctx.mkBound(17, bool);
        this.val = (BitVecExpr) ctx.mkBound(18, bv64);
        this.lval = (BoolExpr) ctx.mkBound(19, bool);
        this.bval = (BoolExpr) ctx.mkBound(20, bool);
        this.cnum = (IntExpr) ctx.mkBound(21, integer);

    }

    public BitVecExpr getRez() {
        return rez;
    }

    public BitVecExpr getRezp() {
        return rezp;
    }

    public BitVecExpr getBuf() {
        return buf;
    }

    public BitVecExpr getBufp() {
        return bufp;
    }

    public BitVecExpr getF() {
        return f;
    }

    public BitVecExpr getFpp() {
        return fpp;
    }

    public BitVecExpr getVfp() {
        return vfp;
    }

    public BitVecExpr getCn() {
        return cn;
    }

    public BitVecExpr getVal() {
        return val;
    }

    public BoolExpr getLrez() {
        return lrez;
    }

    public BoolExpr getBrez() {
        return brez;
    }

    public BoolExpr getLrezp() {
        return lrezp;
    }

    public BoolExpr getLbuf() {
        return lbuf;
    }

    public BoolExpr getLbufp() {
        return lbufp;
    }

    public BoolExpr getLfp() {
        return lfp;
    }

    public BoolExpr getBfp() {
        return bfp;
    }

    public BoolExpr getLf() {
        return lf;
    }

    public BoolExpr getBf() {
        return bf;
    }

    public BoolExpr getLval() {
        return lval;
    }

    public BoolExpr getBval() {
        return bval;
    }

    public IntExpr getFnum() {
        return fnum;
    }

    public IntExpr getCnum() {
        return cnum;
    }

    public int getOperandSize(OperandSize size) {
        switch (size) {
            case OPERAND_SIZE_BYTE:
                return 8;
            case OPERAND_SIZE_WORD:
                return 16;
            case OPERAND_SIZE_DWORD:
                return 32;
            case OPERAND_SIZE_QWORD:
            case OPERAND_SIZE_OWORD:
                return 64;
            default:
                return 64;
        }
    }

    public BitVecExpr getV(int i){
        BitVecSort bv = null;
        try {
//            if (i < 0) return ctx.mkBV(-1*i, bv64);
            return (BitVecExpr) ctx.mkBound(GUARD + 3*i + 0, bv64);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("getV");
        }
    }

    public BoolExpr getL(int i){
        try {
            return (BoolExpr) ctx.mkBound(GUARD + 3*i + 1, bool);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("getL");
        }
    }

    public BoolExpr getB(int i){
        try {
            return (BoolExpr) ctx.mkBound(GUARD + 3*i + 2, bool);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("getB");
        }
    }
}
