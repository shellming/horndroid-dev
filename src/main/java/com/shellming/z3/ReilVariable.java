package com.shellming.z3;

import com.google.security.zynamics.binnavi.API.reil.OperandSize;
import com.microsoft.z3.*;
import z3.VariableInject;

/**
 * Created by ruluo1992 on 12/11/2016.
 */
public class ReilVariable {
    private final int GUARD = 100;

    private final Context ctx;
    private final BoolSort bool;

    private final BitVecSort bvSize;

    public ReilVariable(Context ctx, int bvSize) throws Z3Exception {
        this.ctx = ctx;

        this.bool = ctx.mkBoolSort();
        IntSort integer = ctx.mkIntSort();
        this.bvSize = ctx.mkBitVecSort(bvSize);
    }

    public BitVecExpr getV(int i){
        BitVecSort bv = null;
        try {
//            if (i < 0) return ctx.mkBV(-1*i, bv64);
            return (BitVecExpr) ctx.mkBound(GUARD + 3*i + 0, bvSize);
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

    public BitVecExpr getSV(){
        BitVecSort bv = null;
        try {
//            if (i < 0) return ctx.mkBV(-1*i, bv64);
            return (BitVecExpr) ctx.mkBound(GUARD + 0, bvSize);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("getV");
        }
    }

    public BoolExpr getSL(){
        try {
            return (BoolExpr) ctx.mkBound(GUARD + 1, bool);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("getL");
        }
    }

    public BoolExpr getSB(){
        try {
            return (BoolExpr) ctx.mkBound(GUARD + 2, bool);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("getB");
        }
    }
}
