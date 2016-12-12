package com.shellming.z3;

import com.microsoft.z3.*;
import z3.Z3Engine;

import java.util.Arrays;
import java.util.Map;

/**
 * Created by ruluo1992 on 12/11/2016.
 */
public class ReilEngine {
    private Context mContext;
    private int bvSize;
    private Z3Engine z3Engine;
    private ReilVariable var;
    private Map<String, Long> regVal;
    private Map<Long, Long> stackVal;

    public BoolExpr rPred(String f, Long pc, final Map<Integer, BitVecExpr> rUp, final Map<Integer, BoolExpr> rUpL, final Map<Integer, BoolExpr> rUpB, final int size) {
        try {
            FuncDecl r = this.rPredDef(f, pc, size);

            Expr[] e = new Expr[3 * size];
            for(int i = 0, j = size, k = 2*size; i < size; i++, j++, k++){
                e[i] = rUp.get(i); if (e[i] == null) e[i] = var.getV(i);
                e[j] = rUpL.get(i); if (e[j] == null) e[j] = var.getL(i);
                e[k] = rUpB.get(i); if (e[k] == null) e[k] = var.getB(i);
            }

            return (BoolExpr) r.apply(e);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Engine Failed: rPred");
        }
    }

    private FuncDecl rPredDef(String f, long pc, int size) {
        try {
            BitVecSort bv64 = mContext.mkBitVecSort(bvSize);
            BoolSort bool = mContext.mkBoolSort();

            String funcName = "R_" + f + '_' + pc;
            Sort[] domains = new Sort[3 * size];
            Arrays.fill(domains, 0, size, bv64);
            Arrays.fill(domains, size, 3 * size, bool);
            FuncDecl fun = mContext.mkFuncDecl(funcName, domains, mContext.mkBoolSort());
            z3Engine.declareRel(fun);
            return fun;
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Engine Failed: rPredDef");
        }
    }

    public Long getRegSimVal(String reg) {
        return regVal.get(reg);
    }

    public void setRegSimVal(String reg, Long val) {
        regVal.put(reg, val);
    }

    public Context getmContext() {
        return mContext;
    }

    public BitVecExpr bvsmod(BitVecExpr bv1, BitVecExpr bv2) {
        return mContext.mkBVSMod(bv1, bv2);
    }

    public void setmContext(Context mContext) {
        this.mContext = mContext;
    }

    public int getBvSize() {
        return bvSize;
    }

    public void setBvSize(int bvSize) {
        this.bvSize = bvSize;
    }

    public Z3Engine getZ3Engine() {
        return z3Engine;
    }

    public void setZ3Engine(Z3Engine z3Engine) {
        this.z3Engine = z3Engine;
    }

    public ReilVariable getVar() {
        return var;
    }

    public void setVar(ReilVariable var) {
        this.var = var;
    }

    public Map<String, Long> getRegVal() {
        return regVal;
    }

    public void setRegVal(Map<String, Long> regVal) {
        this.regVal = regVal;
    }

    public Map<Long, Long> getStackVal() {
        return stackVal;
    }

    public void setStackVal(Map<Long, Long> stackVal) {
        this.stackVal = stackVal;
    }
}
