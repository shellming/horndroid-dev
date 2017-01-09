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

    public BoolExpr sPred(BitVecExpr addr, BitVecExpr v3, BoolExpr v4, BoolExpr v5) {
        try {
            BitVecSort bv = mContext.mkBitVecSort(bvSize);
            BoolSort bool = mContext.getBoolSort();
            FuncDecl s = mContext.mkFuncDecl("S", new Sort[]{bv, bv, bool, bool}, bool);
            z3Engine.declareRel(s);
            return (BoolExpr) s.apply(addr, v3, v4, v5);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Engine Failed: sPred");
        }
    }

    public BoolExpr resPred(String f, BitVecExpr v, BoolExpr l, BoolExpr b) {
        try {
            FuncDecl res = this.resPredDef(f);
            Expr[] e = new Expr[]{v, l, b};
            return (BoolExpr) res.apply(e);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Engine Failed: resPred");
        }
    }

    private FuncDecl resPredDef(String fun) {
        try {
            BoolSort bool = mContext.mkBoolSort();
            BitVecSort bitVecSort = mContext.mkBitVecSort(bvSize);
            String funcName = "RES_" + fun;
            FuncDecl f = mContext.mkFuncDecl(funcName, new Sort[]{bitVecSort, bool, bool}, bool);

            z3Engine.declareRel(f);
//            Symbol[] symbols = new Symbol[]{mContext.mkSymbol("interval_relation"),
//                                            mContext.mkSymbol("bound_relation")};
//            mFixedPoint.setPredicateRepresentation(f, symbols);
            return f;
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Engine Failed: resPredDef");
        }
    }

    public BoolExpr regPred(String regName, BitVecExpr v, BoolExpr b, BoolExpr l) {
        FuncDecl funcDecl = regPreDef(regName);
        int hash = regName.hashCode();
        BitVecExpr rv = v == null ? var.getV(hash) : v;
        BoolExpr rb = b == null ? var.getL(hash) : b;
        BoolExpr rl = l == null ? var.getB(hash) : l;
        return (BoolExpr) funcDecl.apply(rv, rb, rl);
    }

    public FuncDecl regPreDef(String name) {
        try {
            String funcName = "REG_" + name;
            Sort[] sorts = new Sort[3];
            sorts[0] = mContext.mkBitVecSort(bvSize);
            sorts[1] = mContext.mkBoolSort();
            sorts[2] = mContext.mkBoolSort();
            FuncDecl fun = mContext.mkFuncDecl(funcName, sorts, mContext.mkBoolSort());
            z3Engine.declareRel(fun);
            return fun;
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Engine Failed: rPredDef");
        }
    }

    public BoolExpr rPred(String f, Long pc) {
        try {
            FuncDecl r = this.rPredDef(f, pc);
            Expr[] e = new Expr[0];
            return (BoolExpr) r.apply(e);
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Engine Failed: rPred");
        }
    }

    private FuncDecl rPredDef(String f, long pc) {
        try {
            String funcName = "R_" + f + '_' + pc;
            FuncDecl fun = mContext.mkFuncDecl(funcName, new Sort[0], mContext.mkBoolSort());
            z3Engine.declareRel(fun);
            return fun;
        } catch (Z3Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Z3Engine Failed: rPredDef");
        }
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
}
