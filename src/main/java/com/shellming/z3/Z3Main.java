package com.shellming.z3;

import com.microsoft.z3.*;
import com.sun.org.apache.xpath.internal.operations.Bool;
import z3.Z3Query;

import java.util.HashMap;

/**
 * Created by ruluo1992 on 10/30/2016.
 */
public class Z3Main {
    private static Context ctx;
    private static Solver solver;

    static {
        ctx = new Context(new HashMap<String, String>());
        solver = ctx.mkSolver();
    }

    public static void main(String[] args) throws Examples.TestFailedException {
//        quantifierExample2(ctx);
//        test7();
//        Examples examples = new Examples();
//        examples.quantifierExample3(ctx);
//            test12();
        Long a = 8L;
        System.out.println(a << -4);
        System.out.println(a >> 2);
    }

    static void test12() {
        BitVecSort bv32 = ctx.mkBitVecSort(32);
        BitVecSort bv64 = ctx.mkBitVecSort(64);
        BoolSort boolSort = ctx.mkBoolSort();
        FuncDecl funcDecl = ctx.mkFuncDecl("test", bv64, boolSort);

        BitVecExpr vecExpr = (BitVecExpr) ctx.mkBound(0, bv32);
        BoolExpr boolExpr = (BoolExpr) funcDecl.apply(vecExpr);
        System.out.println(boolExpr);
    }

    static void test10() {
        BoolSort boolSort = ctx.getBoolSort();
        Sort[] domain = new Sort[0];
        FuncDecl fd0 = ctx.mkFuncDecl("f0", domain, boolSort);
        FuncDecl fd1 = ctx.mkFuncDecl("f1", domain, boolSort);
        FuncDecl fd2 = ctx.mkFuncDecl("f2", domain, boolSort);

        Expr[] e = new Expr[0];

        BoolExpr r0 = (BoolExpr) fd0.apply(e);
        BoolExpr r1 = (BoolExpr) fd1.apply(e);
        BoolExpr r2 = (BoolExpr) fd2.apply(e);

        Fixedpoint fixedpoint = ctx.mkFixedpoint();
        fixedpoint.addRule(ctx.mkImplies(r0, r1), null);
        fixedpoint.addRule(ctx.mkImplies(r1, r2), null);
        fixedpoint.addRule(r0, null);

        fixedpoint.registerRelation(fd0);
        fixedpoint.registerRelation(fd1);
        fixedpoint.registerRelation(fd2);

        System.out.println(fixedpoint.query(r0));
    }

    static void test11() {
        BoolSort boolSort = ctx.getBoolSort();
        Sort[] domain = new Sort[3];
        domain[0] = boolSort;
        domain[1] = boolSort;
        domain[2] = boolSort;

        FuncDecl fd0 = ctx.mkFuncDecl("f0", domain, boolSort);
        FuncDecl fd1 = ctx.mkFuncDecl("f1", domain, boolSort);
        FuncDecl fd2 = ctx.mkFuncDecl("f2", domain, boolSort);
        FuncDecl fd3 = ctx.mkFuncDecl("f3", domain, boolSort);

        Expr[] e0 = new Expr[3];
        e0[0] = ctx.mkFalse();
        e0[1] = ctx.mkFalse();
        e0[2] = ctx.mkFalse();

        Expr[] e1 = new Expr[3];
        e1[0] = ctx.mkConst("a", boolSort);
        e1[1] = ctx.mkConst("b", boolSort);
        e1[2] = ctx.mkConst("c", boolSort);


        Expr[] e2 = new Expr[3];
        e2[0] = ctx.mkTrue();
        e2[1] = ctx.mkConst("b", boolSort);
        e2[2] = ctx.mkConst("c", boolSort);

        Expr[] e3 = new Expr[3];
        e3[0] = ctx.mkConst("a", boolSort);
        e3[1] = ctx.mkConst("a", boolSort);
        e3[2] = ctx.mkConst("c", boolSort);
//        e3[0] = ctx.mkBound(0, boolSort);
//        e3[1] = ctx.mkBound(0, boolSort);
//        e3[2] = ctx.mkBound(2, boolSort);

        BoolExpr r1 = (BoolExpr) fd0.apply(e0);

        BoolExpr r2 = (BoolExpr) fd0.apply(e1);
        BoolExpr r3 = (BoolExpr) fd1.apply(e2);

        BoolExpr r4 = (BoolExpr) fd1.apply(e1);
        BoolExpr r5 = (BoolExpr) fd2.apply(e3);

        BoolExpr r6 = (BoolExpr) fd2.apply(e1);
        BoolExpr r7 = (BoolExpr) fd3.apply(e1);


        Fixedpoint fixedpoint = ctx.mkFixedpoint();
        fixedpoint.addRule(r1, null);
        fixedpoint.addRule(ctx.mkImplies(r2, r3), null);
        fixedpoint.addRule(ctx.mkImplies(r4, r5), null);
        fixedpoint.addRule(ctx.mkImplies(r6, r7), null);

        BoolExpr query = ctx.mkAnd(
                (BoolExpr) fd3.apply(e1),
                ctx.mkEq(
                        ctx.mkBound(2, boolSort),
                        ctx.mkTrue()
                )
        );
        fixedpoint.registerRelation(fd0);
        fixedpoint.registerRelation(fd1);
        fixedpoint.registerRelation(fd2);
        fixedpoint.registerRelation(fd3);

        System.out.println(fixedpoint.query(query));
    }

    static void test9() {
        BoolSort boolSort = ctx.getBoolSort();
        Sort[] domain = new Sort[3];
        domain[0] = boolSort;
        domain[1] = boolSort;
        domain[2] = boolSort;

        FuncDecl fd0 = ctx.mkFuncDecl("f0", domain, boolSort);
        FuncDecl fd1 = ctx.mkFuncDecl("f1", domain, boolSort);
        FuncDecl fd2 = ctx.mkFuncDecl("f2", domain, boolSort);
        FuncDecl fd3 = ctx.mkFuncDecl("f3", domain, boolSort);

        Expr[] e0 = new Expr[3];
        e0[0] = ctx.mkFalse();
        e0[1] = ctx.mkFalse();
        e0[2] = ctx.mkFalse();

        Expr[] e1 = new Expr[3];
        e1[0] = ctx.mkBound(0, boolSort);
        e1[1] = ctx.mkBound(1, boolSort);
        e1[2] = ctx.mkBound(2, boolSort);


        Expr[] e2 = new Expr[3];
        e2[0] = ctx.mkTrue();
        e2[1] = ctx.mkBound(1, boolSort);
        e2[2] = ctx.mkBound(2, boolSort);

        Expr[] e3 = new Expr[3];
        e3[0] = ctx.mkBound(0, boolSort);
        e3[1] = ctx.mkBound(0, boolSort);
        e3[2] = ctx.mkBound(2, boolSort);

        BoolExpr r1 = (BoolExpr) fd0.apply(e0);

        BoolExpr r2 = (BoolExpr) fd0.apply(e1);
        BoolExpr r3 = (BoolExpr) fd1.apply(e2);

        BoolExpr r4 = (BoolExpr) fd1.apply(e1);
        BoolExpr r5 = (BoolExpr) fd2.apply(e3);

        BoolExpr r6 = (BoolExpr) fd2.apply(e1);
        BoolExpr r7 = (BoolExpr) fd3.apply(e1);


        Fixedpoint fixedpoint = ctx.mkFixedpoint();
        fixedpoint.addRule(r1, null);
        fixedpoint.addRule(ctx.mkImplies(r2, r3), null);
        fixedpoint.addRule(ctx.mkImplies(r4, r5), null);
        fixedpoint.addRule(ctx.mkImplies(r6, r7), null);

        BoolExpr query = ctx.mkAnd(
                (BoolExpr) fd3.apply(e1),
                ctx.mkEq(
                        ctx.mkBound(2, boolSort),
                        ctx.mkTrue()
                )
        );
        fixedpoint.registerRelation(fd0);
        fixedpoint.registerRelation(fd1);
        fixedpoint.registerRelation(fd2);
        fixedpoint.registerRelation(fd3);

        System.out.println(fixedpoint.query(query));
    }

    static void test8() {
        BoolSort boolSort = ctx.getBoolSort();
        BitVecSort bitVecSort = ctx.mkBitVecSort(64);
         ctx.mkBound(0, boolSort);
        Sort[] domain = new Sort[3];
        domain[0] = boolSort;
        domain[1] = boolSort;
        domain[2] = boolSort;

        FuncDecl fd0 = ctx.mkFuncDecl("f0", domain, boolSort);
        Expr[] e0 = new Expr[3];
        e0[0] = ctx.mkFalse();
        e0[1] = ctx.mkFalse();
        e0[2] = ctx.mkFalse();

        FuncDecl fd1 = ctx.mkFuncDecl("f1", domain, boolSort);
        Expr[] e1 = new Expr[3];
        e1[0] = ctx.mkBound(0, boolSort);
        e1[1] = ctx.mkBound(1, boolSort);
        e1[2] = ctx.mkBound(2, boolSort);

        BoolExpr r01 = (BoolExpr) fd0.apply(e1);
        BoolExpr r02 = (BoolExpr) fd1.apply(e0);

        BoolExpr r11 = (BoolExpr) fd1.apply(e1);

        FuncDecl fd2 = ctx.mkFuncDecl("f2", domain, boolSort);
        Expr[] e2 = new Expr[3];
        e2[0] = ctx.mkBound(0, boolSort);
        e2[1] = ctx.mkFalse();
        e2[2] = ctx.mkBound(2, boolSort);
        BoolExpr r12 = (BoolExpr) fd2.apply(e2);

        FuncDecl fd3 = ctx.mkFuncDecl("f3", domain, boolSort);
        Expr[] e3 = new Expr[3];
        e3[0] = ctx.mkBound(0, boolSort);
        e3[1] = ctx.mkBound(1, boolSort);
        e3[2] = ctx.mkBound(2, boolSort);

        BoolExpr r21 = (BoolExpr) fd2.apply(e1);
        BoolExpr r22 = (BoolExpr) fd3.apply(e3);

        Fixedpoint fixedpoint = ctx.mkFixedpoint();
        fixedpoint.add((BoolExpr)fd1.apply(e0));
//        fixedpoint.add(ctx.mkImplies(r01, r02));
        fixedpoint.add(ctx.mkImplies(r11, r12));
        fixedpoint.add(ctx.mkImplies(r21, r22));

        fixedpoint.registerRelation(fd1);
        fixedpoint.registerRelation(fd2);
        fixedpoint.registerRelation(fd3);
        fixedpoint.registerRelation(fd0);

        BoolExpr query = ctx.mkAnd(
                (BoolExpr) fd2.apply(e1),
                ctx.mkEq(
                        ctx.mkBound(1, boolSort),
                        ctx.mkTrue()
                )
        );

        BoolExpr query2 = ctx.mkEq(ctx.mkBound(1, boolSort), ctx.mkTrue());

        System.out.println(fixedpoint.query(query));
        Status status = fixedpoint.query(query2);
        Params params = ctx.mkParams();
        params.add("print-answer", true);
        fixedpoint.setParameters(params);
        System.out.println(fixedpoint.query(query2));


    }

    static void test7() {
        // 对任意的x，x > 5
        // 对任意的y, y > 3
        // x + y = 5
//        IntExpr x = (IntExpr) ctx.mkConst(0, ctx.getIntSort());
//        IntExpr y = (IntExpr) ctx.mkBound(1, ctx.getIntSort());
        IntExpr x = ctx.mkIntConst("x");
        IntExpr xx = (IntExpr) ctx.mkBound(0, ctx.getIntSort());
        IntExpr y = ctx.mkIntConst("y");

        Quantifier q1 = ctx.mkForall(new Sort[]{ctx.getIntSort(), ctx.getIntSort()},
                new Symbol[]{ctx.mkSymbol("x"), ctx.mkSymbol("y")},
                ctx.mkAnd(
                        ctx.mkGt(x, ctx.mkInt(5)),
                        ctx.mkGt(y, ctx.mkInt(3))
                ),
                1, null, null, null, null
        );
        solver.add(q1);
        solver.add(ctx.mkEq(
                ctx.mkAdd(x, y),
                ctx.mkInt(10)
        ));
        System.out.println(solver);
        System.out.println(solver.check());
        System.out.println(solver.getModel());
    }

    static void quantifierExample2(Context ctx)
    {

        System.out.println("QuantifierExample2");
//        Log.append("QuantifierExample2");

        Expr q1, q2;
        FuncDecl f = ctx.mkFuncDecl("f", ctx.getIntSort(), ctx.getIntSort());
        FuncDecl g = ctx.mkFuncDecl("g", ctx.getIntSort(), ctx.getIntSort());

        // Quantifier with Exprs as the bound variables.
        {
            Expr x = ctx.mkConst("x", ctx.getIntSort());
            Expr y = ctx.mkConst("y", ctx.getIntSort());
            Expr f_x = ctx.mkApp(f, x);
            Expr f_y = ctx.mkApp(f, y);
            Expr g_y = ctx.mkApp(g, y);
            @SuppressWarnings("unused")
            Pattern[] pats = new Pattern[] { ctx.mkPattern(f_x, g_y) };
            Expr[] no_pats = new Expr[] { f_y };
            Expr[] bound = new Expr[] { x, y };
            Expr body = ctx.mkAnd(ctx.mkEq(f_x, f_y), ctx.mkEq(f_y, g_y));

            q1 = ctx.mkForall(bound, body, 1, null, no_pats, ctx.mkSymbol("q"),
                    ctx.mkSymbol("sk"));

            System.out.println(q1);
        }

        // Quantifier with de-Brujin indices.
        {
            Expr x = ctx.mkBound(1, ctx.getIntSort());
            Expr y = ctx.mkBound(0, ctx.getIntSort());
            Expr f_x = ctx.mkApp(f, x);
            Expr f_y = ctx.mkApp(f, y);
            Expr g_y = ctx.mkApp(g, y);
            @SuppressWarnings("unused")
            Pattern[] pats = new Pattern[] { ctx.mkPattern(f_x, g_y) };
            Expr[] no_pats = new Expr[] { f_y };
            Symbol[] names = new Symbol[] { ctx.mkSymbol("x"),
                    ctx.mkSymbol("y") };
            Sort[] sorts = new Sort[] { ctx.getIntSort(), ctx.getIntSort() };
            Expr body = ctx.mkAnd(ctx.mkEq(f_x, f_y), ctx.mkEq(f_y, g_y));

            q2 = ctx.mkForall(sorts, names, body, 1, null, // pats,
                    no_pats, ctx.mkSymbol("q"), ctx.mkSymbol("sk"));
            System.out.println(q2);
        }

        System.out.println(q1.equals(q2));
    }

    static void quantifierExample1(Context ctx)
    {
        System.out.println("QuantifierExample");
//        Log.append("QuantifierExample");

        Sort[] types = new Sort[3];
        IntExpr[] xs = new IntExpr[3];
        Symbol[] names = new Symbol[3];
        IntExpr[] vars = new IntExpr[3];

        for (int j = 0; j < 3; j++)
        {
            types[j] = ctx.getIntSort();
            names[j] = ctx.mkSymbol("x_" + Integer.toString(j));
            xs[j] = (IntExpr) ctx.mkConst(names[j], types[j]);
            vars[j] = (IntExpr) ctx.mkBound(2 - j, types[j]); // <-- vars
            // reversed!
        }

        Expr body_vars = ctx.mkAnd(
                ctx.mkEq(ctx.mkAdd(vars[0], ctx.mkInt(1)), ctx.mkInt(2)),
                ctx.mkEq(ctx.mkAdd(vars[1], ctx.mkInt(2)),
                        ctx.mkAdd(vars[2], ctx.mkInt(3))));

        Expr body_const = ctx.mkAnd(
                ctx.mkEq(ctx.mkAdd(xs[0], ctx.mkInt(1)), ctx.mkInt(2)),
                ctx.mkEq(ctx.mkAdd(xs[1], ctx.mkInt(2)),
                        ctx.mkAdd(xs[2], ctx.mkInt(3))));

        Expr x = ctx.mkForall(types, names, body_vars, 1, null, null,
                ctx.mkSymbol("Q1"), ctx.mkSymbol("skid1"));
        System.out.println("Quantifier X: " + x.toString());

        Expr y = ctx.mkForall(xs, body_const, 1, null, null,
                ctx.mkSymbol("Q2"), ctx.mkSymbol("skid2"));
        solver.add((Quantifier)y);
        System.out.println(solver.check());
        System.out.println("Quantifier Y: " + y.toString());
    }

    public static void test6() {
        BoolExpr a = ctx.mkBoolConst("a");
        BoolExpr b = ctx.mkBoolConst("b");
        BoolExpr c = ctx.mkBoolConst("c");
        BoolExpr a2b = ctx.mkImplies(a, b);

        Expr eee = ctx.mkBound(10, ctx.getBoolSort());

        solver.add();
    }

    public static void test5() {
        Context ctx = new Context(new HashMap<String, String>());
        Solver solver = ctx.mkSolver();
        IntExpr dog = ctx.mkIntConst("dog");
        IntExpr cat = ctx.mkIntConst("cat");
        IntExpr mouse = ctx.mkIntConst("mouse");
        solver.add(ctx.mkGe(dog, ctx.mkInt(1)));
        solver.add(ctx.mkGe(cat, ctx.mkInt(1)));
        solver.add(ctx.mkGe(mouse, ctx.mkInt(1)));
        solver.add(
                ctx.mkEq(
                        ctx.mkAdd(dog, cat, mouse),
                        ctx.mkInt(100)
                )
        );
        solver.add(ctx.mkEq(
                ctx.mkAdd(
                        ctx.mkMul(dog, ctx.mkInt(1500)),
                        ctx.mkMul(cat, ctx.mkInt(100)),
                        ctx.mkMul(mouse, ctx.mkInt(25))
                ),
                ctx.mkInt(10000)
        ));
        System.out.println(solver.check());
        System.out.println(solver.getModel());


//        ctx.mkConstructor("Pair", "mk-pair", )
//        ctx.mkDatatypeSort("Pair",);
    }

    // Arrays
    public static void test4() {
        Context ctx = new Context(new HashMap<String, String>());
        Solver solver = ctx.mkSolver();
        IntExpr a = ctx.mkIntConst("a");
        IntExpr b = ctx.mkIntConst("b");
        ArrayExpr a1 = ctx.mkArrayConst("a1", ctx.getIntSort(), ctx.getIntSort());
        BoolExpr b1 = ctx.mkEq(ctx.mkSelect(a1, a), a);
        BoolExpr b2 = ctx.mkEq(ctx.mkSelect(a1, b), a);
        solver.add(b1, b2);
        System.out.println(solver.check());
        System.out.println(solver.getModel());

    }

    public static void test3() {
        Context ctx = new Context(new HashMap<String, String>());
        Solver solver = ctx.mkSolver();
        IntExpr a = ctx.mkIntConst("a");
        IntExpr b = ctx.mkIntConst("b");
        ArithExpr add = ctx.mkAdd(a, b);
        System.out.println(add.getClass());
        RealExpr realAdd = ctx.mkInt2Real((IntExpr) add);
        ArithExpr mul = ctx.mkMul(realAdd, ctx.mkReal("0.5"));

        solver.add(ctx.mkGt(mul, ctx.mkInt(4)));
        System.out.println(solver.check());
        System.out.println(solver.getModel());

    }

    public static void test2() {
        Context ctx = new Context(new HashMap<String, String>());
        BoolExpr p = ctx.mkBoolConst("p");
        BoolExpr q = ctx.mkBoolConst("q");
        BoolExpr r = ctx.mkBoolConst("r");
        BoolExpr pq = ctx.mkImplies(p, q);
        BoolExpr qr = ctx.mkImplies(q, r);
        BoolExpr pr = ctx.mkImplies(p, r);
        BoolExpr conjecture = ctx.mkImplies(ctx.mkAnd(pq, qr), pr);
        Solver solver = ctx.mkSolver();
        solver.add(ctx.mkNot(conjecture));
        System.out.println(solver.check());
    }

    public static void test1() {
        Context context = new Context(new HashMap<String, String>());
        IntSort intSort = context.getIntSort();
//        FuncDecl a = context.mkConstDecl("a", intSort);
        IntExpr a = context.mkIntConst("a");
        Sort[] arguments = new Sort[2];
        arguments[0] = context.getIntSort();
        arguments[1] = context.getBoolSort();
        FuncDecl f = context.mkFuncDecl("f", arguments, context.getIntSort());
        BoolExpr b1 = context.mkGt(a, context.mkInt(10));
        Expr result = f.apply(a, context.mkTrue());
        System.out.println(result.toString());
        System.out.println(result.getClass());
        BoolExpr b2 = context.mkLt((IntExpr)result, context.mkInt(100));
        Solver solver = context.mkSolver();
        solver.add(b1);
        solver.add(b2);
        System.out.println(solver.check());
        System.out.println(solver.getModel());
//        System.out.println(f.toString());
//        System.out.println(f.getClass());
//        context.mkGe(a, f);
    }
}