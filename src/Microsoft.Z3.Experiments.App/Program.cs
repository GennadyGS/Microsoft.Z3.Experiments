using System;
using System.Collections.Generic;
using System.Linq;
using System.Xml.Serialization;

namespace Microsoft.Z3.Experiments.App
{
    class Program
    {
        static void Main(string[] args)
        {
            Run();
        }

        private static void Run()
        {
            using (Context ctx = new Context(new Dictionary<string, string> { { "MODEL", "false" } }))
            {
                CheckSat(ctx, CreateExprContradiction(ctx));

                CheckSat(ctx, CreateExprIsEmpty(ctx));

                CheckSat(ctx, CreateExprIntervals(ctx));

                CheckSat(ctx, CreateReal(ctx));

                CheckSat(ctx, CreateContains(ctx));

                CheckSat(ctx, CreateNotContains(ctx));

                CheckSat(ctx, CreateNullable(ctx));

                CheckSat(ctx, CreateSatCore(ctx));

                CheckSat(ctx, CreateUnInterpretedFunction(ctx));

                CheckSat(ctx, CreateIsEmptyFunction(ctx));

                //CheckSat(ctx, CreateLTrimFunction(ctx));

                CheckSat(ctx, CreateLTrimFunction2(ctx));

                CheckSat(ctx, CreateTrimFunction(ctx));

                CheckSat(ctx, CreateUpperFunction(ctx));

                ctx.Dispose();
            }
        }

        private static BoolExpr[] CreateUpperFunction(Context ctx)
        {
            var upperFunc = ctx.MkFuncDecl("upper", new[] { ctx.StringSort }, ctx.StringSort);
            var x = (SeqExpr)ctx.MkConst("x", ctx.StringSort);
            var y = (SeqExpr)ctx.MkConst("y", ctx.StringSort);
            var rule = ctx.MkForall(
                new Expr[] { x, y },
                ctx.MkImplies(
                    ctx.MkEq(ctx.MkApp(upperFunc, x), y),
                    ctx.MkEq(ctx.MkLength(x), ctx.MkLength(y))));
            var v1 = (SeqExpr)ctx.MkConst("v1", ctx.StringSort);
            var v2 = (SeqExpr)ctx.MkConst("v2", ctx.StringSort);
            return new[]
            {
                rule,
                ctx.MkEq(ctx.MkApp(upperFunc, v1), v2),
                ctx.MkEq(ctx.MkLength(v1), ctx.MkLength(v2)),
            };
        }

        private static BoolExpr[] CreateTrimFunction(Context ctx)
        {
            var trimFunc = ctx.MkFuncDecl("Trim", new[] { ctx.StringSort }, ctx.StringSort);
            var x = (SeqExpr)ctx.MkConst("x", ctx.StringSort);
            var y = (SeqExpr)ctx.MkConst("y", ctx.StringSort);
            var z = (SeqExpr)ctx.MkConst("z", ctx.StringSort);
            var rule = ctx.MkForall(
                new Expr[] { x, y },
                ctx.MkImplies(
                    ctx.MkEq(ctx.MkApp(trimFunc, x), y),
                    ctx.MkContains(x, y)));
            var v1 = (SeqExpr)ctx.MkConst("v1", ctx.StringSort);
            var v2 = (SeqExpr)ctx.MkConst("v2", ctx.StringSort);
            return new[]
            {
                rule,
                ctx.MkEq(ctx.MkApp(trimFunc, v1), v2),
                ctx.MkLt(ctx.MkLength(v1), ctx.MkLength(v2)),
            };
        }

        private static BoolExpr[] CreateLTrimFunction2(Context ctx)
        {
            var lTrimFunc = ctx.MkFuncDecl("lTrim", new[] { ctx.StringSort }, ctx.StringSort);
            var x = (SeqExpr)ctx.MkConst("x", ctx.StringSort);
            var y = (SeqExpr)ctx.MkConst("y", ctx.StringSort);
            var rule = ctx.MkForall(
                new Expr[] { x, y },
                ctx.MkImplies(
                    ctx.MkEq(ctx.MkApp(lTrimFunc, x), y),
                    ctx.MkSuffixOf(y, x)));
            var v1 = (SeqExpr)ctx.MkConst("v1", ctx.StringSort);
            var v2 = (SeqExpr)ctx.MkConst("v2", ctx.StringSort);
            return new[]
            {
                rule,
                ctx.MkEq(ctx.MkApp(lTrimFunc, v1), v2),
                ctx.MkLe(ctx.MkLength(v1), ctx.MkLength(v2)),
            };
        }

        private static BoolExpr[] CreateUnInterpretedFunction(Context ctx)
        {
            var func = ctx.MkFuncDecl("Func", new []{ ctx.StringSort }, ctx.StringSort);
            var x = ctx.MkConst("x", ctx.StringSort);
            var y = ctx.MkConst("y", ctx.StringSort);
            return new[]
            {
                ctx.MkNot(ctx.MkEq(
                    ctx.MkApp(func, x),
                    ctx.MkApp(func, y))),
                ctx.MkEq(x, y),
            };
        }

        private static BoolExpr[] CreateIsEmptyFunction(Context ctx)
        {
            var isEmptyFunc = ctx.MkFuncDecl("IsEmpty", new[] { ctx.StringSort }, ctx.MkBoolSort());
            var x = (SeqExpr)ctx.MkConst("x", ctx.StringSort);
            var isEmptyFuncRule = ctx.MkForall(
                new Expr[] { x },
                ctx.MkEq(
                    (BoolExpr) ctx.MkApp(isEmptyFunc, x),
                    ctx.MkInRe(x, ctx.MkToRe(ctx.MkString(@"\s*")))));
            return new[]
            {
                isEmptyFuncRule,
                ctx.MkEq(
                    ctx.MkApp(isEmptyFunc, ctx.MkString("   ")),
                    ctx.MkFalse()),
            };
        }

        private static BoolExpr[] CreateLTrimFunction(Context ctx)
        {
            var lTrimFunc = ctx.MkFuncDecl("lTrim", new[] { ctx.StringSort }, ctx.StringSort);
            var x = (SeqExpr)ctx.MkConst("x", ctx.StringSort);
            var y = (SeqExpr)ctx.MkConst("y", ctx.StringSort);
            var z = (SeqExpr)ctx.MkConst("z", ctx.StringSort);
            var rule = ctx.MkForall(
                new Expr[] {x, y, z},
                ctx.MkImplies(
                    ctx.MkAnd(
                        ctx.MkEq(
                            ctx.MkConcat(z, y),
                            x),
                        ctx.MkInRe(z, ctx.MkToRe(ctx.MkString(@"\s*")))),
                    ctx.MkEq(ctx.MkApp(lTrimFunc, x), y)));
            return new[]
            {
                rule,
                ctx.MkEq(
                    ctx.MkApp(lTrimFunc, ctx.MkString(" 123")),
                    ctx.MkString("3")),
            };
        }

        private static BoolExpr[] CreateSatCore(Context ctx)
        {
            var varA = ctx.MkConst(ctx.MkSymbol("a"), ctx.StringSort);
            return new[]
            {
                ctx.MkEq(varA, ctx.MkString("2")),
                ctx.MkNot(
                    ctx.MkEq(varA, ctx.MkString("2"))),
                ctx.MkEq(varA, ctx.MkString("1")),
                ctx.MkNot(
                    ctx.MkEq(varA, ctx.MkString("1"))),
            };
        }

        private static void CheckSat(Context ctx, params BoolExpr[] exprs)
        {
            var solver = ctx.MkSolver();
            for (var index = 0; index < exprs.Length; index++)
            {
                var expr = exprs[index];
                solver.AssertAndTrack(
                    expr, 
                    (BoolExpr)ctx.MkConst($"p{index}", ctx.BoolSort ));
                //solver.Assert(expr);
            }
            Console.WriteLine(solver);
            var status = solver.Check();
            Console.WriteLine(status);
            if (status == Status.SATISFIABLE)
            {
                var model = solver.Model;
                Console.WriteLine($"Model:({model})");
            }
            else
            {
                var unsatCore = solver.UnsatCore;
                Console.WriteLine($"UnsatCore:({string.Join(", ", unsatCore.Select(x => x.ToString()))})");
            }
            Console.WriteLine();
        }

        private static BoolExpr CreateContains(Context ctx)
        {
            var varA = ctx.MkConst(ctx.MkSymbol("a"), ctx.StringSort);
            return ctx.MkAnd(
                ctx.MkEq(varA, ctx.MkString("abc")), 
                ctx.MkContains((SeqExpr)varA, ctx.MkString("ac")));
        }

        private static BoolExpr CreateNotContains(Context ctx) => 
            ctx.MkNot(CreateContains(ctx));

        private static BoolExpr CreateExprIntervals(Context ctx)
        {
            var varA = ctx.MkConst(ctx.MkSymbol("a"), ctx.IntSort);
            return ctx.MkAnd(
                ctx.MkGt((ArithExpr)varA, ctx.MkInt(10)),
                ctx.MkLt((ArithExpr)varA, ctx.MkInt(12)));
        }

        private static BoolExpr CreateExprContradiction(Context ctx)
        {
            var varA = ctx.MkConst(ctx.MkSymbol("a"), ctx.StringSort);
            return ctx.MkAnd(
                ctx.MkEq(varA, ctx.MkString("1")),
                ctx.MkNot(
                    ctx.MkEq(varA, ctx.MkString("1"))));
        }

        private static BoolExpr CreateReal(Context ctx)
        {
            var varA = ctx.MkRealConst("a");
            return ctx.MkAnd(
                ctx.MkGt(varA, ctx.MkReal(1)),
                ctx.MkLe(varA, ctx.MkReal(10, 10)));
        }

        private static BoolExpr CreateExprIsEmpty(Context ctx)
        {
            var varA = ctx.MkConst(ctx.MkSymbol("a"), ctx.StringSort);
            return ctx.MkAnd(
                ctx.MkOr(
                    ctx.MkEq(varA, ctx.MkString("")),
                    ctx.MkEq(varA, ctx.MkString("NULL"))),
                ctx.MkNot(ctx.MkEq(varA, ctx.MkString("NA"))));
        }

        private static BoolExpr CreateNullable(Context ctx)
        {
            (DatatypeSort, Constructor, Constructor) CreateNullableSort(Sort sort)
            {
                var nullConstr = ctx.MkConstructor("null", "isNull");
                var valueConstr = ctx.MkConstructor(
                    "value", 
                    "hasValue", 
                    new[] {"value"}, 
                    new[] { sort });
                var datatypeSort = ctx.MkDatatypeSort("Nullable", new[]
                {
                    nullConstr, valueConstr
                });
                return (datatypeSort, valueConstr, nullConstr);
            }

            var (dataType, valueConstructor, nullConstructor) = CreateNullableSort(ctx.IntSort);
            var (dataType2, valueConstructor2, nullConstructor2) = CreateNullableSort(ctx.RealSort);
            var a = ctx.MkConst("a", dataType);
            var b = ctx.MkConst("b", dataType2);
            var const0 = ctx.MkApp(valueConstructor.ConstructorDecl, ctx.MkInt(0));
            var const1 = ctx.MkApp(valueConstructor.ConstructorDecl, ctx.MkInt(1));
            var constNull = ctx.MkApp(nullConstructor.ConstructorDecl);
            var getValueDecl = valueConstructor.AccessorDecls[0];
            var aValue = (ArithExpr) ctx.MkApp(getValueDecl, a);
            var aIsNull = (BoolExpr)ctx.MkApp(nullConstructor2.TesterDecl, a);
            var aIsValue = (BoolExpr) ctx.MkApp(valueConstructor2.TesterDecl, a);
            return ctx.MkAnd(
                ctx.MkAnd(aIsValue, ctx.MkGe(aValue, ctx.MkInt(0))),
                aIsNull);
        }
    }
}
