using System;
using System.Collections.Generic;
using System.Linq;
using System.Runtime.Remoting.Contexts;

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
            using (Context ctx = new Context(new Dictionary<string, string> { { "MODEL", "true" } }))
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

                // CheckSat(ctx, CreateLTrimFunction(ctx));

                ctx.Dispose();
            }
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
                    ctx.MkReplace(x, ctx.MkString(" "), ctx.MkString("")),
                    ctx.MkString("")));
            return new[]
            {
                isEmptyFuncRule,
                ctx.MkEq(
                    ctx.MkApp(isEmptyFunc, ctx.MkString("123")),
                    ctx.MkFalse()),
            };
        }

        private static BoolExpr[] CreateLTrimFunction(Context ctx)
        {
            throw new NotImplementedException();
            //var lTrimFunc = ctx.MkFuncDecl("LTrim", new[] { ctx.StringSort }, ctx.StringSort);
            //var x = ctx.MkConst("x", ctx.StringSort);
            //var y = ctx.MkConst("x", ctx.StringSort);
            //var z = ctx.MkConst("x", ctx.StringSort);
            //var lTrimRules = ctx.MkForall(
            //    new []{ x, y, z },

            //)
            //var y = ctx.MkConst("y", ctx.StringSort);
            //return new[]
            //{
            //    ctx.MkNot(ctx.MkEq(
            //        ctx.MkApp(lTrimFunc, x),
            //        ctx.MkApp(lTrimFunc, y))),
            //    ctx.MkEq(x, y),
            //};
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
            }
            var status = solver.Check();
            var unsatCore = solver.UnsatCore;
            Console.WriteLine(solver);
            Console.WriteLine(status);
            Console.WriteLine($"UnsatCore:({string.Join(", ", unsatCore.Select(x => x.ToString()))})");
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
