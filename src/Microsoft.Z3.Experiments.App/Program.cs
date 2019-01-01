using System;
using System.Collections.Generic;
using System.Linq;

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

                CheckSimplify(ctx);

                ctx.Dispose();
            }
        }

        private static void CheckSimplify(Context ctx)
        {
            var tactic = ctx.MkTactic("ctx-solver-simplify");
            var a = ctx.MkRealConst("a");
            var expr = ctx.MkOr(
                ctx.MkGt(a, ctx.MkReal(1)),
                ctx.MkGt(a, ctx.MkReal(2)));
            var goal = ctx.MkGoal();
            goal.Assert(expr);
            var result = tactic.Apply(goal);
            Console.WriteLine(result);
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
                solver.AssertAndTrack(expr, ctx.MkBoolConst($"{index}"));
            }
            var status = solver.Check();
            var unsatCore = solver.UnsatCore;
            Console.WriteLine(solver);
            Console.WriteLine(status);
            var unsatCoreIds = unsatCore
                .Select(expr => int.Parse(expr.FuncDecl.Name.ToString()))
                .ToArray();
            Console.WriteLine($"UnsatCore:({string.Join(", ", unsatCore.Select(x => x.ToString()))})");
            Console.WriteLine($"UnsatCoreIds:({string.Join(", ", unsatCoreIds.Select(x => x.ToString()))})");
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
