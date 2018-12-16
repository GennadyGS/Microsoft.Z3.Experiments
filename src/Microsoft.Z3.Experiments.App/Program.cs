using System;
using System.Collections.Generic;

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
                Console.WriteLine(CheckSat(ctx, CreateExprContradiction(ctx)));

                Console.WriteLine(CheckSat(ctx, CreateExprIsEmpty(ctx)));

                Console.WriteLine(CheckSat(ctx, CreateExprIntervals(ctx)));

                Console.WriteLine(CheckSat(ctx, CreateReal(ctx)));

                Console.WriteLine(CheckSat(ctx, CreateContains(ctx)));

                Console.WriteLine(CheckSat(ctx, CreateNotContains(ctx)));

                ctx.Dispose();
            }
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

        private static Status CheckSat(Context ctx, BoolExpr eq)
        {
            var solver = ctx.MkSolver();
            solver.Assert(eq);
            var result = solver.Check();
            return result;
        }
    }
}
