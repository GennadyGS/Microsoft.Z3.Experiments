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
            using (Context context = new Context(new Dictionary<string, string> { { "MODEL", "false" } }))
            {
                CheckSat(context, CreateExprContradiction(context));

                CheckSat(context, CreateBool(context));

                CheckSat(context, CreateExprIsEmpty(context));

                CheckSat(context, CreateExprIntervals(context));

                CheckSat(context, CreateReal(context));

                CheckSat(context, CreateReal2(context));

                CheckSat(context, CreateContains(context));

                CheckSat(context, CreateNotContains(context));

                CheckSat(context, CreateNullable(context));

                CheckSat(context, CreateSatCore(context));

                CheckSat(context, CreateIsEmptyFunction(context));

                //CheckSat(context, CreateLTrimFunction(context));

                CheckSat(context, CreateLTrimFunction2(context));

                CheckSat(context, CreateTrimFunction(context));

                // CheckSat(context, CreateUpperFunction(context));

                CheckSat(context, CreateIntToString(context));

                CheckSimplify(context);

                CheckSat(context, CreateNullable2(context));

                CheckSat(context, CreateNullable3(context));

                CheckSat(context, CreateFunctionAxiom(context));

                CheckSat(context, CreateAlphaNumeric(context));

                CheckSat(context, CreateNonAlphaNumeric(context));

                CheckSat(context, CreateNonAlphaNumeric2(context));

                CheckSat(context, CreateNonAlphaNumeric2(context));

                CheckSat(context, CreateAllDistinctEmpty(context));

                CheckSat(context, CreateAllDistinct1(context));

                CheckSat(context, CreateAllDistinct2(context));

                CheckSat(context, CreateAllDistinctSame(context));

                CheckSat(context, CreateDivide(context));

                CheckSat(context, CreateUnInterpretedFunction(context));

                CheckSat(context, CreateFinite(context));

                CheckSat(context, CreateBigIntToString(context));

                CheckSat(context, CreateIntDivide(context));

                CheckSat(context, CreateAddYears(context));

                CheckSat(context, CreateRound(context));
                CheckSat(context, CreateCustom(context));
            }
        }

        private static BoolExpr[] CreateUpperFunction(Context context)
        {
            var upperFunc = context.MkFuncDecl("upper", new[] { context.StringSort }, context.StringSort);
            var x = (SeqExpr)context.MkConst("x", context.StringSort);
            var y = (SeqExpr)context.MkConst("y", context.StringSort);
            var rule = context.MkForall(
                new Expr[] { x, y },
                context.MkImplies(
                    context.MkEq(context.MkApp(upperFunc, x), y),
                    context.MkEq(context.MkLength(x), context.MkLength(y))));
            var v1 = (SeqExpr)context.MkConst("v1", context.StringSort);
            var v2 = (SeqExpr)context.MkConst("v2", context.StringSort);
            return new[]
            {
                rule,
                context.MkEq(context.MkApp(upperFunc, v1), v2),
                context.MkEq(context.MkLength(v1), context.MkLength(v2)),
            };
        }

        private static BoolExpr[] CreateTrimFunction(Context context)
        {
            var trimFunc = context.MkFuncDecl("Trim", new[] { context.StringSort }, context.StringSort);
            var x = (SeqExpr)context.MkConst("x", context.StringSort);
            var y = (SeqExpr)context.MkConst("y", context.StringSort);
            var z = (SeqExpr)context.MkConst("z", context.StringSort);
            var rule = context.MkForall(
                new Expr[] { x, y },
                context.MkImplies(
                    context.MkEq(context.MkApp(trimFunc, x), y),
                    context.MkContains(x, y)));
            var v1 = (SeqExpr)context.MkConst("v1", context.StringSort);
            var v2 = (SeqExpr)context.MkConst("v2", context.StringSort);
            return new[]
            {
                rule,
                context.MkEq(context.MkApp(trimFunc, v1), v2),
                context.MkLt(context.MkLength(v1), context.MkLength(v2)),
            };
        }

        private static BoolExpr[] CreateLTrimFunction2(Context context)
        {
            var lTrimFunc = context.MkFuncDecl("lTrim", new[] { context.StringSort }, context.StringSort);
            var x = (SeqExpr)context.MkConst("x", context.StringSort);
            var y = (SeqExpr)context.MkConst("y", context.StringSort);
            var rule = context.MkForall(
                new Expr[] { x, y },
                context.MkImplies(
                    context.MkEq(context.MkApp(lTrimFunc, x), y),
                    context.MkSuffixOf(y, x)));
            var v1 = (SeqExpr)context.MkConst("v1", context.StringSort);
            var v2 = (SeqExpr)context.MkConst("v2", context.StringSort);
            return new[]
            {
                rule,
                context.MkEq(context.MkApp(lTrimFunc, v1), v2),
                context.MkLe(context.MkLength(v1), context.MkLength(v2)),
            };
        }

        private static BoolExpr[] CreateUnInterpretedFunction(Context context)
        {
            var func = context.MkFuncDecl("Functions.Func", new []{ context.StringSort }, context.StringSort);
            var x = context.MkConst("Fields.X", context.StringSort);
            var y = context.MkConst("Fields.Y", context.StringSort);
            return new[]
            {
                context.MkNot(context.MkEq(
                    context.MkApp(func, x),
                    context.MkApp(func, y))),
                context.MkEq(x, y),
            };
        }

        private static BoolExpr[] CreateIsEmptyFunction(Context context)
        {
            var isEmptyFunc = context.MkFuncDecl("IsEmpty", new[] { context.StringSort }, context.MkBoolSort());
            var x = (SeqExpr)context.MkConst("x", context.StringSort);
            var isEmptyFuncRule = context.MkForall(
                new Expr[] { x },
                context.MkEq(
                    (BoolExpr) context.MkApp(isEmptyFunc, x),
                    context.MkInRe(x, context.MkToRe(context.MkString(@"\s*")))));
            return new[]
            {
                isEmptyFuncRule,
                context.MkEq(
                    context.MkApp(isEmptyFunc, context.MkString("   ")),
                    context.MkFalse()),
            };
        }

        private static BoolExpr[] CreateLTrimFunction(Context context)
        {
            var lTrimFunc = context.MkFuncDecl("lTrim", new[] { context.StringSort }, context.StringSort);
            var x = (SeqExpr)context.MkConst("x", context.StringSort);
            var y = (SeqExpr)context.MkConst("y", context.StringSort);
            var z = (SeqExpr)context.MkConst("z", context.StringSort);
            var rule = context.MkForall(
                new Expr[] {x, y, z},
                context.MkImplies(
                    context.MkAnd(
                        context.MkEq(
                            context.MkConcat(z, y),
                            x),
                        context.MkInRe(z, context.MkToRe(context.MkString(@"\s*")))),
                    context.MkEq(context.MkApp(lTrimFunc, x), y)));
            return new[]
            {
                rule,
                context.MkEq(
                    context.MkApp(lTrimFunc, context.MkString(" 123")),
                    context.MkString("3")),
            };
        }

        private static BoolExpr CreateBool(Context context)
        {
            var varA = context.MkConst(context.MkSymbol("a"), context. BoolSort);
            return context.MkEq(varA, context.MkTrue());
        }

        private static void CheckSimplify(Context context)
        {
            var tactic = context.MkTactic("ctx-solver-simplify");
            var a = context.MkRealConst("a");
            var expr = context.MkOr(
                context.MkGt(a, context.MkReal(1)),
                context.MkGt(a, context.MkReal(2)));
            var goal = context.MkGoal();
            goal.Assert(expr);
            var result = tactic.Apply(goal);
            Console.WriteLine(result);
        }

        private static BoolExpr[] CreateSatCore(Context context)
        {
            var varA = context.MkConst(context.MkSymbol("a"), context.StringSort);
            return new[]
            {
                context.MkEq(varA, context.MkString("2")),
                context.MkNot(
                    context.MkEq(varA, context.MkString("2"))),
                context.MkEq(varA, context.MkString("1")),
                context.MkNot(
                    context.MkEq(varA, context.MkString("1"))),
            };
        }

        private static void CheckSat(Context context, params BoolExpr[] exprs)
        {
            var solver = context.MkSolver();
            for (var index = 0; index < exprs.Length; index++)
            {
                var expr = exprs[index];
                solver.AssertAndTrack(expr, context.MkBoolConst($"{index}"));
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
                var unsatCoreIds = unsatCore
                    .Select(expr => int.Parse(expr.FuncDecl.Name.ToString()))
                    .ToArray();
                Console.WriteLine($"UnsatCore:({string.Join(", ", unsatCore.Select(x => x.ToString()))})");
                Console.WriteLine($"UnsatCoreIds:({string.Join(", ", unsatCoreIds.Select(x => x.ToString()))})");
            }
            Console.WriteLine("----------------------------------");
        }

        private static BoolExpr CreateContains(Context context)
        {
            var varA = context.MkConst(context.MkSymbol("a"), context.StringSort);
            return context.MkAnd(
                context.MkEq(varA, context.MkString("abc")), 
                context.MkContains((SeqExpr)varA, context.MkString("ac")));
        }

        private static BoolExpr CreateNotContains(Context context) => 
            context.MkNot(CreateContains(context));

        private static BoolExpr CreateExprIntervals(Context context)
        {
            var varA = context.MkConst(context.MkSymbol("a"), context.IntSort);
            return context.MkAnd(
                context.MkGt((ArithExpr)varA, context.MkInt(10)),
                context.MkLt((ArithExpr)varA, context.MkInt(12)));
        }

        private static BoolExpr CreateExprContradiction(Context context)
        {
            var varA = context.MkConst(context.MkSymbol("a"), context.StringSort);
            return context.MkAnd(
                context.MkEq(varA, context.MkString("1")),
                context.MkNot(
                    context.MkEq(varA, context.MkString("1"))));
        }

        private static BoolExpr CreateReal(Context context)
        {
            var varA = context.MkRealConst("a");
            return context.MkAnd(
                context.MkGt(varA, context.MkReal(1)),
                context.MkLe(varA, context.MkReal(10, 10)));
        }

        private static BoolExpr CreateReal2(Context context)
        {
            var varA = context.MkIntConst("a");
            return context.MkEq(varA, context.MkReal(1));
        }

        private static BoolExpr CreateExprIsEmpty(Context context)
        {
            var varA = context.MkConst(context.MkSymbol("a"), context.StringSort);
            return context.MkAnd(
                context.MkOr(
                    context.MkEq(varA, context.MkString("")),
                    context.MkEq(varA, context.MkString("NULL"))),
                context.MkNot(context.MkEq(varA, context.MkString("NA"))));
        }

        private static BoolExpr CreateNullable2(Context context)
        {
            var (dataType, valueConstructor, _) = CreateNullableSort(context.IntSort, context);
            var a = context.MkConst("a", dataType);
            var b = context.MkConst("b", dataType);
            var constant = context.MkApp(valueConstructor.ConstructorDecl, context.MkInt(42));
            return context.MkAnd(
                context.MkEq(a, constant),
                context.MkEq(a, b));
        }

        private static BoolExpr CreateNullable3(Context context)
        {
            var (dataType, _, nullConstructor) = CreateNullableSort(context.IntSort, context);
            var a = context.MkConst("a", dataType);
            var b = context.MkConst("b", dataType);
            var nullConstant = context.MkApp(nullConstructor.ConstructorDecl);
            return context.MkAnd(
                context.MkEq(a, nullConstant),
                context.MkEq(a, b));
        }

        private static BoolExpr CreateNullable(Context context)
        {
            var (dataType, valueConstructor, nullConstructor) = CreateNullableSort(context.IntSort, context);
            var (dataType2, valueConstructor2, nullConstructor2) = CreateNullableSort(context.RealSort, context);
            var a = context.MkConst("a", dataType);
            var b = context.MkConst("b", dataType2);
            var const0 = context.MkApp(valueConstructor.ConstructorDecl, context.MkInt(0));
            var const1 = context.MkApp(valueConstructor.ConstructorDecl, context.MkInt(1));
            var constNull = context.MkApp(nullConstructor.ConstructorDecl);
            var getValueDecl = valueConstructor.AccessorDecls[0];
            var aValue = (ArithExpr)context.MkApp(getValueDecl, a);
            var aIsNull = (BoolExpr)context.MkApp(nullConstructor2.TesterDecl, a);
            var aIsValue = (BoolExpr)context.MkApp(valueConstructor2.TesterDecl, a);
            return context.MkAnd(
                context.MkAnd(aIsValue, context.MkGe(aValue, context.MkInt(0))),
                aIsNull);
        }

        private static BoolExpr CreateAlphaNumeric(Context context) =>
            context.MkInRe(
                (SeqExpr)context.MkConst("x", context.StringSort),
                context.MkLoop(
                    context.MkUnion(
                        context.MkRange(context.MkString("0"), context.MkString("9")),
                        context.MkRange(context.MkString("A"), context.MkString("Z")),
                        context.MkRange(context.MkString("a"), context.MkString("z"))),
                    3, 
                    5));

        private static BoolExpr CreateNonAlphaNumeric(Context context)
        {
            SeqExpr x = (SeqExpr)context.MkConst("x", context.StringSort);
            return 
                context.MkAnd(
                    context.MkEq(x, context.MkString("11111")),
                    context.MkOr(
                        context.MkLt(context.MkLength(x), context.MkInt(3)),
                        context.MkGt(context.MkLength(x), context.MkInt(5)),
                        context.MkInRe(
                            x,
                            context.MkConcat(
                                context.MkFullRe(context.MkReSort(context.StringSort)),
                                    context.MkUnion(
                                        context.MkRange(context.MkString("\\x00"), context.MkString("\\x2F")),
                                        context.MkRange(context.MkString("\\x3A"), context.MkString("\\xFF"))),
                                context.MkFullRe(context.MkReSort(context.StringSort))))));
        }

        private static BoolExpr[] CreateNonAlphaNumeric2(Context context)
        {
            var x = (SeqExpr)context.MkConst("x", context.StringSort);
            var y = (SeqExpr)context.MkConst("y", context.StringSort);
            var alphaNumChars = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz"
                .ToList();
            return new[]
            {

                context.MkEq(x, context.MkString("11111")),
                context.MkAnd(alphaNumChars.Select(c =>
                    context.MkNot(
                        context.MkEq(y, context.MkString(c.ToString()))))),
                context.MkEq(context.MkLength(y), context.MkInt(1)),
                context.MkOr(
                    context.MkLt(context.MkLength(x), context.MkInt(3)),
                    context.MkGt(context.MkLength(x), context.MkInt(5)),
                    context.MkContains(x, y)),
            };
        }

        private static BoolExpr CreateIntToString(Context context)
        {
            var x = context.MkConst("x", context.IntSort);
            return context.MkEq(
                context.IntToString(x), 
                context.MkString("4"));
        }

        private static (DatatypeSort, Constructor, Constructor) CreateNullableSort(Sort sort, Context context)
        {
            var mkConstructor = context.MkConstructor("null", "isNull");
            var valueConstructor = context.MkConstructor("value", "hasValue", new[] {"value"}, new[] {sort});
            var dataTypeSort = context.MkDatatypeSort("Nullable", new[] {mkConstructor, valueConstructor});
            return (dataTypeSort, valueConstructor, mkConstructor);
        }

        private static BoolExpr[] CreateFunctionAxiom(Context context)
        {
            var func1 = context.MkFuncDecl("func1", new[] { context.StringSort }, context.BoolSort);
            var func2 = context.MkFuncDecl("func2", Array.Empty<Sort>(), context.BoolSort);
            var x = (SeqExpr)context.MkConst("x", context.StringSort);
            var rule = context.MkForall(
                new Expr[] { x },
                context.MkImplies(
                    context.MkApp(func1, x) as BoolExpr,
                    context.MkNot(context.MkApp(func2) as BoolExpr)));
            var v = (SeqExpr)context.MkConst("v", context.StringSort);
            return new[]
            {
                rule,
                context.MkApp(func1, v) as BoolExpr,
                context.MkApp(func2) as BoolExpr,
            };
        }

        private static BoolExpr CreateAllDistinctEmpty(Context context)
        {
            return context.MkDistinct();
        }

        private static BoolExpr CreateAllDistinct1(Context context)
        {
            return context.MkDistinct(
                context.MkConst("a", context.StringSort));
        }

        private static BoolExpr CreateAllDistinct2(Context context)
        {
            return context.MkDistinct(
                context.MkConst("a", context.StringSort),
                context.MkConst("b", context.StringSort));
        }

        private static BoolExpr CreateAllDistinctSame(Context context)
        {
            return context.MkDistinct(
                context.MkConst("a", context.StringSort),
                context.MkConst("a", context.StringSort));
        }

        private static BoolExpr CreateDivide(Context context)
        {
            return context.MkEq(
                context.MkConst("A", context.RealSort),
                context.MkDiv(
                    (ArithExpr) context.MkConst("B", context.RealSort),
                    (ArithExpr) context.MkConst("C", context.RealSort)));
        }

        private static BoolExpr CreateIntDivide(Context context)
        {
            return context.MkEq(
                context.MkConst("A", context.IntSort),
                context.MkMod(context.MkInt(-5), context.MkInt(3)));
        }

        private static BoolExpr[] CreateAddYears(Context context)
        {
            const int DaysPerNormalYear = 10;
            const int YearsPerCycle = 4;
            const int DaysPerCycle = DaysPerNormalYear * YearsPerCycle + 1;

            var day = (IntExpr)context.MkConst("day", context.IntSort);
            var years = (IntExpr)context.MkConst("years", context.IntSort);
            var result = (IntExpr)context.MkConst("result", context.IntSort);

            var yearsPerCycle = context.MkInt(YearsPerCycle);
            var daysPerCycle = context.MkInt(DaysPerCycle);
            var daysPerCycleMinusOne = 
                (IntExpr)context.MkSub(context.MkInt(DaysPerCycle), context.MkInt(1));

            IntExpr GetMainPart(IntExpr dividend, IntExpr divider) =>
                (IntExpr)context.MkMul(
                    context.MkDiv(dividend, divider),
                    divider);

            var dayInCycle = context.MkMod(day, daysPerCycle);
            var rule = context.MkEq(
                result,
                context.MkAdd(
                    GetMainPart(day, daysPerCycle),
                    GetMainPart(dayInCycle, daysPerCycleMinusOne),
                    context.MkDiv(
                        context.MkAdd(
                            context.MkMul(
                                context.MkMod(dayInCycle, daysPerCycleMinusOne),
                                daysPerCycle,
                                yearsPerCycle),
                            context.MkMul(
                                years,
                                daysPerCycle,
                                daysPerCycleMinusOne)),
                        context.MkMul(yearsPerCycle, daysPerCycleMinusOne))));
            return new[] {
                rule,
                context.MkEq(day, context.MkInt(-41)),
                // context.MkEq(years, context.MkInt(4)),
                context.MkEq(result, context.MkInt(0)),
            };
        }

        private static BoolExpr CreateFinite(Context context)
        {
            var finiteSort = context.MkFiniteDomainSort("Sort", 10000);
            return context.MkEq(
                context.MkNumeral(1, finiteSort),
                context.MkConst("A", finiteSort));
        }

        private static BoolExpr CreateBigIntToString(Context context)
        {
            var x = (IntExpr)context.MkConst("x", context.IntSort);
            var y = (SeqExpr)context.MkConst("y", context.StringSort);
            return 
                context.MkAnd(
                    context.MkEq(context.IntToString(x), y),
                    context.MkEq(
                        context.MkMod(x, context.MkInt(97)), 
                        context.MkInt(1)),
                        context.MkEq(context.MkLength(y), context.MkInt(23)));
        }

        private static BoolExpr CreateRound(Context context)
        {
            var x = (IntExpr)context.MkConst("x", context.IntSort);
            var y = (RealExpr)context.MkConst("y", context.RealSort);
            return
                context.MkAnd(
                    context.MkEq(context.MkReal2Int(y), x),
                    context.MkEq(y, context.MkReal(-1, 10)));
        }
        private static BoolExpr[] CreateCustom(Context context)
        {

            return context.ParseSMTLIB2String(@"
(declare-datatypes ((Special_String_NA_Null 0)) (((Value (value String)) (Null) (NA))))
(declare-datatypes ((Special_String_Exempt_NA_Null 0)) (((Value1 (value String)) (Null) (NA) (Exempt))))
(declare-fun Fields.ZipCode () Special_String_Exempt_NA_Null)
(declare-fun Fields.State () Special_String_NA_Null)
(declare-fun Functions.IsStateCode (String) Bool)
(declare-fun Fields.City () Special_String_NA_Null)
(declare-fun Fields.StreetAddress () Special_String_Exempt_NA_Null)
(assert (let ((a!1 (not (or (= Fields.City (Value """")))))
      (a!2 (not (or (= Fields.State (Value """")))))
      (a!3 (not (or (= Fields.ZipCode (Value1 """")))))
      (a!6 (not (or ((_ is (Null () Special_String_Exempt_NA_Null))
                      Fields.StreetAddress)
                    (= Fields.StreetAddress (Value1 """")))))
      (a!7 (or ((_ is (Null () Special_String_NA_Null)) Fields.City)
               (or (= Fields.City (Value """")))))
      (a!8 (or (and ((_ is (Value (String) Special_String_NA_Null))
                    Fields.State)
                    (Functions.IsStateCode (value Fields.State)))
               ((_ is (NA () Special_String_NA_Null)) Fields.State)))
      (a!9 (or ((_ is (Null () Special_String_NA_Null)) Fields.State)
               (or (= Fields.State (Value """")))))
      (a!10 (re.++ (re.++ (re.++ (re.range ""0"" ""9"") (re.range ""0"" ""9""))
                          (re.range ""0"" ""9""))
                   (re.range ""0"" ""9"")))
      (a!15(or((_ is (Null() Special_String_Exempt_NA_Null)) Fields.ZipCode)
                (or(= Fields.ZipCode(Value1 """"))))))
(let((a!4(not(and((_ is (NA() Special_String_Exempt_NA_Null))
                       Fields.StreetAddress)
                     (and((_ is (Value(String) Special_String_NA_Null))
                            Fields.City)
                          a!1)
                     (and((_ is (Value(String) Special_String_NA_Null))
                            Fields.State)
                          a!2)

                     (and((_ is (Value1(String) Special_String_Exempt_NA_Null))
                            Fields.ZipCode)
                          a!3))))
      (a!5(not(and(and((_ is (Value(String) Special_String_NA_Null))
                            Fields.City)
                          a!1)
                     (and((_ is (Value(String) Special_String_NA_Null))
                            Fields.State)
                          a!2)
                     (and((_ is (Value1(String) Special_String_Exempt_NA_Null))
                            Fields.ZipCode)
                          a!3))))
      (a!11(re.++(re.++(re.++ a!10(re.range ""0"" ""9""))(str.to_re ""-""))
                   (re.range ""0"" ""9"")))
      (a!13(and((_ is (Value1(String) Special_String_Exempt_NA_Null))
                   Fields.ZipCode)
                 (str.in_re(value Fields.ZipCode)
                            (re.++ a!10(re.range ""0"" ""9""))))))
(let((a!12(re.++(re.++(re.++ a!11(re.range ""0"" ""9""))(re.range ""0"" ""9""))
                   (re.range ""0"" ""9""))))
(let((a!14(or(and((_ is (Value1(String) Special_String_Exempt_NA_Null))
                       Fields.ZipCode)
                     (str.in_re(value Fields.ZipCode) a!12))
                a!13
                ((_ is (NA() Special_String_Exempt_NA_Null)) Fields.ZipCode)
                ((_ is (Exempt() Special_String_Exempt_NA_Null))
                  Fields.ZipCode))))
  (or(and a!4
           (not a!5)
           a!6
           (not a!7)
           (and a!8(not a!9))
           (and a!14(not a!15)))
      (and(not a!4)
           a!5
           a!6
           (not a!7)
           (and a!8(not a!9))
           (and a!14(not a!15)))))))))
");
        }
    }
}
