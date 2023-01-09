open Microsoft.Z3

let solveAndPrintResult (context: Context) assertions =
    let timeout = 120_000u

    let solver = context.MkSolver()
    solver.Set("timeout", timeout)
    solver.Assert(assertions |> List.toArray)
    printfn "%s" $"Assertions: {solver}"

    let status = solver.Check()
    printfn "%s" $"Status: {status}"

    if status = Status.SATISFIABLE then
        printfn "%s" $"Model: {solver.Model}"

let rec contains (context: Context) item list =
    list |> List.map (fun listItem -> context.MkEq(listItem, item)) |> context.MkOr

let rec areAllDistinct (context: Context) exprList =
    context.MkDistinct(exprList |> List.toArray)

let getPointSort (context: Context) =
    context.MkTupleSort(
        context.MkSymbol("Point"),
        [| context.MkSymbol("x"); context.MkSymbol("y") |],
        [| context.RealSort; context.RealSort |]
    )

let getTupleMember (context: Context) index (tuple: Expr) =
    let tupleSort = tuple.Sort :?> DatatypeSort
    context.MkApp(tupleSort.Accessors[0][index], tuple)

let getCoordinates (context: Context) point =
    let getCoordinate index point =
        getTupleMember context index point :?> ArithExpr

    getCoordinate 0 point, getCoordinate 1 point

let areColinear (context: Context) (p1, p2, p3) =
    let (x1, y1) = getCoordinates context p1
    let (x2, y2) = getCoordinates context p2
    let (x3, y3) = getCoordinates context p3

    context.MkEq(
        context.MkMul(context.MkSub(y3, y2), context.MkSub(x2, x1)),
        context.MkMul(context.MkSub(y2, y1), context.MkSub(x3, x2))
    )

let areAllColinear (context: Context) points =
    match points with
    | []
    | [ _ ]
    | [ _; _ ] -> context.MkTrue()
    | p1 :: p2 :: tail ->
        tail
        |> List.map (fun point -> areColinear context (p1, p2, point))
        |> context.MkAnd

let createPoints (context: Context) name pointCount =
    let pointSort = getPointSort context
    List.init pointCount (fun i -> context.MkConst($"{name}{i}", pointSort))

let isStraightLine (context: Context) points =
    context.MkAnd(areAllDistinct context points, areAllColinear context points)

let getProblemAssertions (context: Context) (lineCount, pointCount) =
    let lines =
        List.init lineCount (fun i -> createPoints context $"p{i}" pointCount)

    [ yield! lines |> List.map (isStraightLine context) ]

[<EntryPoint>]
let main _ =
    use context = new Context()

    let lineCount = 1
    let pointCount = 4
    let problemAssertions = getProblemAssertions context (lineCount, pointCount)
    solveAndPrintResult context problemAssertions
    0
