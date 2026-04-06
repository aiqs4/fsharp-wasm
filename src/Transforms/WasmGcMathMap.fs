/// WasmGC dispatch for Math operations and the Map<int,int> IComparer intercept.
/// dispatchMathCall — routes standard math selectors (abs, min, max, round, …)
///                    to the appropriate WasmGC instructions or software helpers.
/// tryMapInline      — intercepts Fable's IComparer-injected Map.ofList / Map.empty
///                    calls, drops the injected comparator, and routes to Map_ofList /
///                    Map_empty with the correct WasmGC return type from KnownFuncs.
module Fable.Transforms.WasmGc.WasmGcMathMap

open Fable
open Fable.AST
open Fable.AST.Fable
open Fable.AST.WasmGc
open Fable.Transforms.WasmGc.WasmGcTypes
open Fable.Transforms.WasmGc.WasmGcBuilder
open Fable.Transforms.WasmGc.WasmGcRuntime

// ─────────────────────────────────────────────────────────────────
// Math dispatch
// ─────────────────────────────────────────────────────────────────

let dispatchMathCall (name: string) (wArgs: WExpr list) (ty: WType) : WExpr =
    match name, wArgs, ty with
    // abs
    | "abs", [arg], WType.F64 -> WExpr.Unary(WUnaryOp.Abs, arg, WType.F64)
    | "abs", [arg], WType.F32 -> WExpr.Unary(WUnaryOp.Abs, arg, WType.F32)
    | "abs", [arg], WType.I32 ->
        wasm {
            let! tmp = arg
            return wasmIf (ltS tmp (i32Const 0)) (sub (i32Const 0) tmp) tmp
        }
    | "abs", [arg], WType.I64 ->
        wasm {
            let! tmp = arg
            return wasmIf (ltS tmp (i64Const 0L))
                (WExpr.Binary(WBinaryOp.Sub, i64Const 0L, tmp, WType.I64)) tmp
        }
    // sqrt
    | "sqrt", [arg], WType.F64 -> WExpr.Unary(WUnaryOp.Sqrt, arg, WType.F64)
    | "sqrt", [arg], WType.F32 -> WExpr.Unary(WUnaryOp.Sqrt, arg, WType.F32)
    // floor
    | "floor", [arg], WType.F64 -> WExpr.Unary(WUnaryOp.Floor, arg, WType.F64)
    | "floor", [arg], WType.F32 -> WExpr.Unary(WUnaryOp.Floor, arg, WType.F32)
    // ceil
    | ("ceil" | "ceiling"), [arg], WType.F64 -> WExpr.Unary(WUnaryOp.Ceil, arg, WType.F64)
    | ("ceil" | "ceiling"), [arg], WType.F32 -> WExpr.Unary(WUnaryOp.Ceil, arg, WType.F32)
    // trunc
    | ("trunc" | "truncate"), [arg], WType.F64 -> WExpr.Unary(WUnaryOp.Trunc, arg, WType.F64)
    | ("trunc" | "truncate"), [arg], WType.F32 -> WExpr.Unary(WUnaryOp.Trunc, arg, WType.F32)
    // round / nearest
    | ("round" | "nearest"), [arg], WType.F64 -> WExpr.Unary(WUnaryOp.Nearest, arg, WType.F64)
    | ("round" | "nearest"), [arg], WType.F32 -> WExpr.Unary(WUnaryOp.Nearest, arg, WType.F32)
    | ("round" | "nearest"), [arg; _], WType.F64 -> WExpr.Unary(WUnaryOp.Nearest, arg, WType.F64)
    | ("round" | "nearest"), [arg; _], WType.F32 -> WExpr.Unary(WUnaryOp.Nearest, arg, WType.F32)
    // min
    | "min", [a; b], WType.F64 -> WExpr.Binary(WBinaryOp.Min, a, b, WType.F64)
    | "min", [a; b], WType.F32 -> WExpr.Binary(WBinaryOp.Min, a, b, WType.F32)
    | "min", [a; b], (WType.I32 | WType.I64) ->
        wasm {
            let! ta = a
            let! tb = b
            return wasmIf (ltS ta tb) ta tb
        }
    // max
    | "max", [a; b], WType.F64 -> WExpr.Binary(WBinaryOp.Max, a, b, WType.F64)
    | "max", [a; b], WType.F32 -> WExpr.Binary(WBinaryOp.Max, a, b, WType.F32)
    | "max", [a; b], (WType.I32 | WType.I64) ->
        wasm {
            let! ta = a
            let! tb = b
            return wasmIf (gtS ta tb) ta tb
        }
    // sign
    | "sign", [arg], _ ->
        wasm {
            let! tmp = arg
            return wasmIf (gtS tmp (i32Const 0))
                (i32Const 1)
                (wasmIf (ltS tmp (i32Const 0)) (i32Const (-1)) (i32Const 0))
        }
    | _ ->
        eprintfn "[WasmGc] WARNING: unhandled Math call '%s' — emitting I32 0" name
        WExpr.Const(WConst.I32 0)

// ─────────────────────────────────────────────────────────────────
// Map module intercept
// ─────────────────────────────────────────────────────────────────
/// Intercept standard F# `Map.*` calls that come through Fable's `mapModule`
/// replacement. Two operations get an extra IComparer argument appended by
/// Fable's `injectArg`:
///   - `Map.ofList [pairs...]`  → `LibCall("Map", "ofList", [list; comparer])`
///   - `Map.empty`              → `LibCall("Map", "empty",  [comparer])`
/// We drop the comparer (it's emitted as Nop anyway) and call the compiled
/// fable-library function directly, using the actual return type from KnownFuncs
/// to avoid the `FSharpMap<int,int>` → `I32` fallback in mapTypeKnown.
///
/// All other Map operations (`add`, `find`, `tryFind`, `containsKey`) receive
/// NO injected comparer, so they route correctly via KnownFuncsByPath as long
/// as the actual return type is used (see the fixed fallback in Fable2WasmGc).
let tryMapInline
        (ctx: Ctx)
        (importStem: string)
        (selector: string)
        (wArgs: WExpr list) : WExpr option =
    if importStem <> "Map" then None
    else
    match selector, wArgs with
    // Map.ofList [pairs; _comparer] — drop injected comparer, call Map_ofList(list)
    | "ofList", [wList; _comparer] ->
        match Map.tryFind "Map_ofList" ctx.KnownFuncs with
        | Some (_, retTy) -> Some(WExpr.Call("Map_ofList", [wList], retTy))
        | None -> None
    // Map.empty [_comparer] — drop injected comparer, call Map_empty()
    | "empty", [_comparer] ->
        match Map.tryFind "Map_empty" ctx.KnownFuncs with
        | Some (_, retTy) -> Some(WExpr.Call("Map_empty", [], retTy))
        | None -> None
    // Map.map routes to Map_mapValues (since "map" conflicts in F#)
    | "map", wArgs ->
        match Map.tryFind "Map_mapValues" ctx.KnownFuncs with
        | Some (_, retTy) -> Some(WExpr.Call("Map_mapValues", wArgs, retTy))
        | None -> None
    // Map.iter — Fable emits "iterate" as the selector
    | "iterate", wArgs ->
        match Map.tryFind "Map_iter" ctx.KnownFuncs with
        | Some (_, retTy) -> Some(WExpr.Call("Map_iter", wArgs, retTy))
        | None -> None
    | _ -> None

// ─────────────────────────────────────────────────────────────────
// Set module intercept
// ─────────────────────────────────────────────────────────────────
/// Intercept standard F# `Set.*` calls that come through Fable's `setModule`
/// replacement.  Operations that receive an injected IComparer have it dropped.
let trySetInline
        (ctx: Ctx)
        (importStem: string)
        (selector: string)
        (wArgs: WExpr list) : WExpr option =
    if importStem <> "Set" then None
    else
    match selector, wArgs with
    // Set.ofList [items; _comparer] — drop injected comparer
    | "ofList", [wList; _comparer] ->
        match Map.tryFind "Set_ofList" ctx.KnownFuncs with
        | Some (_, retTy) -> Some(WExpr.Call("Set_ofList", [wList], retTy))
        | None -> None
    // Set.ofArray [items; _comparer]
    | "ofArray", [wArr; _comparer] ->
        match Map.tryFind "Set_ofList" ctx.KnownFuncs with
        | Some (_, retTy) -> Some(WExpr.Call("Set_ofList", [wArr], retTy))
        | None -> None
    // Set.empty [_comparer]
    | "empty", [_comparer] ->
        match Map.tryFind "Set_empty" ctx.KnownFuncs with
        | Some (_, retTy) -> Some(WExpr.Call("Set_empty", [], retTy))
        | None -> None
    // Set.singleton [value; _comparer]
    | "singleton", [wVal; _comparer] ->
        match Map.tryFind "Set_add" ctx.KnownFuncs, Map.tryFind "Set_empty" ctx.KnownFuncs with
        | Some (_, retTy), Some _ -> Some(WExpr.Call("Set_add", [wVal; WExpr.Call("Set_empty", [], retTy)], retTy))
        | _ -> None
    | _ -> None

// ─────────────────────────────────────────────────────────────────
// Async/Task — synchronous MVP
// ─────────────────────────────────────────────────────────────────
/// Intercept Fable's AsyncBuilder and Async LibCalls.
/// For the WasmGC synchronous MVP, Async<T> is just T — all computations
/// are evaluated immediately and synchronously.
let tryAsyncInline
        (_ctx: Ctx)
        (importStem: string)
        (selector: string)
        (wArgs: WExpr list)
        (ty: WType) : WExpr option =
    match importStem with
    | "AsyncBuilder" ->
        match selector, wArgs with
        // AsyncBuilder.return(builder, x) → x
        // Fable passes the singleton builder instance as first arg
        | "return", [_builder; wVal] -> Some wVal
        | "return", [wVal] -> Some wVal
        // AsyncBuilder.zero() → nop (unit)
        | "zero", _ -> Some WExpr.Nop
        // AsyncBuilder.delay(builder, f) → invoke f synchronously
        | "delay", [_builder; wThunk] ->
            let funcTypeIdx = _ctx.GetOrAddFuncType([], ty)
            Some(WExpr.ClosureApply(wThunk, [], funcTypeIdx, 0, 0, ty))
        | "delay", [wThunk] ->
            let funcTypeIdx = _ctx.GetOrAddFuncType([], ty)
            Some(WExpr.ClosureApply(wThunk, [], funcTypeIdx, 0, 0, ty))
        // AsyncBuilder.returnFrom(builder, comp) → comp
        | "returnFrom", [_builder; wComp] -> Some wComp
        | "returnFrom", [wComp] -> Some wComp
        // AsyncBuilder.bind(builder, comp, f) → f(comp)
        | "bind", [_builder; wComp; wFunc] ->
            let funcTypeIdx = _ctx.GetOrAddFuncType([ty], ty)
            Some(WExpr.ClosureApply(wFunc, [wComp], funcTypeIdx, 0, 0, ty))
        | "bind", [wComp; wFunc] ->
            let funcTypeIdx = _ctx.GetOrAddFuncType([ty], ty)
            Some(WExpr.ClosureApply(wFunc, [wComp], funcTypeIdx, 0, 0, ty))
        // AsyncBuilder.singleton → nop (the builder instance is not needed)
        | "singleton", _ -> Some WExpr.Nop
        // AsyncBuilder.combine(builder, a, b) → sequence a then b
        | "combine", [_builder; wA; wB] -> Some(WExpr.Sequence [wA; wB])
        | "combine", [wA; wB] -> Some(WExpr.Sequence [wA; wB])
        // All other AsyncBuilder methods — ignore builder, return last meaningful arg
        | _, args ->
            match args |> List.filter (fun a -> a <> WExpr.Nop) with
            | [] -> Some WExpr.Nop
            | xs -> Some (List.last xs)
    | "Async" ->
        match selector, wArgs with
        // Async.RunSynchronously(comp) → comp (synchronous: just eval)
        | "runSynchronously", [wComp] -> Some wComp
        | "runSynchronously", (wComp :: _) -> Some wComp
        // Async.StartImmediate(comp) → comp (synchronous: just eval, discard result)
        | "startImmediate", [wComp] -> Some(WExpr.Sequence [wComp; WExpr.Nop])
        | "startImmediate", (wComp :: _) -> Some(WExpr.Sequence [wComp; WExpr.Nop])
        // Async.ignore(comp) → comp; nop
        | "ignore", [wComp] -> Some(WExpr.Sequence [wComp; WExpr.Nop])
        // Async.map(f, comp) → f(comp)  (synchronous apply)
        | "map", [_f; wComp] -> Some wComp
        // Default: return first arg (best effort)
        | _, (first :: _) -> Some first
        | _ -> Some WExpr.Nop
    | _ -> None
