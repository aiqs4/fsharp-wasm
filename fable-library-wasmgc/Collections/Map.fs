/// fable-library-wasmgc — Map collection.
/// Written in pure F# — compiled by the WasmGC Fable backend.
/// This is NOT a hand-crafted WasmIR helper inside the compiler.
/// Key type: int (BST by integer comparison).
module MapModule

// ─── Data type ───────────────────────────────────────────────────────────────
// Simple, unbalanced BST — correct semantics.
// Represented as a discriminated union; compiled to a WasmGC struct hierarchy
// by ClassDeclaration handling in Fable2WasmGc.processDecl.

type MapNode =
    | Empty
    | Node of int * int * MapNode * MapNode
    //         key  value  left     right

// ─── Public API ──────────────────────────────────────────────────────────────

/// Empty map — always returns the Empty node.
let empty () : MapNode = Empty

/// True when the map has no entries.
let isEmpty (tree: MapNode) : bool =
    match tree with
    | Empty -> true
    | _ -> false

/// Insert or replace key→value.  O(depth).
let rec add (key: int) (value: int) (tree: MapNode) : MapNode =
    match tree with
    | Empty -> Node(key, value, Empty, Empty)
    | Node(k, v, l, r) ->
        if key < k then Node(k, v, add key value l, r)
        elif key > k then Node(k, v, l, add key value r)
        else Node(key, value, l, r)   // replace

/// Look up a key.  Returns None when absent.
let rec tryFind (key: int) (tree: MapNode) : int option =
    match tree with
    | Empty -> None
    | Node(k, v, l, r) ->
        if key < k then tryFind key l
        elif key > k then tryFind key r
        else Some v

/// Total number of nodes (entries).
let rec count (tree: MapNode) : int =
    match tree with
    | Empty -> 0
    | Node(_, _, l, r) -> 1 + count l + count r

/// True when key is present.
let rec containsKey (key: int) (tree: MapNode) : bool =
    match tree with
    | Empty -> false
    | Node(k, _, l, r) ->
        if key < k then containsKey key l
        elif key > k then containsKey key r
        else true

/// Return value for key; raises on missing key.
let find (key: int) (tree: MapNode) : int =
    match tryFind key tree with
    | Some v -> v
    | None   -> failwith "Key not found"

/// Helper: merge two subtrees by inserting all elements of source into target.
let rec private mergeInto (source: MapNode) (target: MapNode) : MapNode =
    match source with
    | Empty -> target
    | Node(sk, sv, sl, sr) ->
        mergeInto sr (mergeInto sl (add sk sv target))

/// Remove a key from the map by rebuilding the path without it.
let rec remove (key: int) (tree: MapNode) : MapNode =
    match tree with
    | Empty -> Empty
    | Node(k, v, l, r) ->
        if key < k then Node(k, v, remove key l, r)
        elif key > k then Node(k, v, l, remove key r)
        else mergeInto r l

/// Convert to a list of (key, value) pairs in ascending key order.
let rec private toListAcc (acc: (int * int) list) (node: MapNode) : (int * int) list =
    match node with
    | Empty -> acc
    | Node(k, v, l, r) -> toListAcc ((k, v) :: toListAcc acc r) l

let toList (node: MapNode) : (int * int) list = toListAcc [] node

/// Build a map from a list of (key, value) pairs.
/// The IComparer argument injected by Fable is dropped at the call site in
/// tryMapInline (WasmGcMathMap.fs); this function receives only the list.
let rec private ofListAcc (acc: MapNode) (pairs: (int * int) list) : MapNode =
    match pairs with
    | [] -> acc
    | (k, v) :: rest -> ofListAcc (add k v acc) rest

let ofList (pairs: (int * int) list) : MapNode = ofListAcc Empty pairs
