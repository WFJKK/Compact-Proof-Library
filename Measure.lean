import CompactCheck.Json
import LinearMaxK.Exact

/-!
# `measure`: the checker on exported networks, by compiled evaluation

    lake exe measure <network.json> ...

For each network file (`scripts/export_network.py` of the Lean repository), runs the checker of
`LinearMaxK` with the counting interpreter, compiled, and prints one JSON line: the count, the bill,
`bill k V d` from the cost formula, and `E` (the number of weight entries, which the open lane
charges once as `extract`). This is a measurement, not a kernel check: the kernel-checked instances
are in `instances/`.
-/

open CompactCheck LinearMaxK Lean

def measureOne (path : String) : IO Unit := do
  let j ← readJson path
  match parseNetwork j with
  | .error e => IO.println (Json.mkObj [("file", Json.str path), ("error", Json.str e)]).compress
  | .ok net =>
    let g := net.graph
    let d := ((List.lookup nE net.weights).map fun t => t.shape.headD 0).getD 0
    let e := (net.weights.map fun p => p.2.data.size).sum
    let r := CostM.billed (check Interp.counting g (maxTask g.positions g.values))
      ⟨net.weights, #[]⟩
    let (count, bill') := r.getD (0, 0)
    IO.println (Json.mkObj [("network", Json.str net.network), ("family", toJson (IsLinearMaxK g)),
      ("k", toJson g.positions), ("V", toJson g.values), ("d", toJson d),
      ("count", toJson count), ("bill", toJson bill'),
      ("bill_formula", toJson (bill g.positions g.values d)),
      ("E", toJson e), ("length", toJson (bill' + e))]).compress

def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    IO.eprintln "usage: measure <network.json> ..."
    return 2
  for p in args do measureOne p
  return 0
