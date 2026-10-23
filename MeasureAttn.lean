import CompactCheck.Json
import AttnClasses.Check
import BruteForce.General

/-!
# `measure_attn`: entry 6 on exported attention networks, by compiled evaluation

    lake exe measure_attn <network.json> ...
    lake exe measure_attn --bf <network.json> ...

For each network file (`scripts/export_network.py` of the Lean repository, an attention network of
the pipeline), runs the checker of `AttnClasses` with the counting interpreter, compiled, for the
label the file names (`max` or `min`), and prints one JSON line: the count, the bill,
`bill V n d h` from the cost formula, and `E` (the number of weight entries; the open lane charges
them once as `extract`, without `#const0`'s single entry, which `E` here includes).

With `--bf`, it runs instead the general single rule of entry 2 (`BruteForce.gsingleOn`) on one
input, the input of zeros, and prints its charge and the charge formula of `BruteForce/General.lean`,
`2 n d h + 2 d h + 4 n h + 2 n d + 2 n + d + V d + V - 1` (the charge depends only on the shapes,
so it is the same for every input).

This is a measurement, not a kernel check: the kernel-checked instances are in `instances/`.
-/

open CompactCheck AttnClasses Lean

def measureOne (path : String) : IO Unit := do
  let j ← readJson path
  match parseNetwork j with
  | .error e => IO.println (Json.mkObj [("file", Json.str path), ("error", Json.str e)]).compress
  | .ok net =>
    let g := net.graph
    let mx := net.task.name == "max"
    let d := ((List.lookup nE net.weights).map fun t => t.shape.getD 1 0).getD 0
    let h := ((List.lookup nQ net.weights).map fun t => t.shape.getD 1 0).getD 0
    let e := (net.weights.map fun p => p.2.data.size).sum
    let r := CostM.billed (check Interp.counting mx g net.task) ⟨net.weights, #[]⟩
    let (count, bill') := r.getD (0, 0)
    IO.println (Json.mkObj [("network", Json.str net.network), ("task", Json.str net.task.name),
      ("n", toJson g.positions), ("V", toJson g.values), ("d", toJson d), ("h", toJson h),
      ("ran", toJson r.isSome), ("count", toJson count), ("bill", toJson bill'),
      ("bill_formula", toJson (bill g.values g.positions d h)),
      ("E", toJson e), ("length", toJson (bill' + e))]).compress

/-- Entry 2's charge for one forward pass, and the formula. -/
def measureBF (path : String) : IO Unit := do
  let j ← readJson path
  match parseNetwork j with
  | .error e => IO.println (Json.mkObj [("file", Json.str path), ("error", Json.str e)]).compress
  | .ok net =>
    let g := net.graph
    let n := g.positions
    let V := g.values
    let d := ((List.lookup nE net.weights).map fun t => t.shape.getD 1 0).getD 0
    let h := ((List.lookup nQ net.weights).map fun t => t.shape.getD 1 0).getD 0
    let r := BruteForce.gsingleOn net.weights g net.task (List.replicate n 0)
    let formula := 2 * n * d * h + 2 * d * h + 4 * n * h + 2 * n * d + 2 * n + d + V * d + V - 1
    IO.println (Json.mkObj [("network", Json.str net.network), ("n", toJson n), ("V", toJson V),
      ("d", toJson d), ("h", toJson h), ("ran", toJson r.isSome),
      ("charge", toJson ((r.map (·.2)).getD 0)), ("charge_formula", toJson formula)]).compress

def main (args : List String) : IO UInt32 := do
  match args with
  | [] | ["--bf"] =>
    IO.eprintln "usage: measure_attn [--bf] <network.json> ..."
    return 2
  | "--bf" :: ps => for p in ps do measureBF p
  | ps => for p in ps do measureOne p
  return 0
