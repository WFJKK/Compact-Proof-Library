import CompactCheck.Json
import GrossCubic.Check
import PathBrute.Runs

/-!
# `measure_gross`: entries 7 and 8 on exported attention networks, by compiled evaluation

    lake exe measure_gross <network.json> ...
    lake exe measure_gross --brute <network.json> ...

For each network file (`scripts/export_network.py` of the Lean repository, an attention network of
the pipeline), runs the checker of `GrossCubic` (the cubic proof of Gross et al.) with the counting
interpreter, compiled, for the label the file names (`max` or `min`), and prints one JSON line: the
count, the bill, `bill V n d h` from the cost formula, and `E` (the number of weight entries; the
open lane charges them once as `extract`, without `#const0`'s single entry, which `E` here
includes).

With `--brute`, it runs instead the checker of `PathBrute` (entry 8, every input from the path
tables), with its cost formula `PathBrute.bill`.

This is a measurement, not a kernel check: the kernel-checked instances are in `instances/`.
-/

open CompactCheck GrossCubic Lean

def measureOne (brute : Bool) (path : String) : IO Unit := do
  let j ← readJson path
  match parseNetwork j with
  | .error e => IO.println (Json.mkObj [("file", Json.str path), ("error", Json.str e)]).compress
  | .ok net =>
    let g := net.graph
    let mx := net.task.name == "max"
    let d := ((List.lookup AttnClasses.nE net.weights).map fun t => t.shape.getD 1 0).getD 0
    let h := ((List.lookup AttnClasses.nQ net.weights).map fun t => t.shape.getD 1 0).getD 0
    let e := (net.weights.map fun p => p.2.data.size).sum
    let r := if brute then
        CostM.billed (PathBrute.check Interp.counting g net.task) ⟨net.weights, #[]⟩
      else CostM.billed (check Interp.counting mx g net.task) ⟨net.weights, #[]⟩
    let formula := if brute then PathBrute.bill g.values g.positions d h
      else bill g.values g.positions d h
    let (count, bill') := r.getD (0, 0)
    IO.println (Json.mkObj [("network", Json.str net.network), ("task", Json.str net.task.name),
      ("n", toJson g.positions), ("V", toJson g.values), ("d", toJson d), ("h", toJson h),
      ("ran", toJson r.isSome), ("count", toJson count), ("bill", toJson bill'),
      ("bill_formula", toJson formula), ("entry", toJson (if brute then 8 else 7)),
      ("E", toJson e), ("length", toJson (bill' + e))]).compress

def main (args : List String) : IO UInt32 := do
  match args with
  | [] | ["--brute"] =>
    IO.eprintln "usage: measure_gross [--brute] <network.json> ..."
    return 2
  | "--brute" :: ps => for p in ps do measureOne true p
  | ps => for p in ps do measureOne false p
  return 0
