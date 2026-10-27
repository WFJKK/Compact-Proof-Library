import CompactCheck.Json
import GrossSub.Checker

/-!
# `measure_sub`: entry 9 on exported attention networks, by compiled evaluation

    lake exe measure_sub <network.json> <plan.json> ...

For a network file and plan files (`scripts/gross_sub_plan.py`: one of Gross et al.'s
configurations, its method codes `err` and `eu`, the plan `gaps` by ranks, and the certificate),
runs the checker of `GrossSub` with the counting interpreter, compiled, and prints one JSON line per
plan: the count, the bill, and the length as the open lane scores it: the bill, `E` (the number of
weight entries, without those of the constants `#const...`, which the open lane does not charge),
and the certificate's size.

This is a measurement, not a kernel check: the kernel-checked instances are in `instances/`.
-/

open CompactCheck GrossSub Lean

def natOf (j : Json) (k : String) : Nat := (j.getObjValAs? Nat k).toOption.getD 0

def gapsOf (j : Json) : Array (Array (Array Nat)) :=
  (j.getObjValAs? (Array (Array (Array Nat))) "gaps").toOption.getD #[]

def certOf (j : Json) : Except String (Array Rat) := do
  let .arr xs ← j.getObjVal? "cert" | throw "cert must be a list"
  xs.mapM parseNumber

def measureOne (net : NetworkFile) (path : String) : IO Unit := do
  let pj ← readJson path
  let g := net.graph
  let mx := net.task.name == "max"
  let d := ((List.lookup AttnClasses.nE net.weights).map fun t => t.shape.getD 1 0).getD 0
  let h := ((List.lookup AttnClasses.nQ net.weights).map fun t => t.shape.getD 1 0).getD 0
  let e := ((net.weights.filter fun p => !p.1.startsWith "#const").map fun p => p.2.data.size).sum
  match certOf pj with
  | .error err =>
    IO.println (Json.mkObj [("plan", Json.str path), ("error", Json.str err)]).compress
  | .ok cert =>
    let gs := gapsOf pj
    let gap : ℕ → ℕ → ℕ → ℕ := fun rq lam c => ((gs.getD rq #[]).getD lam #[]).getD c 1
    let err := natOf pj "err"
    let eu := natOf pj "eu"
    let t0 ← IO.monoMsNow
    let r := CostM.billed (check Interp.counting mx err eu gap g net.task) ⟨net.weights, cert⟩
    let (count, bill') := r.getD (0, 0)
    let t1 ← IO.monoMsNow
    IO.println (Json.mkObj [("network", Json.str net.network),
      ("config", (pj.getObjVal? "config").toOption.getD Json.null),
      ("task", Json.str net.task.name),
      ("n", toJson g.positions), ("V", toJson g.values), ("d", toJson d), ("h", toJson h),
      ("err", toJson err), ("eu", toJson eu), ("ran", toJson r.isSome), ("count", toJson count),
      ("bill", toJson bill'), ("E", toJson e), ("read", toJson cert.size),
      ("length", toJson (bill' + e + cert.size)),
      ("ms", toJson (t1 - t0))]).compress

def main (args : List String) : IO UInt32 := do
  match args with
  | netPath :: plans@(_ :: _) =>
    let j ← readJson netPath
    match parseNetwork j with
    | .error e => IO.eprintln s!"{netPath}: {e}"; return 1
    | .ok net => for p in plans do measureOne net p
    return 0
  | _ =>
    IO.eprintln "usage: measure_sub <network.json> <plan.json> ..."
    return 2
