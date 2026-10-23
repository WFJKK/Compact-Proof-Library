import LinearMaxK.Family

/-!
# The checker: the exact group method, in the counted language

A checker of the counted language (version 4, `CompactCheck/CountedOps.lean`): it is written
for every interpreter `I`, touches the network's numbers only through `I`'s charged operations,
and never branches on a truth value. Its only branches are on public structure: the graph's sizes
and the weights' shapes.

The method, for a network of the family with `k` positions, `V` tokens and width `d`:

1. One forward pass on the input `(V - 1, ..., V - 1)` (`I.single`). The counted language cannot
   read a tensor's length, and a forward pass that succeeds shows the weights have the sizes their
   shapes say. Its result gates every count, so it costs one gate per group.
2. Every column of `M = U L E`: column `t` reads column `t` of `E` (free), then applies `L` (`d^2`
   multiply-adds) and `U` (`V d`).
3. For every group `m` (inputs whose largest token is `m`) and every other output `j`, with
   `D(t) = M[m, t] - M[j, t]`, the test

       D(m) + (k - 1) · min over t ≤ m of D(t) > 0

   (`m + 1` subtractions, `m` minima, a multiply-add and a comparison). The worst input of the
   group against `j` puts `m` at one position and the minimiser at the other `k - 1`, so the test is
   exact: it passes for every `j` iff every input of the group is answered correctly
   (`Exact.lean`).
4. The count: the sum over the groups that pass of their sizes, `(m + 1)^k - m^k`.

Nothing here depends on the weights' values except through `I`, so the bill is a function of
`(k, V, d)` alone (`runs_check` in `Runs.lean`, `bill_eq` and `check_bill` in `Exact.lean`).
-/

namespace LinearMaxK

open CompactCheck Common

section Checker

variable (I : Interp)

/-- The category of every charge but the guard's. -/
def cat : String := "m"

/-- Entries `is` of the weight `name`. -/
def readW (name : String) : List ℕ → I.M (List I.V)
  | [] => pure []
  | i :: is => do
    let q ← I.weight name i
    let qs ← readW name is
    pure (q :: qs)

/-- `acc + Σ x_i y_i`, one multiply-add per term. -/
def dot : List I.V → List I.V → I.V → I.M I.V
  | [], _, acc => pure acc
  | _ :: _, [], acc => pure acc
  | x :: xs, y :: ys, acc => do
    let acc' ← I.muladd cat acc x y
    dot xs ys acc'

/-- `W v` on the rows `rs` of the weight `name`, which has `n` columns. -/
def matVec (name : String) (n : ℕ) (v : List I.V) : List ℕ → I.M (List I.V)
  | [] => pure []
  | r :: rs => do
    let row ← readW I name ((List.range n).map fun i => r * n + i)
    let q ← dot I row v I.zero
    let qs ← matVec name n v rs
    pure (q :: qs)

/-- Column `t` of `M = U L E`, as a list over the outputs. -/
def column (V d t : ℕ) : I.M (List I.V) := do
  let e ← readW I nE ((List.range d).map fun b => b * V + t)
  let h ← matVec I nL d e (List.range d)
  matVec I nU d h (List.range V)

/-- The columns `ts` of `M`. -/
def columns (V d : ℕ) : List ℕ → I.M (List (List I.V))
  | [] => pure []
  | t :: ts => do
    let c ← column I V d t
    let cs ← columns V d ts
    pure (c :: cs)

/-- `M[j, t]`, from the columns. -/
def entry (cols : List (List I.V)) (j t : ℕ) : I.V := (cols.getD t []).getD j I.zero

/-- `min (acc, D(t) for t in ts)`, with `D(t) = M[m, t] - M[j, t]`. -/
def minDiff (cols : List (List I.V)) (m j : ℕ) : List ℕ → I.V → I.M I.V
  | [], acc => pure acc
  | t :: ts, acc => do
    let dt ← I.sub cat (entry I cols m t) (entry I cols j t)
    let acc' ← I.min cat acc dt
    minDiff cols m j ts acc'

/-- The test of the group `m` against the output `j`: `D(m) + (k - 1) min_{t ≤ m} D(t) > 0`, where
    `km1` holds `k - 1`. -/
def pairTest (cols : List (List I.V)) (km1 : I.V) (m j : ℕ) : I.M I.B := do
  let dm ← I.sub cat (entry I cols m m) (entry I cols j m)
  let mu ← minDiff I cols m j (List.range m) dm
  let v ← I.muladd cat dm km1 mu
  I.lt cat I.zero v

/-- The tests of the group `m` against the outputs `js`, joined by charged gates. -/
def groupTest (cols : List (List I.V)) (km1 : I.V) (m : ℕ) : List ℕ → I.M I.B
  | [] => pure I.btrue
  | j :: js =>
    if j = m then groupTest cols km1 m js
    else do
      let b ← pairTest I cols km1 m j
      let r ← groupTest cols km1 m js
      I.band cat b r

/-- The count of the groups `ms`: each group's size if its tests and the guard pass. -/
def countGroups (cols : List (List I.V)) (km1 : I.V) (ok0 : I.B) (k V : ℕ) :
    List ℕ → I.M I.N
  | [] => pure I.nzero
  | m :: ms => do
    let b ← groupTest I cols km1 m (List.range V)
    let bb ← I.band cat ok0 b
    let n ← countGroups cols km1 ok0 k V ms
    pure (I.nadd (I.nscale (Nat.pow (m + 1) k - Nat.pow m k) bb) n)

/-- The checker, for the graph `g` and the task `task`. -/
def check (g : Graph) (task : Task) : I.M I.N := do
  let sE ← I.weightShape nE
  let sL ← I.weightShape nL
  let sU ← I.weightShape nU
  let d := sE.headD 0
  if sE == [d, g.values] && sL == [d, d] && sU == [g.values, d] then do
    let ok0 ← I.single g task (List.replicate g.positions (g.values - 1))
    let cols ← columns I g.values d (List.range g.values)
    let km1 ← I.lit cat (g.positions - 1)
    countGroups I cols km1 ok0 g.positions g.values (List.range g.values)
  else pure I.nzero

end Checker

end LinearMaxK
