import LinearMaxKPlans.Pieces
import LinearMaxK.Checker

/-!
# The checker of a plan, in the counted language

The checker of entry 1, with the groups replaced by the pieces of a plan. A plan is public data: a
list of pieces `⟨m, lo, hi⟩`, fixed with the checker, so the checker may branch on it.

For a piece and an output `j ≠ m`, with `D(t) = M[m, t] - M[j, t]`:

* a tail, `hi = m` (the inputs of the group whose tokens are all at least `lo`): the test of entry 1
  with the minimum taken over `[lo, m]`,

      D(m) + (k - 1) · min_{lo ≤ t ≤ m} D(t) > 0

  (`2 (m - lo) + 3` operations);
* a band, `hi < m`: with `A` the minimum of `D` over `[lo, hi]` and `B` its minimum over `[lo, m]`,

      D(m) + A + (k - 2) · B > 0

  (`2 (m - lo) + 4` operations): one token of the input is `m`, another is its smallest token, in
  `[lo, hi]`, and the other `k - 2` are in `[lo, m]`.

A piece counts its size if its tests and the guard pass. Before anything, the checker checks that
the plan is valid (`planOk`); for an invalid plan it certifies nothing.
-/

namespace LinearMaxKPlans

open CompactCheck LinearMaxK

section Checker

variable (I : Interp)

/-- The test of the piece `p` against the output `j`; `km1` holds `k - 1`, `km2` holds `k - 2`. -/
def pieceTest (cols : List (List I.V)) (km1 km2 : I.V) (p : Piece) (j : ℕ) : I.M I.B := do
  let dm ← I.sub cat (entry I cols p.m p.m) (entry I cols j p.m)
  if p.hi = p.m then do
    let mu ← minDiff I cols p.m j (List.range' p.lo (p.m - p.lo)) dm
    let v ← I.muladd cat dm km1 mu
    I.lt cat I.zero v
  else do
    let a0 ← I.sub cat (entry I cols p.m p.lo) (entry I cols j p.lo)
    let a ← minDiff I cols p.m j (List.range' (p.lo + 1) (p.hi - p.lo)) a0
    let b0 ← minDiff I cols p.m j (List.range' (p.hi + 1) (p.m - p.hi - 1)) a
    let b ← I.min cat b0 dm
    let s ← I.add cat dm a
    let v ← I.muladd cat s km2 b
    I.lt cat I.zero v

/-- The tests of the piece `p` against the outputs `js`, joined by charged gates. -/
def pieceTests (cols : List (List I.V)) (km1 km2 : I.V) (p : Piece) : List ℕ → I.M I.B
  | [] => pure I.btrue
  | j :: js =>
    if j = p.m then pieceTests cols km1 km2 p js
    else do
      let b ← pieceTest I cols km1 km2 p j
      let r ← pieceTests cols km1 km2 p js
      I.band cat b r

/-- The count of the pieces `ps`: each piece's size if its tests and the guard pass. -/
def countPieces (cols : List (List I.V)) (km1 km2 : I.V) (ok0 : I.B) (k V : ℕ) :
    List Piece → I.M I.N
  | [] => pure I.nzero
  | p :: ps => do
    let b ← pieceTests I cols km1 km2 p (List.range V)
    let bb ← I.band cat ok0 b
    let n ← countPieces cols km1 km2 ok0 k V ps
    pure (I.nadd (I.nscale (p.size k) bb) n)

/-- The checker of the plan `plan`, for the graph `g` and the task `task`. -/
def check (plan : List Piece) (g : Graph) (task : Task) : I.M I.N := do
  let sE ← I.weightShape nE
  let sL ← I.weightShape nL
  let sU ← I.weightShape nU
  let d := sE.headD 0
  if sE == [d, g.values] && sL == [d, d] && sU == [g.values, d] && planOk g.values plan then do
    let ok0 ← I.single g task (List.replicate g.positions (g.values - 1))
    let cols ← columns I g.values d (List.range g.values)
    let km1 ← I.lit cat (g.positions - 1)
    let km2 ← I.lit cat (g.positions - 2)
    countPieces I cols km1 km2 ok0 g.positions g.values plan
  else pure I.nzero

end Checker

end LinearMaxKPlans
