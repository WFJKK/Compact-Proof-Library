import GrossCubic.Checker

/-!
# Entry 8: every input from the path tables

Brute force on the one-head attention models of entry 6, from the path tables instead of forward
passes: the tables are computed once, and every input's test reads them. Cleared of the softmax's
denominator, an input `x` with query `q` and label `ℓ` is answered correctly if, for every other
output `j`,

    Σ_p e^{S[q, x_p, p]} y_p < 0
    y_p = (D[q, j] - D[q, ℓ]) + (O[x_p, p, j] - O[x_p, p, ℓ])

The checker bounds each term by `max(lo y_p, hi y_p)`, with `lo ≤ e^S ≤ hi` the counted language's
bounds on `exp` (at `2^-120`), so the test passes on every input the network answers correctly but
for margins below the bounds' width. The tables of differences `D[q, j] - D[q, l]` and
`O[t, p, j] - O[t, p, l]` are computed once, for every `l`; each input then costs `5 n` operations
per other output.

Gross et al.'s code evaluates inputs from such tables too (`run_model_cached` in
`gbmi/exp_max_of_n/verification/brute_force.py`, used by their importance sampling), with each
position's weight taken relative to the largest token's score at that position, which drops the
positional part of the attention; their brute-force proof runs the model on every input, which is
entry 2. Here the scores are the network's own.

The checker reads the weights' shapes and lengths (free) and refuses (count 0) unless they are the
family's.
-/

namespace PathBrute

open CompactCheck AttnClasses GrossCubic

section Checker

variable (I : Interp)

/-- The test of the input `x` with the label `ℓ`, from the tables of differences `Dd[q][ℓ][j]`
    and `Od[t][p][ℓ][j]` and the bounds `X[q][t][p]` on `exp` of the scores. -/
def test (V n : ℕ) (Dd : List (List (List I.V))) (Od : List (List (List (List I.V))))
    (X : List (List (List (I.V × I.V)))) (ℓ : ℕ) (x : Input) : I.M I.B := do
  let q := x.getD (n - 1) 0
  let ups ← (others V ℓ).mapM fun j => do
    let ts ← (List.range n).mapM fun p => do
      let y ← I.add cat (((Dd.getD q []).getD ℓ []).getD j I.zero)
        ((((Od.getD (x.getD p 0) []).getD p []).getD ℓ []).getD j I.zero)
      kup I (((X.getD q []).getD (x.getD p 0) []).getD p (I.zero, I.zero)) y
    sumL I ts
  let top ← maxL I ups
  I.lt cat top I.zero

/-- Differences within each row: `r[j] - r[l]`, for every `l` and `j`. -/
def diffs (r : List I.V) : I.M (List (List I.V)) :=
  (List.range r.length).mapM fun l => r.mapM fun v => I.sub cat v (r.getD l I.zero)

/-- The checker, for the graph `g` and the task `task`: every input, from the path tables. -/
def check (g : Graph) (task : Task) : I.M I.N := do
  let sE ← I.weightShape nE
  let sP ← I.weightShape nP
  let sQ ← I.weightShape nQ
  let sK ← I.weightShape nK
  let sV ← I.weightShape nV
  let sO ← I.weightShape nO
  let sU ← I.weightShape nU
  let sC ← I.weightShape nC
  let lE ← I.weightSize nE
  let lP ← I.weightSize nP
  let lQ ← I.weightSize nQ
  let lK ← I.weightSize nK
  let lV ← I.weightSize nV
  let lO ← I.weightSize nO
  let lU ← I.weightSize nU
  let lC ← I.weightSize nC
  let V := g.values
  let n := g.positions
  let d := sE.getD 1 0
  let h := sQ.getD 1 0
  if wellFormed V n d h [sE, sP, sQ, sK, sV, sO, sU, sC] [lE, lP, lQ, lK, lV, lO, lU, lC] then do
    let Es ← (List.range V).mapM (row I nE d)
    let Ps ← (List.range n).mapM (row I nP d)
    let c ← I.weight nC 0
    let Qc ← (List.range h).mapM fun k => do
      let w ← col I nQ d h k
      w.mapM fun v => I.muladd cat I.zero v c
    let Kc ← (List.range h).mapM (col I nK d h)
    let Vr ← (List.range d).mapM (row I nV h)
    let Oc ← (List.range d).mapM (col I nO h d)
    let Uc ← (List.range V).mapM (col I nU d V)
    let last := Ps.getD (n - 1) []
    let Eq ← Es.mapM (vadd I · last)
    let Qs ← mm I Eq Qc
    let SE ← mm I Qs (← mm I Es Kc)
    let SP ← mm I Qs (← mm I Ps Kc)
    let VOU ← mm I (← mm I Vr Oc) Uc
    let VOUc := (List.range V).map fun j => VOU.map (·.getD j I.zero)
    let EV ← mm I Es VOUc
    let PV ← mm I Ps VOUc
    let EU ← mm I Eq Uc
    let Ot ← EV.mapM fun r => PV.mapM (vadd I r)
    let Od ← Ot.mapM fun rs => rs.mapM (diffs I)
    let Dd ← EU.mapM (diffs I)
    let X ← (List.zip SE SP).mapM fun p => p.1.mapM fun s => p.2.mapM fun s' => do
      I.exp cat (← I.add cat s s')
    let vs ← (allInputs task.space).mapM fun x => test I V n Dd Od X (task.label x) x
    pure (vs.foldl (fun a b => I.nadd a (I.countB b)) I.nzero)
  else pure I.nzero

end Checker

end PathBrute
