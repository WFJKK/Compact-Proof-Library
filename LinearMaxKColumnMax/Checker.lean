import LinearMaxK.Checker
import Symmetry.Sorted

/-!
# Entry 5: column maxima, in the counted language

The improvement an agent found in the open lane (pilot 2, round 4, `Full64`, for one network with
`k = 2`), here for every `k`, `V` and `d`. Entry 1 tests a group of inputs against every other
output `j`, one test per `j`. Here each column `t` of `M = U L E` is summarised once:

* `mx_t = max_{j ≠ t} M[j, t]`, its largest entry off the diagonal;
* `top_t = max (mx_t, M[t, t])`, its largest entry;
* `dm_t = M[t, t] - mx_t`, the margin of its diagonal.

No output gains more from token `t` than `top_t`, and no output other than `t` more than `mx_t`. So
one test of the summaries bounds the margins against all `j` at once.

A plan is a list of terms. Each term certifies a set of inputs closed under reordering, given as a
list of sorted inputs (`Term.inputs`), and counts their reorderings (`Term.size`). For inputs
whose largest token is `m`:

* `diag m`, the input `(m, ..., m)`: `0 < dm_m`.
* `box m lo hi dg`, the inputs whose other tokens all lie in `[lo, hi]`, with `hi < m`, and
  `(m, ..., m)` too if `dg`. With the loss `ℓ(t) = top_t - M[m, t]`, the test is

      (k - 1) · max_{lo ≤ t ≤ hi} ℓ(t) < dm_m.

* `refined x`, the reorderings of the sorted input `x`, with `c` copies of `m`. Against every `j`
  that is not a token of `x`,

      Σ_{t ∈ x, t ≠ m} (mx_t - M[m, t]) < c · dm_m,

  and against each other token `j` of `x`, the exact margin,

      Σ_{t ∈ x, t ≠ m} (M[j, t] - M[m, t]) < c · (M[m, m] - M[j, m]).

* `exact x`, the reorderings of `x`: its logits, the sum of the columns of its tokens, and one
  comparison of logit `m` with the largest of the others.

For `k = 2` these are `Full64`'s four tests: `diag m`; `pair a m wd` is `box m a a wd`;
`rpair a m` is `refined [a, m]`; `exact a m` is `exact [a, m]`.

The checker reads the shapes and lengths of the weights (free) and checks the plan (free, it is
public data). Then it computes the columns, their summaries and the tests.
-/

namespace LinearMaxKColumnMax

open CompactCheck LinearMaxK

/-! ## Plans -/

/-- A term of a plan. -/
inductive Term where
  /-- The input `(m, ..., m)`. -/
  | diag (m : ℕ)
  /-- The inputs whose largest token is `m` and whose other tokens lie in `[lo, hi]`, at least one
      of them; and `(m, ..., m)` if `dg`. -/
  | box (m lo hi : ℕ) (dg : Bool)
  /-- The reorderings of the sorted input `x`, by the refined test. -/
  | refined (x : Input)
  /-- The reorderings of the sorted input `x`, by its logits. -/
  | exact (x : Input)

/-- The sorted inputs of a term, one for each class of reorderings it certifies. A box's are
    `y ++ (m, ..., m)` with `i + 1` copies of `m` and `y` sorted in `[lo, hi]`. -/
def Term.inputs (k : ℕ) : Term → List Input
  | .diag m => [List.replicate k m]
  | .box m lo hi dg =>
    (List.range (if dg then k else k - 1)).flatMap fun i =>
      (Symmetry.sortedFrom (hi + 1) (k - 1 - i) lo).map fun y => y ++ List.replicate (i + 1) m
  | .refined x => [x]
  | .exact x => [x]

/-- The number of inputs a term certifies: the reorderings of its sorted inputs. -/
def Term.size (V k : ℕ) (t : Term) : ℕ :=
  (t.inputs k).foldr (fun x acc => Nat.add (Symmetry.mult V k x) acc) 0

/-- Nondecreasing. -/
def sortedB : List ℕ → Bool
  | [] => true
  | a :: l => l.all (fun b => Nat.ble a b) && sortedB l

/-- A sorted input of `k` tokens in `[0, V)`. -/
def validInput (V k : ℕ) (x : Input) : Bool :=
  sortedB x && Nat.beq x.length k && x.all fun t => Nat.blt t V

/-- No input twice. -/
def nodupB : List Input → Bool
  | [] => true
  | x :: xs => !(xs.contains x) && nodupB xs

/-- A box has `lo ≤ hi < m < V`, a diagonal term `m < V`. -/
def Term.valid (V : ℕ) : Term → Bool
  | .diag m => Nat.blt m V
  | .box m lo hi _ => Nat.ble lo hi && Nat.blt hi m && Nat.blt m V
  | .refined _ => true
  | .exact _ => true

/-- A valid plan: valid terms, whose sorted inputs are sorted inputs of the task, none in two terms
    (so no input is counted twice). -/
def planOk (V k : ℕ) (plan : List Term) : Bool :=
  plan.all (Term.valid V) && (plan.flatMap (Term.inputs k)).all (validInput V k) &&
    nodupB (plan.flatMap (Term.inputs k))

/-! ## The checker -/

/-- The summaries of a column. -/
structure Summary (I : Interp) where
  /-- The largest entry off the diagonal. -/
  mx : I.V
  /-- The largest entry. -/
  top : I.V
  /-- The diagonal entry less `mx`. -/
  dm : I.V

section Checker

variable (I : Interp)

/-- The largest of `vs`, or zero if there are none. -/
def maxOf : List I.V → I.M I.V
  | [] => pure I.zero
  | v :: vs => vs.foldlM (I.max cat) v

/-- The tokens other than `t`. -/
def others (V t : ℕ) : List ℕ := (List.range V).filter fun j => j != t

/-- The summaries of column `t`. -/
def summary (cols : List (List I.V)) (V t : ℕ) : I.M (Summary I) := do
  let mx ← maxOf I ((others V t).map fun j => entry I cols j t)
  let top ← I.max cat mx (entry I cols t t)
  let dm ← I.sub cat (entry I cols t t) mx
  pure ⟨mx, top, dm⟩

/-- The summaries of the columns `ts`. -/
def summaries (cols : List (List I.V)) (V : ℕ) (ts : List ℕ) : I.M (List (Summary I)) :=
  ts.mapM (summary I cols V)

/-- The summaries of column `t`, from the list. -/
def sm (ss : List (Summary I)) (t : ℕ) : Summary I := ss.getD t ⟨I.zero, I.zero, I.zero⟩

/-- `v + v + ... + v`, `c` times. -/
def rep (v : I.V) (c : ℕ) : I.M I.V :=
  if c = 0 then pure I.zero else (List.range (c - 1)).foldlM (fun s _ => I.add cat s v) v

/-- `Σ_{t ∈ ts} (f t - g t)`. -/
def sumDiff (f g : ℕ → I.V) : List ℕ → I.M I.V
  | [] => pure I.zero
  | t :: ts => do
    let e ← I.sub cat (f t) (g t)
    ts.foldlM (fun acc u => do
      let e' ← I.sub cat (f u) (g u)
      I.add cat acc e') e

/-- The test of a box: `(k - 1) · max_{lo ≤ t ≤ hi} ℓ(t) < dm_m`, with the loss
    `ℓ(t) = top_t - M[m, t]`. -/
def boxTest (cols : List (List I.V)) (ss : List (Summary I)) (k m lo hi : ℕ) : I.M I.B := do
  let l ← I.sub cat (sm I ss lo).top (entry I cols m lo)
  let a ← (List.range' (lo + 1) (hi - lo)).foldlM (fun a t => do
    let l' ← I.sub cat (sm I ss t).top (entry I cols m t)
    I.max cat a l') l
  let s ← rep I a (k - 1)
  I.lt cat s (sm I ss m).dm

/-- The refined test of the sorted input `x`, whose largest token `m` it holds `c` times and whose
    other tokens are `os`: against the outputs that are not tokens of `x`, by the summaries; against
    each other token `j` of `x`, exactly,
    `Σ_{t ∈ os} (M[j, t] - M[m, t]) < c · (M[m, m] - M[j, m])`. -/
def refinedTest (cols : List (List I.V)) (ss : List (Summary I)) (x : Input) : I.M I.B := do
  let m := x.foldl max 0
  let os := x.filter fun t => t != m
  let c := (x.filter fun t => t == m).length
  let l ← sumDiff I (fun t => (sm I ss t).mx) (fun t => entry I cols m t) os
  let r ← rep I (sm I ss m).dm c
  let b ← I.lt cat l r
  ((List.range m).filter fun j => x.contains j).foldlM (fun b j => do
    let lj ← sumDiff I (fun t => entry I cols j t) (fun t => entry I cols m t) os
    let e ← I.sub cat (entry I cols m m) (entry I cols j m)
    let rj ← rep I e c
    let bj ← I.lt cat lj rj
    I.band cat b bj) b

/-- Logit `j` of the input `x`: the sum of the entries `(j, t)` over its tokens `t`. -/
def logit (cols : List (List I.V)) (x : Input) (j : ℕ) : I.M I.V :=
  x.tail.foldlM (fun a t => I.add cat a (entry I cols j t)) (entry I cols j (x.headD 0))

/-- The largest of `f j` over `js`, or zero if there are none. -/
def maxOver (f : ℕ → I.M I.V) : List ℕ → I.M I.V
  | [] => pure I.zero
  | j :: js => do
    let s ← f j
    js.foldlM (fun a j' => do
      let s' ← f j'
      I.max cat a s') s

/-- The exact test of the input `x`: logit `m` must beat the largest of the others. -/
def exactTest (cols : List (List I.V)) (V : ℕ) (x : Input) : I.M I.B := do
  let mo ← maxOver I (logit I cols x) (others V (x.foldl max 0))
  let s ← logit I cols x (x.foldl max 0)
  I.lt cat mo s

/-- The test of a term. -/
def termTest (cols : List (List I.V)) (ss : List (Summary I)) (V k : ℕ) : Term → I.M I.B
  | .diag m => I.lt cat I.zero (sm I ss m).dm
  | .box m lo hi _ => boxTest I cols ss k m lo hi
  | .refined x => refinedTest I cols ss x
  | .exact x => exactTest I cols V x

/-- The count of the plan: each term's size if its test passes. -/
def countTerms (cols : List (List I.V)) (ss : List (Summary I)) (V k : ℕ) (plan : List Term) :
    I.M I.N :=
  plan.foldlM (fun n t => do
    let b ← termTest I cols ss V k t
    pure (I.nadd n (I.nscale (t.size V k) b))) I.nzero

/-- The checker of the plan `plan`, for the graph `g` and the task `task`. -/
def check (plan : List Term) (g : Graph) (_task : Task) : I.M I.N := do
  let sE ← I.weightShape nE
  let sL ← I.weightShape nL
  let sU ← I.weightShape nU
  let lE ← I.weightSize nE
  let lL ← I.weightSize nL
  let lU ← I.weightSize nU
  let d := sE.headD 0
  if wellFormed g.values d sE sL sU lE lL lU && planOk g.values g.positions plan then do
    let cols ← columns I g.values d (List.range g.values)
    let ss ← summaries I cols g.values (List.range g.values)
    countTerms I cols ss g.values g.positions plan
  else pure I.nzero

end Checker

end LinearMaxKColumnMax
