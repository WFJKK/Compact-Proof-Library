import LinearMaxKPlans.Checker
import LinearMaxK.Runs

/-!
# What the checker of a plan computes, and what it costs

As in entry 1: each function of the checker, run by the counting interpreter on well-formed weights,
as a `Runs`, with its value in terms of `M = U L E` and its exact number of operations. Together
they give the checker's count and its bill (`runs_check`).
-/

namespace LinearMaxKPlans

open CompactCheck Common LinearMaxK

section Tests

variable (tE tL tU : Tensor ℚ) (V d : ℕ)

/-- `min D(t)` over `[lo, m]`, as the checker folds it for a tail. -/
def muTail (m j lo : ℕ) : ℚ :=
  (List.range' lo (m - lo)).foldl (fun a t => min a (Dif tE tL tU V d m j t))
    (Dif tE tL tU V d m j m)

/-- `A`: the minimum of `D` over `[lo, hi]`. -/
def minA (m j lo hi : ℕ) : ℚ :=
  (List.range' (lo + 1) (hi - lo)).foldl (fun a t => min a (Dif tE tL tU V d m j t))
    (Dif tE tL tU V d m j lo)

/-- `B`: the minimum of `D` over `[lo, m]`, for a band (`hi < m`). -/
def minB (m j lo hi : ℕ) : ℚ :=
  min ((List.range' (hi + 1) (m - hi - 1)).foldl (fun a t => min a (Dif tE tL tU V d m j t))
    (minA tE tL tU V d m j lo hi)) (Dif tE tL tU V d m j m)

/-- The test of the piece `p` against the output `j`. -/
def pieceOkPair (k : ℕ) (p : Piece) (j : ℕ) : Bool :=
  if p.hi = p.m then
    decide (0 < Dif tE tL tU V d p.m j p.m + ((k - 1 : ℕ) : ℚ) * muTail tE tL tU V d p.m j p.lo)
  else
    decide (0 < (Dif tE tL tU V d p.m j p.m + minA tE tL tU V d p.m j p.lo p.hi) +
      ((k - 2 : ℕ) : ℚ) * minB tE tL tU V d p.m j p.lo p.hi)

/-- The tests of the piece `p` against every other output. -/
def pieceOk (k : ℕ) (p : Piece) : Bool :=
  (List.range V).all fun j => decide (j = p.m) || pieceOkPair tE tL tU V d k p j

end Tests

/-- The operations of one test of the piece `p`. -/
def pairCost (p : Piece) : ℕ := if p.hi = p.m then 2 * (p.m - p.lo) + 3 else 2 * (p.m - p.lo) + 4

/-- The bill of the plan: the guard's forward pass, the columns, the literals `k - 1` and `k - 2`,
    and for each piece its tests, a gate per test, and a gate with the guard. -/
def billPlan (k V d : ℕ) (plan : List Piece) : ℕ :=
  (k * d + d * d + d * V + (V - 1)) + V * (d * d + V * d) + 2 +
    (plan.map fun p => (V - 1) * (pairCost p + 1) + 1).sum

section

variable {env : Env} {V d : ℕ} {tE tL tU : Tensor ℚ}

theorem runs_add (cat : String) (a b : Q) : Runs (CostM.qadd cat a b) env ⟨a.val + b.val⟩ 1 :=
  fun c => ⟨c.add cat 1, rfl, Cost.total_add _ _ _⟩

theorem runs_pieceTest {k : ℕ} {p : Piece} (hv : p.valid V = true) {j : ℕ} (hj : j < V) :
    Runs (pieceTest K (colsQ tE tL tU V d) ⟨((k - 1 : ℕ) : ℚ)⟩ ⟨((k - 2 : ℕ) : ℚ)⟩ p j) env
      (pieceOkPair tE tL tU V d k p j) (pairCost p) := by
  simp only [Piece.valid, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hv
  obtain ⟨⟨hlh, hhm⟩, hmV⟩ := hv
  have hlo : p.lo < V := by omega
  by_cases hh : p.hi = p.m
  · simp only [pieceTest, hh, ↓reduceIte, Interp.counting_bind, entry_colsQ hmV hmV,
      entry_colsQ hj hmV]
    exact Runs.bind' (runs_sub cat _ _)
      (Runs.bind' (runs_minDiff hmV hj _ _ fun t ht => by
          simp only [List.mem_range'_1] at ht; omega)
        (Runs.bind' (runs_muladd cat _ _ _) (runs_lt cat _ _) rfl rfl) rfl rfl)
      (by simp only [pieceOkPair, hh, ↓reduceIte, muTail, Dif]
          exact decide_eq_decide.mpr Iff.rfl)
      (by simp [pairCost, hh]; omega)
  · simp only [pieceTest, hh, ↓reduceIte, Interp.counting_bind, entry_colsQ hmV hmV,
      entry_colsQ hj hmV, entry_colsQ hmV hlo, entry_colsQ hj hlo]
    exact Runs.bind' (runs_sub cat _ _)
      (Runs.bind' (runs_sub cat _ _)
        (Runs.bind' (runs_minDiff hmV hj _ _ fun t ht => by
            simp only [List.mem_range'_1] at ht; omega)
          (Runs.bind' (runs_minDiff hmV hj _ _ fun t ht => by
              simp only [List.mem_range'_1] at ht; omega)
            (Runs.bind' (runs_min cat _ _)
              (Runs.bind' (runs_add cat _ _)
                (Runs.bind' (runs_muladd cat _ _ _) (runs_lt cat _ _) rfl rfl) rfl rfl)
              rfl rfl) rfl rfl) rfl rfl) rfl rfl)
      (by simp only [pieceOkPair, hh, ↓reduceIte, minA, minB, Dif]
          exact decide_eq_decide.mpr Iff.rfl)
      (by simp only [pairCost, hh, ↓reduceIte, List.length_range']; omega)

theorem runs_pieceTests {k : ℕ} {p : Piece} (hv : p.valid V = true) :
    ∀ (js : List ℕ), (∀ j ∈ js, j < V) →
      Runs (pieceTests K (colsQ tE tL tU V d) ⟨((k - 1 : ℕ) : ℚ)⟩ ⟨((k - 2 : ℕ) : ℚ)⟩ p js) env
        (js.all fun j => decide (j = p.m) || pieceOkPair tE tL tU V d k p j)
        (js.countP (fun j => !decide (j = p.m)) * (pairCost p + 1))
  | [], _ => (Runs.pure _).congr rfl (by simp)
  | j :: js, hj => by
    have ih := runs_pieceTests (k := k) hv js fun u hu => hj u (List.mem_cons_of_mem _ hu)
    by_cases hjm : j = p.m
    · simp only [pieceTests, hjm, ↓reduceIte]
      exact ih.congr (by simp) (by simp)
    · simp only [pieceTests, hjm, ↓reduceIte, Interp.counting_bind]
      exact Runs.bind' (runs_pieceTest hv (hj j List.mem_cons_self))
        (Runs.bind' ih (runs_band cat _ _) rfl rfl) (by simp [hjm])
        (by simp [hjm]; ring)

theorem valid_of_planOk {p : Piece} : ∀ {plan : List Piece}, planOk V plan = true → p ∈ plan →
    p.valid V = true
  | [], _, hp => absurd hp List.not_mem_nil
  | q :: qs, h, hp => by
    simp only [planOk, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hp with rfl | hp
    · exact h.1.1
    · exact valid_of_planOk h.2 hp

theorem runs_countPieces {k : ℕ} (ok0 : Bool) :
    ∀ (ps : List Piece), (∀ p ∈ ps, p.valid V = true) →
      Runs (countPieces K (colsQ tE tL tU V d) ⟨((k - 1 : ℕ) : ℚ)⟩ ⟨((k - 2 : ℕ) : ℚ)⟩ ok0 k V ps)
        env ((ps.map fun p => cond (ok0 && pieceOk tE tL tU V d k p) (p.size k) 0).sum)
        ((ps.map fun p => (V - 1) * (pairCost p + 1) + 1).sum)
  | [], _ => (Runs.pure _).congr rfl rfl
  | p :: ps, hp => by
    have hv := hp p List.mem_cons_self
    have hmV : p.m < V := by
      simp only [Piece.valid, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hv; exact hv.2
    simp only [countPieces, Interp.counting_bind, Interp.counting_pure]
    exact Runs.bind' (runs_pieceTests (k := k) hv (List.range V) fun j hj => List.mem_range.mp hj)
      (Runs.bind' (runs_band cat _ _)
        (Runs.bind' (runs_countPieces ok0 ps fun q hq => hp q (List.mem_cons_of_mem _ hq))
          (Runs.pure _) rfl rfl) rfl rfl)
      (by simp [pieceOk]) (by simp [countP_ne, hmV]; ring)

/-- What the checker of a valid plan does on a network of the family with well-formed weights: its
    count, from the guard and the pieces' tests, and its bill. -/
theorem runs_check {g : Graph} (hg : IsLinearMaxK g = true)
    (hw : WF env.weights g.values d tE tL tU) {plan : List Piece}
    (hplan : planOk g.values plan = true) :
    Runs (check K plan g (maxTask g.positions g.values)) env
      ((plan.map fun p =>
        cond (singleOk g env.weights (maxTask g.positions g.values) (guardInput g) &&
          pieceOk tE tL tU g.values d g.positions p) (p.size g.positions) 0).sum)
      (billPlan g.positions g.values d plan) := by
  simp only [check, Interp.counting_bind]
  refine Runs.bind0 (runs_weightShape hw.hE) ?_
  refine Runs.bind0 (runs_weightShape hw.hL) ?_
  refine Runs.bind0 (runs_weightShape hw.hU) ?_
  simp only [hw.hEs, hw.hLs, hw.hUs, List.headD_cons, beq_self_eq_true, Bool.and_self, hplan,
    ↓reduceIte]
  exact Runs.bind' (runs_single (singleCost_family hg hw))
    (Runs.bind' (runs_columns hw fun t ht => List.mem_range.mp ht)
      (Runs.bind' (runs_lit cat _)
        (Runs.bind' (runs_lit cat _)
          (runs_countPieces _ plan fun p hp => valid_of_planOk hplan hp) rfl rfl)
        rfl rfl)
      rfl rfl)
    rfl (by simp [billPlan]; ring)

end

end LinearMaxKPlans
