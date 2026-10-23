import LinearMaxKPlans.Sound
import LinearMaxK.Exact

/-!
# Exactness and cost of the checker of a plan

The test of a tail is exact, as entry 1's: the input that puts `m` at one position and the token
`t ∈ [lo, m]` minimising `D` at the other `k - 1` belongs to the piece and has margin
`D(m) + (k - 1) D(t)`. For `k = 2` the test of a band is exact too: the input `(m, t)`, with
`t ∈ [lo, hi]` minimising `D`, belongs to the piece and has margin `D(m) + A`. So for such pieces
the tests pass iff the network answers every input of the piece correctly (`pieceOk_iff`). For
`k > 2` the test of a band is sufficient only.

* `check_billed`: on well-formed weights and a valid plan, the count is the sum of the sizes of the
  pieces whose tests pass, if the guard input is answered correctly, and the bill is `billPlan`.
* `planOk_groups`, `billPlan_groups`: the plan of all whole groups is valid, and its bill is entry
  1's plus one (the literal `k - 2`); its count is entry 1's.
-/

namespace LinearMaxKPlans

open CompactCheck Common LinearMaxK

variable {V d : ℕ} {tE tL tU : Tensor ℚ}

theorem muTail_attained {m j lo : ℕ} (hlo : lo ≤ m) :
    ∃ t, lo ≤ t ∧ t ≤ m ∧ muTail tE tL tU V d m j lo = Dif tE tL tU V d m j t := by
  unfold muTail
  rcases foldl_min_mem (Dif tE tL tU V d m j) (List.range' lo (m - lo)) (Dif tE tL tU V d m j m)
    with h | ⟨t, ht, h⟩
  · exact ⟨m, hlo, le_rfl, h⟩
  · rw [List.mem_range'_1] at ht
    exact ⟨t, ht.1, by omega, h⟩

theorem minA_attained {m j lo hi : ℕ} (hlh : lo ≤ hi) :
    ∃ t, lo ≤ t ∧ t ≤ hi ∧ minA tE tL tU V d m j lo hi = Dif tE tL tU V d m j t := by
  unfold minA
  rcases foldl_min_mem (Dif tE tL tU V d m j) (List.range' (lo + 1) (hi - lo))
    (Dif tE tL tU V d m j lo) with h | ⟨t, ht, h⟩
  · exact ⟨lo, le_rfl, hlh, h⟩
  · rw [List.mem_range'_1] at ht
    exact ⟨t, by omega, by omega, h⟩

/-- An input of the family's input space, from its length and its tokens. -/
theorem mem_allInputs_of {k V : ℕ} {x : Input} (hlen : x.length = k) (hx : ∀ t ∈ x, t < V) :
    x ∈ allInputs (List.replicate k V) := mem_allInputs_replicate.mpr ⟨hlen, hx⟩

/-- If every input of a tail, or of a band when `k = 2`, is answered correctly, its tests pass. -/
theorem pieceOkPair_of_correct {g : Graph} (hg : IsLinearMaxK g = true) {w : Weights ℚ}
    (hw : WF w g.values d tE tL tU) {p : Piece} (hv : p.valid g.values = true)
    (hshape : g.positions = 2 ∨ p.hi = p.m) {j : ℕ} (hj : j < g.values) (hjm : j ≠ p.m)
    (h : ∀ x ∈ allInputs (List.replicate g.positions g.values), p.mem x = true →
      Correct g w (maxTask g.positions g.values) x) :
    pieceOkPair tE tL tU g.values d g.positions p j = true := by
  obtain ⟨-, -, hk, -⟩ := isLinearMaxK_spec hg
  simp only [Piece.valid, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hv
  obtain ⟨⟨hlh, hhm⟩, hmV⟩ := hv
  -- the margin of a correct input of the piece against `j` is positive
  have hpos : ∀ x : Input, x.length = g.positions → (∀ t ∈ x, t ≤ p.m) → p.m ∈ x →
      (∀ t ∈ x, p.lo ≤ t) → (∃ t ∈ x, t ≤ p.hi) →
      0 < (x.map (Dif tE tL tU g.values d p.m j)).sum := by
    intro x hlen hle hmx hlo hhi
    have hxV : ∀ t ∈ x, t < g.values := fun t ht => lt_of_le_of_lt (hle t ht) hmV
    have hne : x ≠ [] := List.ne_nil_of_mem hmx
    have hlab : x.foldl max 0 = p.m := label_eq hle hmx
    have hmem : p.mem x = true := (mem_iff hne).mpr ⟨hle, ⟨p.m, hmx, le_rfl⟩, hlo, hhi⟩
    have hc := (correct_iff hg hw hlen hxV).mp (h x (mem_allInputs_of hlen hxV) hmem) j hj
      (by rw [hlab]; exact hjm)
    rw [hlab] at hc
    have := margin_eq (V := g.values) (d := d) (tE := tE) (tL := tL) (tU := tU) x p.m j
    linarith
  by_cases hh : p.hi = p.m
  · obtain ⟨t, hlt, htm, hmu⟩ := muTail_attained (tE := tE) (tL := tL) (tU := tU) (V := g.values)
      (d := d) (j := j) (le_trans hlh hhm)
    have hx := hpos (p.m :: List.replicate (g.positions - 1) t)
      (by simp only [List.length_cons, List.length_replicate]; omega)
      (fun u hu => by
        rcases List.mem_cons.mp hu with rfl | hu
        · exact le_rfl
        · rw [(List.mem_replicate.mp hu).2]; exact htm)
      List.mem_cons_self
      (fun u hu => by
        rcases List.mem_cons.mp hu with rfl | hu
        · exact le_trans hlh hhm
        · rw [(List.mem_replicate.mp hu).2]; exact hlt)
      ⟨p.m, List.mem_cons_self, by omega⟩
    simp only [List.map_cons, List.map_replicate, List.sum_cons, List.sum_replicate,
      nsmul_eq_mul] at hx
    simp only [pieceOkPair, hh, ↓reduceIte, hmu]
    exact decide_eq_true hx
  · have hk2 : g.positions = 2 := hshape.resolve_right hh
    have hhm' : p.hi < p.m := lt_of_le_of_ne hhm hh
    obtain ⟨t, hlt, hth, hA⟩ := minA_attained (tE := tE) (tL := tL) (tU := tU) (V := g.values)
      (d := d) (m := p.m) (j := j) hlh
    have hx := hpos [p.m, t] (by simp [hk2])
      (fun u hu => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
        rcases hu with rfl | rfl <;> omega)
      List.mem_cons_self
      (fun u hu => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
        rcases hu with rfl | rfl <;> omega)
      ⟨t, by simp, hth⟩
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at hx
    simp only [pieceOkPair, hh, ↓reduceIte, hk2, hA]
    exact decide_eq_true (by simp; linarith)

/-- For a tail, or a band when `k = 2`: the tests pass iff the network answers every input of the
    piece correctly. -/
theorem pieceOk_iff {g : Graph} (hg : IsLinearMaxK g = true) {w : Weights ℚ}
    (hw : WF w g.values d tE tL tU) {p : Piece} (hv : p.valid g.values = true)
    (hshape : g.positions = 2 ∨ p.hi = p.m) :
    pieceOk tE tL tU g.values d g.positions p = true ↔
      ∀ x ∈ allInputs (List.replicate g.positions g.values), p.mem x = true →
        Correct g w (maxTask g.positions g.values) x := by
  refine ⟨fun hok x hx hm => piece_correct hg hw hv hok hx hm, fun h => ?_⟩
  refine List.all_eq_true.mpr fun j hj => ?_
  by_cases hjm : j = p.m
  · simp [hjm]
  · simp [hjm, pieceOkPair_of_correct hg hw hv hshape (List.mem_range.mp hj) hjm h]

/-- **Count and cost.** On well-formed weights and a valid plan: the count is the sum of the sizes
    of the pieces whose tests pass, if the guard input is answered correctly, and the bill is
    `billPlan k V d plan`, whatever the weights' values. -/
theorem check_billed {g : Graph} (hg : IsLinearMaxK g = true) {w : Weights ℚ}
    (hw : WF w g.values d tE tL tU) {plan : List Piece} (hplan : planOk g.values plan = true)
    (c : Cert) :
    CostM.billed (check Interp.counting plan g (maxTask g.positions g.values)) ⟨w, c⟩ =
      some ((plan.map fun p =>
        cond (singleOk g w (maxTask g.positions g.values) (guardInput g) &&
          pieceOk tE tL tU g.values d g.positions p) (p.size g.positions) 0).sum,
        billPlan g.positions g.values d plan) :=
  (runs_check (env := ⟨w, c⟩) hg hw hplan).billed

/-! ## The plan of whole groups -/

/-- Every group, whole: the plan of entry 1. -/
def groups (V : ℕ) : List Piece := (List.range V).map fun m => ⟨m, 0, m⟩

theorem apartAll_groups {m : ℕ} : ∀ (ms : List ℕ), (∀ m' ∈ ms, m < m') →
    apartAll ⟨m, 0, m⟩ (ms.map fun m' => ⟨m', 0, m'⟩) = true
  | [], _ => rfl
  | m' :: ms, h => by
    have h1 := h m' List.mem_cons_self
    simp only [List.map_cons, apartAll, Bool.and_eq_true]
    refine ⟨?_, apartAll_groups ms fun u hu => h u (List.mem_cons_of_mem _ hu)⟩
    simp only [Piece.apart, Bool.or_eq_true, Bool.not_eq_true']
    left; left
    exact Bool.eq_false_iff.mpr fun h => absurd (Nat.eq_of_beq_eq_true h) (by omega)

theorem planOk_groups (V : ℕ) : planOk V (groups V) = true := by
  suffices h : ∀ a n, a + n ≤ V → planOk V ((List.range' a n).map fun m => ⟨m, 0, m⟩) = true by
    simpa [groups, List.range_eq_range'] using h 0 V (by omega)
  intro a n
  induction n generalizing a with
  | zero => intro _; rfl
  | succ n ih =>
    intro han
    simp only [List.range'_succ, List.map_cons, planOk, Bool.and_eq_true]
    refine ⟨⟨?_, apartAll_groups _ fun u hu => by simp [List.mem_range'_1] at hu; omega⟩,
      ih (a + 1) (by omega)⟩
    simp [Piece.valid]; omega

/-- The plan of whole groups costs entry 1's bill and one literal more. -/
theorem billPlan_groups (k V d : ℕ) : billPlan k V d (groups V) = bill k V d + 1 := by
  simp only [billPlan, bill, groups, List.map_map, Function.comp_def, pairCost, ↓reduceIte,
    Nat.sub_zero]
  have : ((List.range V).map fun m => (V - 1) * (2 * m + 3 + 1) + 1) =
      (List.range V).map fun m => (V - 1) * (2 * m + 4) + 1 := by
    refine List.map_congr_left fun m _ => ?_
    ring_nf
  rw [this]
  ring

end LinearMaxKPlans
