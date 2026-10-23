import LinearMaxK.Sound

/-!
# Exactness and cost

The test of the group `m` against `j` is not only sufficient but necessary: the input that puts `m`
at one position and, at the other `k - 1`, the token `t ≤ m` minimising `D(t) = M[m,t] - M[j,t]`
belongs to the group and has margin exactly `D(m) + (k - 1) D(t)` against `j`. So a group passes all
its tests iff the network answers every input of the group correctly (`groupOk_iff`).

Hence, on well-formed weights (`check_billed`): the checker certifies exactly the groups the network
answers entirely correctly, and its bill is `bill V d`, a function of the sizes alone. A network
that answers every input correctly is certified on all `V^k` inputs (`check_complete`).
-/

namespace LinearMaxK

open CompactCheck Common

variable {V d : ℕ} {tE tL tU : Tensor ℚ}

theorem pairOk_of_correct {g : Graph} (hg : IsLinearMaxK g = true) {w : Weights ℚ}
    (hw : WF w g.values d tE tL tU) {m j : ℕ} (hm : m < g.values) (hj : j < g.values)
    (hjm : j ≠ m)
    (h : ∀ x ∈ allInputs (List.replicate g.positions g.values), x.foldl max 0 = m →
      Correct g w (maxTask g.positions g.values) x) :
    pairOk tE tL tU g.values d g.positions m j = true := by
  obtain ⟨-, -, hk, -⟩ := isLinearMaxK_spec hg
  obtain ⟨t, htm, hmu⟩ := mu_attained (V := g.values) (d := d) (tE := tE) (tL := tL) (tU := tU) m j
  have hle : ∀ u ∈ m :: List.replicate (g.positions - 1) t, u ≤ m := by
    intro u hu
    rcases List.mem_cons.mp hu with rfl | hu
    · exact le_rfl
    · rw [(List.mem_replicate.mp hu).2]; exact htm
  have hlen : (m :: List.replicate (g.positions - 1) t).length = g.positions := by
    simp only [List.length_cons, List.length_replicate]; omega
  have hxV : ∀ u ∈ m :: List.replicate (g.positions - 1) t, u < g.values :=
    fun u hu => lt_of_le_of_lt (hle u hu) hm
  have hlab := label_eq hle List.mem_cons_self
  have hx := mem_allInputs_replicate.mpr ⟨hlen, hxV⟩
  have hc := (correct_iff hg hw hlen hxV).mp (h _ hx hlab) j hj (by rw [hlab]; exact hjm)
  rw [hlab] at hc
  have hmarg := margin_eq (V := g.values) (d := d) (tE := tE) (tL := tL) (tU := tU)
    (m :: List.replicate (g.positions - 1) t) m j
  have hsum : ((m :: List.replicate (g.positions - 1) t).map (Dif tE tL tU g.values d m j)).sum =
      Dif tE tL tU g.values d m j m +
        ((g.positions - 1 : ℕ) : ℚ) * Dif tE tL tU g.values d m j t := by
    simp [List.map_replicate, List.sum_replicate, nsmul_eq_mul]
  unfold pairOk
  rw [hmu]
  exact decide_eq_true (by linarith)

/-- A group passes its tests iff the network answers every input of the group correctly. -/
theorem groupOk_iff {g : Graph} (hg : IsLinearMaxK g = true) {w : Weights ℚ}
    (hw : WF w g.values d tE tL tU) {m : ℕ} (hm : m < g.values) :
    groupOk tE tL tU g.values d g.positions m = true ↔
      ∀ x ∈ allInputs (List.replicate g.positions g.values), x.foldl max 0 = m →
        Correct g w (maxTask g.positions g.values) x := by
  refine ⟨fun hok x hx hlab => group_correct hg hw hok hx hlab, fun h => ?_⟩
  refine List.all_eq_true.mpr fun j hj => ?_
  by_cases hjm : j = m
  · simp [hjm]
  · simp [hjm, pairOk_of_correct hg hw hm (List.mem_range.mp hj) hjm h]

/-- `Σ_{m < n} c (2m + 4) = c n (n + 3)`. -/
theorem sum_tests (c : ℕ) : ∀ n : ℕ,
    ((List.range n).map fun m => c * (2 * m + 4)).sum = c * n * (n + 3)
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, sum_tests c n]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    ring

/-- The bill in closed form: the columns `V (d^2 + V d)`, the literal `k - 1`, and the tests
    `(V - 1) V (V + 3)`. -/
theorem bill_eq (V d : ℕ) :
    bill V d = V * (d * d + V * d) + 1 + (V - 1) * V * (V + 3) := by
  rw [bill, sum_tests]

open Classical in
/-- **Exactness and cost.** On well-formed weights the checker certifies exactly the groups the
    network answers entirely correctly, and its bill is `bill V d`, whatever the weights'
    values. -/
theorem check_billed {g : Graph} (hg : IsLinearMaxK g = true) {w : Weights ℚ}
    (hw : WF w g.values d tE tL tU) (c : Cert) :
    CostM.billed (check Interp.counting g (maxTask g.positions g.values)) ⟨w, c⟩ =
      some (∑ m ∈ Finset.range g.values,
          if ∀ x ∈ allInputs (List.replicate g.positions g.values), x.foldl max 0 = m →
              Correct g w (maxTask g.positions g.values) x
          then (m + 1) ^ g.positions - m ^ g.positions else 0,
        bill g.values d) := by
  rw [(runs_check (env := ⟨w, c⟩) hw (maxTask g.positions g.values)).billed, count_eq]
  congr 2
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Finset.mem_range] at hm
  by_cases hgrp : ∀ x ∈ allInputs (List.replicate g.positions g.values), x.foldl max 0 = m →
      Correct g w (maxTask g.positions g.values) x
  · simp only [(groupOk_iff hg hw hm).mpr hgrp, ↓reduceIte]
    exact (ite_eq_left hgrp).symm
  · have : groupOk tE tL tU g.values d g.positions m = false := by
      cases h' : groupOk tE tL tU g.values d g.positions m
      · rfl
      · exact absurd ((groupOk_iff hg hw hm).mp h') hgrp
    simp [this, hgrp]

/-- **The cost formula.** On well-formed weights the bill depends on `V` and `d` only. -/
theorem check_bill {g : Graph} {w : Weights ℚ} (hw : WF w g.values d tE tL tU) (c : Cert) :
    ∃ n, CostM.billed (check Interp.counting g (maxTask g.positions g.values)) ⟨w, c⟩ =
      some (n, bill g.values d) :=
  ⟨_, (runs_check (env := ⟨w, c⟩) hw _).billed⟩

/-- **Completeness.** A network of the family that answers every input correctly is certified on
    all `V^k` of them. -/
theorem check_complete {g : Graph} (hg : IsLinearMaxK g = true) {w : Weights ℚ}
    (hw : WF w g.values d tE tL tU) (c : Cert)
    (hall : ∀ x ∈ allInputs (List.replicate g.positions g.values),
      Correct g w (maxTask g.positions g.values) x) :
    CostM.billed (check Interp.counting g (maxTask g.positions g.values)) ⟨w, c⟩ =
      some (g.values ^ g.positions, bill g.values d) := by
  obtain ⟨-, -, hk, -⟩ := isLinearMaxK_spec hg
  rw [check_billed hg hw c, ← sum_groupSize hk g.values]
  congr 2
  refine Finset.sum_congr rfl fun m _ => ?_
  exact ite_eq_left fun x hx _ => hall x hx

end LinearMaxK
