import LinearMaxKPlans.Runs
import LinearMaxK.Sound

/-!
# Soundness of the checker of a plan

A piece whose tests pass is answered correctly on every input (`piece_correct`). An input `x` of the
piece `⟨m, lo, hi⟩` has margin `Σ_{t ∈ x} D(t)` against `j`. One token of `x` is `m`, every token is
in `[lo, m]`, and some token is at most `hi`.

* For a tail (`hi = m`) the other `k - 1` tokens are in `[lo, m]`, so the margin is at least
  `D(m) + (k - 1) · min_{lo ≤ t ≤ m} D(t)`.
* For a band (`hi < m`) the token at most `hi` is not the token `m`; so the margin is at least
  `D(m) + A + (k - 2) · B`, with `A` the minimum of `D` over `[lo, hi]` and `B` over `[lo, m]`.

The pieces of a valid plan share no input, so their sizes add up to at most `numCorrect`.
-/

namespace LinearMaxKPlans

open CompactCheck Common LinearMaxK

variable {V d : ℕ} {tE tL tU : Tensor ℚ}

/-! ## The minima -/

theorem muTail_le {m j lo t : ℕ} (hlo : lo ≤ t) (htm : t ≤ m) :
    muTail tE tL tU V d m j lo ≤ Dif tE tL tU V d m j t := by
  unfold muTail
  rcases Nat.lt_or_eq_of_le htm with htm | rfl
  · exact foldl_min_le _ _ _ (List.mem_range'_1.mpr ⟨hlo, by omega⟩)
  · exact foldl_min_le_init _ _ _

theorem minA_le {m j lo hi t : ℕ} (hlo : lo ≤ t) (hth : t ≤ hi) :
    minA tE tL tU V d m j lo hi ≤ Dif tE tL tU V d m j t := by
  unfold minA
  rcases Nat.lt_or_eq_of_le hlo with hlo | rfl
  · exact foldl_min_le _ _ _ (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  · exact foldl_min_le_init _ _ _

theorem minB_le {m j lo hi t : ℕ} (hlo : lo ≤ t) (htm : t ≤ m) :
    minB tE tL tU V d m j lo hi ≤ Dif tE tL tU V d m j t := by
  unfold minB
  rcases Nat.lt_or_eq_of_le htm with htm | rfl
  · refine le_trans (min_le_left _ _) ?_
    by_cases hth : t ≤ hi
    · exact le_trans (foldl_min_le_init _ _ _) (minA_le hlo hth)
    · exact foldl_min_le _ _ _ (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  · exact min_le_right _ _

/-! ## A piece that passes its tests is answered correctly -/

theorem piece_correct {g : Graph} (hg : IsLinearMaxK g = true) {w : Weights ℚ}
    (hw : WF w g.values d tE tL tU) {p : Piece} (hv : p.valid g.values = true)
    (hok : pieceOk tE tL tU g.values d g.positions p = true) {x : Input}
    (hx : x ∈ allInputs (List.replicate g.positions g.values)) (hmem : p.mem x = true) :
    Correct g w (maxTask g.positions g.values) x := by
  obtain ⟨-, -, hk, -⟩ := isLinearMaxK_spec hg
  obtain ⟨hlen, hxV⟩ := mem_allInputs_replicate.mp hx
  have hne : x ≠ [] := mem_allInputs_ne_nil hk hx
  have hhm' : p.hi ≤ p.m := by
    simp only [Piece.valid, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hv; exact hv.1.2
  obtain ⟨hle, ⟨t0, ht0, hmt0⟩, hlo, t1, ht1, ht1h⟩ := (mem_iff hne).mp hmem
  have hlab : x.foldl max 0 = p.m := (label_eq_iff hne p.m).mpr ⟨hle, t0, ht0, hmt0⟩
  have hmx : p.m ∈ x := le_antisymm (hle t0 ht0) hmt0 ▸ ht0
  refine (correct_iff hg hw hlen hxV).mpr fun j hj hjm => ?_
  rw [hlab] at hjm ⊢
  have hpair : pieceOkPair tE tL tU g.values d g.positions p j = true := by
    have := List.all_eq_true.mp hok j (List.mem_range.mpr hj)
    simpa [hjm] using this
  have hmarg := margin_eq (V := g.values) (d := d) (tE := tE) (tL := tL) (tU := tU) x p.m j
  suffices hpos : 0 < (x.map (Dif tE tL tU g.values d p.m j)).sum by linarith
  obtain ⟨l1, l2, rfl⟩ := List.append_of_mem hmx
  have hin : ∀ t ∈ l1 ++ l2, t ∈ l1 ++ p.m :: l2 := fun t ht => by
    rcases List.mem_append.mp ht with h | h <;> simp [h]
  have hsum : ((l1 ++ p.m :: l2).map (Dif tE tL tU g.values d p.m j)).sum =
      Dif tE tL tU g.values d p.m j p.m + ((l1 ++ l2).map (Dif tE tL tU g.values d p.m j)).sum := by
    simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons]; ring
  have hlen12 : (l1 ++ l2).length + 1 = g.positions := by
    simp only [List.length_append, List.length_cons] at hlen ⊢; omega
  by_cases hh : p.hi = p.m
  · have hpos : 0 < Dif tE tL tU g.values d p.m j p.m +
        ((g.positions - 1 : ℕ) : ℚ) * muTail tE tL tU g.values d p.m j p.lo := by
      simpa [pieceOkPair, hh] using hpair
    have hrest : ∀ t ∈ l1 ++ l2,
        muTail tE tL tU g.values d p.m j p.lo ≤ Dif tE tL tU g.values d p.m j t :=
      fun t ht => muTail_le (hlo t (hin t ht)) (hle t (hin t ht))
    have hge := list_sum_ge (l1 ++ l2) (Dif tE tL tU g.values d p.m j) _ hrest
    have hl : ((l1 ++ l2).length : ℚ) = ((g.positions - 1 : ℕ) : ℚ) := by
      congr 1; omega
    rw [hl] at hge
    linarith
  · have hhm : p.hi < p.m := lt_of_le_of_ne hhm' hh
    have hpos : 0 < (Dif tE tL tU g.values d p.m j p.m + minA tE tL tU g.values d p.m j p.lo p.hi) +
        ((g.positions - 2 : ℕ) : ℚ) * minB tE tL tU g.values d p.m j p.lo p.hi := by
      simpa [pieceOkPair, hh] using hpair
    have ht1' : t1 ∈ l1 ++ l2 := by
      rcases List.mem_append.mp ht1 with h | h
      · exact List.mem_append_left _ h
      · rcases List.mem_cons.mp h with h | h
        · omega
        · exact List.mem_append_right _ h
    obtain ⟨l3, l4, h34⟩ := List.append_of_mem ht1'
    have hsum' : ((l1 ++ l2).map (Dif tE tL tU g.values d p.m j)).sum =
        Dif tE tL tU g.values d p.m j t1 +
          ((l3 ++ l4).map (Dif tE tL tU g.values d p.m j)).sum := by
      rw [h34]; simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons]; ring
    have hin' : ∀ t ∈ l3 ++ l4, t ∈ l1 ++ l2 := fun t ht => by
      rw [h34]; rcases List.mem_append.mp ht with h | h <;> simp [h]
    have hrest : ∀ t ∈ l3 ++ l4,
        minB tE tL tU g.values d p.m j p.lo p.hi ≤ Dif tE tL tU g.values d p.m j t :=
      fun t ht => minB_le (hlo t (hin t (hin' t ht))) (hle t (hin t (hin' t ht)))
    have hge := list_sum_ge (l3 ++ l4) (Dif tE tL tU g.values d p.m j) _ hrest
    have hA := minA_le (tE := tE) (tL := tL) (tU := tU) (V := g.values) (d := d) (m := p.m) (j := j)
      (hlo t1 ht1) ht1h
    have hl34 : (l1 ++ l2).length = (l3 ++ l4).length + 1 := by
      rw [h34]; simp only [List.length_append, List.length_cons]; omega
    have hl : ((l3 ++ l4).length : ℚ) = ((g.positions - 2 : ℕ) : ℚ) := by
      congr 1; omega
    rw [hl] at hge
    linarith

/-! ## Soundness -/

variable {env : Env}

/-- With the guard's result false, every gate is false and the count is zero. -/
theorem countPieces_false {cols : List (List Q)} {km1 km2 : Q} {k : ℕ} :
    ∀ {ps : List Piece} {c c' : Cost} {n : ℕ},
      (countPieces K cols km1 km2 false k V ps).run env c = some (n, c') → n = 0
  | [], c, c', n, h => by
    simp only [countPieces, Interp.counting_pure, CostM.run_pure, Option.some.injEq,
      Prod.mk.injEq] at h
    exact h.1.symm
  | p :: ps, c, c', n, h => by
    simp only [countPieces, Interp.counting_bind, Interp.counting_pure] at h
    obtain ⟨b, c1, -, h⟩ := Runs.bind_some h
    obtain ⟨bb, c2, hbb, h⟩ := Runs.bind_some h
    obtain ⟨n', c3, hn', h⟩ := Runs.bind_some h
    have hbb' := ((runs_band cat false b).det hbb).1
    have := countPieces_false hn'
    simp only [CostM.run_pure, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1, hbb', this]
    simp

open Classical in
/-- **Soundness.** For every network of the family, whatever its weights, and every plan, the count
    the checker computes is at most the number of inputs the network answers correctly. -/
theorem check_sound {g : Graph} (hg : IsLinearMaxK g = true) (plan : List Piece) (w : Weights ℚ)
    (c : Cert) (n : ℕ) (cost : Cost)
    (h : CostM.exec (check Interp.counting plan g (maxTask g.positions g.values)) ⟨w, c⟩ =
      some (n, cost)) :
    n ≤ numCorrect g w (maxTask g.positions g.values) := by
  obtain ⟨-, -, hk, hV⟩ := isLinearMaxK_spec hg
  unfold CostM.exec at h
  have h0 := h
  simp only [check, Interp.counting_bind] at h
  obtain ⟨sE, c1, hsE, h⟩ := Runs.bind_some h
  obtain ⟨sL, c2, hsL, h⟩ := Runs.bind_some h
  obtain ⟨sU, c3, hsU, h⟩ := Runs.bind_some h
  obtain ⟨tE, hE, rfl⟩ := weightShape_some hsE
  obtain ⟨tL, hL, rfl⟩ := weightShape_some hsL
  obtain ⟨tU, hU, rfl⟩ := weightShape_some hsU
  generalize hd : tE.shape.headD 0 = d at h
  by_cases hc : (tE.shape == [d, g.values] && tL.shape == [d, d] &&
      tU.shape == [g.values, d] && planOk g.values plan) = true
  · have hc' := hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc'
    obtain ⟨⟨⟨hEs, hLs⟩, hUs⟩, hplan⟩ := hc'
    simp only [hc, ↓reduceIte] at h
    obtain ⟨ok0, c4, hok0, h⟩ := Runs.bind_some h
    obtain ⟨sc, hsc⟩ := single_some hok0
    have hok0v := ((runs_single (task := maxTask g.positions g.values) (x := guardInput g)
      hsc).det hok0).1
    cases hok : singleOk g w (maxTask g.positions g.values) (guardInput g)
    · obtain ⟨cols, c5, -, h⟩ := Runs.bind_some h
      obtain ⟨km1, c6, -, h⟩ := Runs.bind_some h
      obtain ⟨km2, c7, -, h⟩ := Runs.bind_some h
      rw [hok0v, hok] at h
      rw [countPieces_false h]
      exact Nat.zero_le _
    · obtain ⟨hlen, hxV⟩ := guardInput_valid hV
      obtain ⟨out, hout⟩ := evalGraph_of_singleOk hok
      have hw : WF w g.values d tE tL tU := wf_of_eval hg hE hEs hL hLs hU hUs hlen hxV hout
      have hrun := ((runs_check (env := ⟨w, c⟩) hg hw hplan).det h0).1
      simp only [hok, Bool.true_and] at hrun
      rw [hrun]
      unfold numCorrect
      refine le_trans ?_ (sum_countP_le hk plan hplan _)
      refine List.sum_le_sum fun p hp => ?_
      cases hpo : pieceOk tE tL tU g.values d g.positions p
      · simp
      · simp only [Bool.cond_true]
        rw [← countP_mem hk (valid_of_planOk hplan hp)]
        refine le_of_eq (List.countP_congr fun x hx => ?_)
        constructor
        · intro hm
          simp only [hm, Bool.true_and, decide_eq_true_eq]
          exact piece_correct hg hw (valid_of_planOk hplan hp) hpo hx hm
        · intro hm; simp only [Bool.and_eq_true] at hm; exact hm.1
  · simp only [hc, Bool.false_eq_true, ↓reduceIte, Interp.counting_pure, CostM.run_pure,
      Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]
    exact Nat.zero_le _

end LinearMaxKPlans
