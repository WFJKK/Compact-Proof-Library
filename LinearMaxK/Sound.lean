import LinearMaxK.Runs

/-!
# Soundness: for all weights, the count is at most the number of correct inputs

The test of the group `m` against the output `j` bounds the margin of every input of the group: if
`x` has largest token `m`, its margin against `j` is `Σ_{t ∈ x} D(t)`, where
`D(t) = M[m,t] - M[j,t]`; one token of `x` is `m` and the other `k - 1` are at most `m`, so the
margin is at least
`D(m) + (k - 1) min_{t ≤ m} D(t)`, which the test requires to be positive (`group_correct`).

For weights that are not well formed, the guard fails and the count is zero (`countGroups_false`).
-/

namespace LinearMaxK

open CompactCheck Common

/-! ## The minimum the checker folds -/

section Min

variable (f : ℕ → ℚ)

theorem foldl_min_le_init : ∀ (l : List ℕ) (a : ℚ), l.foldl (fun a t => min a (f t)) a ≤ a
  | [], _ => le_rfl
  | t :: l, a => le_trans (foldl_min_le_init l (min a (f t))) (min_le_left _ _)

theorem foldl_min_le : ∀ (l : List ℕ) (a : ℚ) {t : ℕ}, t ∈ l →
    l.foldl (fun a t => min a (f t)) a ≤ f t
  | [], _, _, h => absurd h List.not_mem_nil
  | u :: l, a, t, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact le_trans (foldl_min_le_init f l _) (min_le_right _ _)
    · exact foldl_min_le l _ h

theorem foldl_min_mem : ∀ (l : List ℕ) (a : ℚ),
    l.foldl (fun a t => min a (f t)) a = a ∨ ∃ t ∈ l, l.foldl (fun a t => min a (f t)) a = f t
  | [], _ => Or.inl rfl
  | u :: l, a => by
    rcases foldl_min_mem l (min a (f u)) with h | ⟨t, ht, h⟩
    · simp only [List.foldl_cons, h]
      rcases le_total a (f u) with hau | hau
      · left; exact min_eq_left hau
      · right; exact ⟨u, List.mem_cons_self, min_eq_right hau⟩
    · right; exact ⟨t, List.mem_cons_of_mem _ ht, h⟩

end Min

variable {V d : ℕ} {tE tL tU : Tensor ℚ}

theorem mu_le {m j t : ℕ} (ht : t ≤ m) : mu tE tL tU V d m j ≤ Dif tE tL tU V d m j t := by
  unfold mu
  rcases Nat.lt_or_eq_of_le ht with ht | rfl
  · exact foldl_min_le _ _ _ (List.mem_range.mpr ht)
  · exact foldl_min_le_init _ _ _

theorem mu_attained (m j : ℕ) : ∃ t ≤ m, mu tE tL tU V d m j = Dif tE tL tU V d m j t := by
  unfold mu
  rcases foldl_min_mem (Dif tE tL tU V d m j) (List.range m) (Dif tE tL tU V d m j m) with h | h
  · exact ⟨m, le_rfl, h⟩
  · obtain ⟨t, ht, h⟩ := h
    exact ⟨t, le_of_lt (List.mem_range.mp ht), h⟩

/-! ## A group that passes its tests is answered correctly -/

/-- The margin of `x` against `j` is the sum of `D` over its tokens. -/
theorem margin_eq (x : List ℕ) (m j : ℕ) :
    (x.map (Mval tE tL tU V d m)).sum - (x.map (Mval tE tL tU V d j)).sum =
      (x.map (Dif tE tL tU V d m j)).sum := by
  induction x with
  | nil => simp
  | cons t x ih => simp only [List.map_cons, List.sum_cons, Dif, ← ih]; ring

theorem group_correct {g : Graph} (hg : IsLinearMaxK g = true) {w : Weights ℚ}
    (hw : WF w g.values d tE tL tU) {m : ℕ}
    (hok : groupOk tE tL tU g.values d g.positions m = true) {x : Input}
    (hx : x ∈ allInputs (List.replicate g.positions g.values)) (hlab : x.foldl max 0 = m) :
    Correct g w (maxTask g.positions g.values) x := by
  obtain ⟨-, -, hk, -⟩ := isLinearMaxK_spec hg
  obtain ⟨hlen, hxV⟩ := mem_allInputs_replicate.mp hx
  have hne : x ≠ [] := by rintro rfl; simp at hlen; omega
  obtain ⟨hle, t0, ht0, hmt0⟩ := (label_eq_iff hne m).mp hlab
  have hmx : m ∈ x := le_antisymm (hle t0 ht0) hmt0 ▸ ht0
  refine (correct_iff hg hw hlen hxV).mpr fun j hj hjm => ?_
  rw [hlab] at hjm ⊢
  have hpair : pairOk tE tL tU g.values d g.positions m j = true := by
    have := List.all_eq_true.mp hok j (List.mem_range.mpr hj)
    simpa [hjm] using this
  have hpos : 0 < Dif tE tL tU g.values d m j m +
      ((g.positions - 1 : ℕ) : ℚ) * mu tE tL tU g.values d m j := by
    simpa [pairOk] using hpair
  obtain ⟨l1, l2, rfl⟩ := List.append_of_mem hmx
  have hrest : ∀ t ∈ l1 ++ l2, mu tE tL tU g.values d m j ≤ Dif tE tL tU g.values d m j t :=
    fun t ht => mu_le (hle t (by rcases List.mem_append.mp ht with h | h <;> simp [h]))
  have hge := list_sum_ge (l1 ++ l2) (Dif tE tL tU g.values d m j) _ hrest
  have hlen' : ((l1 ++ l2).length : ℚ) = ((g.positions - 1 : ℕ) : ℚ) := by
    simp only [List.length_append, List.length_cons] at hlen ⊢
    congr 1; omega
  rw [hlen'] at hge
  have hsum : ((l1 ++ m :: l2).map (Dif tE tL tU g.values d m j)).sum =
      Dif tE tL tU g.values d m j m + ((l1 ++ l2).map (Dif tE tL tU g.values d m j)).sum := by
    simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons]; ring
  have := margin_eq (V := g.values) (d := d) (tE := tE) (tL := tL) (tU := tU) (l1 ++ m :: l2) m j
  linarith

/-! ## Soundness -/

variable {env : Env}

/-- With the guard's result false, every gate is false and the count is zero, whatever the
    columns hold. -/
theorem countGroups_false {cols : List (List Q)} {km1 : Q} {k : ℕ} :
    ∀ {ms : List ℕ} {c c' : Cost} {n : ℕ},
      (countGroups K cols km1 false k V ms).run env c = some (n, c') → n = 0
  | [], c, c', n, h => by
    simp only [countGroups, Interp.counting_pure, CostM.run_pure, Option.some.injEq,
      Prod.mk.injEq] at h
    exact h.1.symm
  | m :: ms, c, c', n, h => by
    simp only [countGroups, Interp.counting_bind, Interp.counting_pure] at h
    obtain ⟨b, c1, -, h⟩ := Runs.bind_some h
    obtain ⟨bb, c2, hbb, h⟩ := Runs.bind_some h
    obtain ⟨n', c3, hn', h⟩ := Runs.bind_some h
    have hbb' := ((runs_band cat false b).det hbb).1
    have := countGroups_false hn'
    simp only [CostM.run_pure, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1, hbb', this]
    simp

/-- The guard's input is an input of the network. -/
theorem guardInput_valid {g : Graph} (hV : 0 < g.values) :
    (guardInput g).length = g.positions ∧ ∀ t ∈ guardInput g, t < g.values := by
  refine ⟨by simp [guardInput], fun t ht => ?_⟩
  rw [guardInput, List.mem_replicate] at ht
  omega

/-- The count of the checker, when the guard passes, as a finite sum over the groups. -/
theorem count_eq (k V : ℕ) (ok : ℕ → Bool) :
    ((List.range V).map fun m => cond (true && ok m) (Nat.pow (m + 1) k - Nat.pow m k) 0).sum =
      ∑ m ∈ Finset.range V, if ok m then (m + 1) ^ k - m ^ k else 0 := by
  rw [sum_range_eq]
  refine Finset.sum_congr rfl fun m _ => ?_
  cases ok m <;> simp

open Classical in
/-- **Soundness.** For every network of the family, whatever its weights, the count the checker
    computes is at most the number of inputs the network answers correctly. -/
theorem check_sound {g : Graph} (hg : IsLinearMaxK g = true) (w : Weights ℚ) (c : Cert) (n : ℕ)
    (cost : Cost)
    (h : CostM.exec (check Interp.counting g (maxTask g.positions g.values)) ⟨w, c⟩ =
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
      tU.shape == [g.values, d]) = true
  · have hc' := hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc'
    obtain ⟨⟨hEs, hLs⟩, hUs⟩ := hc'
    simp only [hc, ↓reduceIte] at h
    obtain ⟨ok0, c4, hok0, h⟩ := Runs.bind_some h
    obtain ⟨sc, hsc⟩ := single_some hok0
    have hok0v := ((runs_single (task := maxTask g.positions g.values) (x := guardInput g)
      hsc).det hok0).1
    cases hok : singleOk g w (maxTask g.positions g.values) (guardInput g)
    · obtain ⟨cols, c5, -, h⟩ := Runs.bind_some h
      obtain ⟨km1, c6, -, h⟩ := Runs.bind_some h
      rw [hok0v, hok] at h
      rw [countGroups_false h]
      exact Nat.zero_le _
    · obtain ⟨hlen, hxV⟩ := guardInput_valid hV
      obtain ⟨out, hout⟩ := evalGraph_of_singleOk hok
      have hw : WF w g.values d tE tL tU := wf_of_eval hg hE hEs hL hLs hU hUs hlen hxV hout
      have hrun := ((runs_check (env := ⟨w, c⟩) hg hw).det h0).1
      simp only [hok] at hrun
      rw [hrun, count_eq]
      exact sum_groups_le hk hV _ _ fun m _ hok' x hx hlab =>
        decide_eq_true (group_correct hg hw hok' hx hlab)
  · simp only [hc, Bool.false_eq_true, ↓reduceIte, Interp.counting_pure, CostM.run_pure,
      Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]
    exact Nat.zero_le _

end LinearMaxK
