import PathBrute.Runs
import GrossCubic.Correct

/-!
# Soundness of entry 8

`check_sound`: for the family's graph, every count a run of the checker returns is at most the
number of inputs the network answers correctly, for every weights and certificate.

A run that succeeds returns `countV` (`sat_check`): the number of inputs whose test passes. A test
that passes bounds, output by output, the softmax's numerator times the advantage of that output
over the label, from above by a negative number (`test_correct`), and `correct_of_sums`
(`GrossCubic/Bound.lean`) turns that into a correct answer.
-/

namespace PathBrute

open CompactCheck Common AttnClasses GrossCubic Finset

/-- **One input.** If the test of a valid input passes, the network answers it correctly. -/
theorem test_correct {g : Graph} (hg : IsAttn g) {w : Weights ℚ} {N : Net} (hw : N.WF w)
    (hV : N.V = g.values) (hn : N.n = g.positions) {task : Task}
    {X : List (List (List (Q × Q)))}
    (hX : ∀ q < N.V, ∀ t < N.V, ∀ p < N.n,
      expInterval (N.SEf q t + N.SPf q p) =
        some ((((X.getD q []).getD t []).getD p (⟨0⟩, ⟨0⟩)).1.val,
          (((X.getD q []).getD t []).getD p (⟨0⟩, ⟨0⟩)).2.val))
    {x : Input} (hx : x.length = N.n) (hxV : ∀ t ∈ x, t < N.V) (hl : task.label x < N.V)
    (ht : testV N.V N.n (DdTab N) (OdTab N) X (task.label x) x = true) :
    Correct g w task x := by
  have hn0 : 0 < N.n := by have := hg.2.2.1; omega
  have hQ : N.n - 1 < N.n := by omega
  have hxp : ∀ p < N.n, x.getD p 0 < N.V := fun p hp => hxV _ (tk_mem (by omega))
  have hq := hxp _ hQ
  refine correct_of_sums hg hw hV hn hx hxV hl fun j hj hne => ?_
  set Dd := DdTab N with hDd
  set Od := OdTab N with hOd
  set ℓ := task.label x with hℓ
  set q := x.getD (N.n - 1) 0 with hqdef
  unfold testV at ht
  rw [decide_eq_true_eq] at ht
  have h1 := lt_of_le_of_lt (le_maxLV_map (mem_others.mpr ⟨hj, hne⟩)) ht
  rw [sumLV_val, List.map_map, sum_range_eq] at h1
  -- each term of the test bounds the term of the input
  have h2 : ∀ p ∈ range N.n, Real.exp (N.S q (Net.tk x p) p) *
      (((N.D q j : ℝ) - N.D q ℓ) + ((N.O (Net.tk x p) p j : ℝ) - N.O (Net.tk x p) p ℓ)) ≤
      ((kupV (((X.getD q []).getD (x.getD p 0) []).getD p (⟨0⟩, ⟨0⟩))
        ⟨(((Dd.getD q []).getD ℓ []).getD j ⟨0⟩).val +
          ((((Od.getD (x.getD p 0) []).getD p []).getD ℓ []).getD j ⟨0⟩).val⟩).val : ℝ) := by
    intro p hp
    have hp' := mem_range.mp hp
    have ht' := hxp p hp'
    obtain ⟨hlo, hhi⟩ := expInterval_spec (hX _ hq _ ht' p hp')
    have hS : N.SEf q (x.getD p 0) + N.SPf q p = N.S q (x.getD p 0) p := N.score_eq _ _ _
    rw [hS] at hlo hhi
    have h3 := kupV_ge (y := ⟨(((Dd.getD q []).getD ℓ []).getD j ⟨0⟩).val +
      ((((Od.getD (x.getD p 0) []).getD p []).getD ℓ []).getD j ⟨0⟩).val⟩) hlo hhi
    have e : (((Dd.getD q []).getD ℓ []).getD j ⟨0⟩).val +
        ((((Od.getD (x.getD p 0) []).getD p []).getD ℓ []).getD j ⟨0⟩).val =
        (N.D q j - N.D q ℓ) + (N.O (x.getD p 0) p j - N.O (x.getD p 0) p ℓ) := by
      rw [hDd, DdTab, getD_map_range _ hq, getD_mat hl, getD_vec hj, hOd, OdTab,
        getD_map_range _ ht', getD_map_range _ hp', getD_mat hl, getD_vec hj, evT_add_pvT,
        evT_add_pvT]
    simp only at h3
    convert h3 using 3
    rw [e]
    push_cast
    ring
  calc _ ≤ _ := Finset.sum_le_sum h2
    _ < 0 := by
      have h1' : ((∑ p ∈ range N.n, (kupV (((X.getD q []).getD (x.getD p 0) []).getD p (⟨0⟩, ⟨0⟩))
          ⟨(((Dd.getD q []).getD ℓ []).getD j ⟨0⟩).val +
            ((((Od.getD (x.getD p 0) []).getD p []).getD ℓ []).getD j ⟨0⟩).val⟩).val : ℚ) : ℝ) <
          0 := by exact_mod_cast h1
      push_cast at h1'
      exact h1'

/-- The task's labels are outputs. -/
theorem label_lt {mx : Bool} {n V : ℕ} (hn : 0 < n) {x : Input} (hx : x.length = n)
    (hxV : ∀ t ∈ x, t < V) : (taskOf mx n V).label x < V := by
  rw [label_eq hxV]
  refine tok_lt ?_
  have hne : x.map (tok mx V) ≠ [] := by
    intro h
    rw [List.map_eq_nil_iff] at h
    subst h
    simp at hx
    omega
  obtain ⟨t, ht, he⟩ := List.mem_map.mp (foldl_max_mem hne)
  rw [← he]
  exact tok_lt (hxV t ht)

/-- **The count.** Every input counted is answered correctly. -/
theorem countV_le {g : Graph} (hg : IsAttn g) {w : Weights ℚ} {N : Net} (hw : N.WF w)
    (hV : N.V = g.values) (hn : N.n = g.positions) (mx : Bool) {X : List (List (List (Q × Q)))}
    (hX : ∀ q < N.V, ∀ t < N.V, ∀ p < N.n,
      expInterval (N.SEf q t + N.SPf q p) =
        some ((((X.getD q []).getD t []).getD p (⟨0⟩, ⟨0⟩)).1.val,
          (((X.getD q []).getD t []).getD p (⟨0⟩, ⟨0⟩)).2.val)) :
    countV N (taskOf mx N.n N.V) X ≤ numCorrect g w (taskOf mx N.n N.V) := by
  classical
  have hn0 : 0 < N.n := by have := hg.2.2.1; omega
  have hsp : (taskOf mx N.n N.V).space = List.replicate N.n N.V := by cases mx <;> rfl
  unfold countV numCorrect
  rw [List.foldl_map]
  rw [show (fun a x => Interp.counting.nadd a (Interp.counting.countB
      (testV N.V N.n (DdTab N) (OdTab N) X ((taskOf mx N.n N.V).label x) x))) =
      (fun a x => Nat.add a (cond (testV N.V N.n (DdTab N) (OdTab N) X
        ((taskOf mx N.n N.V).label x) x) 1 0)) from rfl, foldl_count, Nat.zero_add]
  refine List.countP_mono_left fun x hx hv => ?_
  rw [hsp] at hx
  obtain ⟨hlen, hxV⟩ := mem_allInputs_replicate.mp hx
  exact decide_eq_true (test_correct hg hw hV hn hX hlen hxV (label_lt hn0 hlen hxV) hv)

/-- **Soundness.** For a graph of the family and the label `max` (`mx`) or `min`, every count a run
    of the checker returns is at most the number of inputs the network answers correctly, for
    every weights and certificate. -/
theorem check_sound {g : Graph} (hg : IsAttn g) (mx : Bool) (w : Weights ℚ) (c : Cert) (n : ℕ)
    (cost : Cost)
    (h : CostM.exec (check Interp.counting g (taskOf mx g.positions g.values)) ⟨w, c⟩ =
      some (n, cost)) :
    n ≤ numCorrect g w (taskOf mx g.positions g.values) := by
  unfold CostM.exec at h
  have h0 := h
  simp only [check, Interp.counting_bind] at h
  obtain ⟨sE, c1, hsE, h⟩ := Runs.bind_some h
  obtain ⟨sP, c2, hsP, h⟩ := Runs.bind_some h
  obtain ⟨sQ, c3, hsQ, h⟩ := Runs.bind_some h
  obtain ⟨sK, c4, hsK, h⟩ := Runs.bind_some h
  obtain ⟨sV, c5, hsV, h⟩ := Runs.bind_some h
  obtain ⟨sO, c6, hsO, h⟩ := Runs.bind_some h
  obtain ⟨sU, c7, hsU, h⟩ := Runs.bind_some h
  obtain ⟨sC, c8, hsC, h⟩ := Runs.bind_some h
  obtain ⟨lE, c9, hlE, h⟩ := Runs.bind_some h
  obtain ⟨lP, c10, hlP, h⟩ := Runs.bind_some h
  obtain ⟨lQ, c11, hlQ, h⟩ := Runs.bind_some h
  obtain ⟨lK, c12, hlK, h⟩ := Runs.bind_some h
  obtain ⟨lV, c13, hlV, h⟩ := Runs.bind_some h
  obtain ⟨lO, c14, hlO, h⟩ := Runs.bind_some h
  obtain ⟨lU, c15, hlU, h⟩ := Runs.bind_some h
  obtain ⟨lC, c16, hlC, h⟩ := Runs.bind_some h
  obtain ⟨tE, hE, rfl⟩ := weightShape_some hsE
  obtain ⟨tP, hP, rfl⟩ := weightShape_some hsP
  obtain ⟨tQ, hQ, rfl⟩ := weightShape_some hsQ
  obtain ⟨tK, hK, rfl⟩ := weightShape_some hsK
  obtain ⟨tV, hV, rfl⟩ := weightShape_some hsV
  obtain ⟨tO, hO, rfl⟩ := weightShape_some hsO
  obtain ⟨tU, hU, rfl⟩ := weightShape_some hsU
  obtain ⟨tC, hC, rfl⟩ := weightShape_some hsC
  obtain ⟨tE', hE', rfl⟩ := weightSize_some hlE
  obtain ⟨tP', hP', rfl⟩ := weightSize_some hlP
  obtain ⟨tQ', hQ', rfl⟩ := weightSize_some hlQ
  obtain ⟨tK', hK', rfl⟩ := weightSize_some hlK
  obtain ⟨tV', hV', rfl⟩ := weightSize_some hlV
  obtain ⟨tO', hO', rfl⟩ := weightSize_some hlO
  obtain ⟨tU', hU', rfl⟩ := weightSize_some hlU
  obtain ⟨tC', hC', rfl⟩ := weightSize_some hlC
  have := hE.symm.trans hE'; cases this
  have := hP.symm.trans hP'; cases this
  have := hQ.symm.trans hQ'; cases this
  have := hK.symm.trans hK'; cases this
  have := hV.symm.trans hV'; cases this
  have := hO.symm.trans hO'; cases this
  have := hU.symm.trans hU'; cases this
  have := hC.symm.trans hC'; cases this
  by_cases hwf : wellFormed g.values g.positions (tE.shape.getD 1 0) (tQ.shape.getD 1 0)
      [tE.shape, tP.shape, tQ.shape, tK.shape, tV.shape, tO.shape, tU.shape, tC.shape]
      [tE.data.size, tP.data.size, tQ.data.size, tK.data.size, tV.data.size, tO.data.size,
        tU.data.size, tC.data.size] = true
  · have hw := WF_of_wellFormed hE hP hQ hK hV hO hU hC hwf
    obtain ⟨X, hX, rfl⟩ :=
      sat_check (env := ⟨w, c⟩) (taskOf mx g.positions g.values) hw rfl rfl
      (by have := hg.2.2.1; simpa using this) _ _ _ h0
    exact countV_le hg hw rfl rfl mx hX
  · simp only [hwf, Bool.false_eq_true, ↓reduceIte, Interp.counting_pure, CostM.run_pure,
      Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]
    exact Nat.zero_le _

/-- **Count and cost.** On well-formed weights with at least one position, when `exp` accepts every
    score, the count is the number of inputs whose test passes and the bill is `bill V n d h`. -/
theorem check_billed {N : Net} (mx : Bool) {g : Graph} {w : Weights ℚ}
    (hw : N.WF w) (hV : N.V = g.values) (hn : N.n = g.positions) (hn0 : 0 < N.n)
    (hexp : ∀ q < N.V, ∀ t < N.V, ∀ p < N.n, (expInterval (N.SEf q t + N.SPf q p)).isSome)
    (c : Cert) :
    CostM.billed (check Interp.counting g (taskOf mx N.n N.V)) ⟨w, c⟩ =
      some (countV N (taskOf mx N.n N.V) (expTab N.V N.n fun q t p => N.SEf q t + N.SPf q p),
        bill N.V N.n N.d N.h) := by
  have hsp : (taskOf mx N.n N.V).space = List.replicate N.n N.V := by cases mx <;> rfl
  refine (runs_check (env := ⟨w, c⟩) _ hw hV hn hn0 hsp (fun x hx => ?_) hexp).billed
  rw [hsp] at hx
  obtain ⟨hlen, hxV⟩ := mem_allInputs_replicate.mp hx
  exact label_lt hn0 hlen hxV

end PathBrute
