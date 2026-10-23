import LinearMaxKColumnMax.Runs
import LinearMaxK.Sound

/-!
# Soundness of entry 5: for every plan and all weights

Each test, when it passes, makes the margin of each of its sorted inputs `x` positive against every
other output (`MarginsOk`). The logits of a reordering of `x` are those of `x`, so every reordering
is answered correctly (`correct_of_perm`). With `x`'s largest token `m` and `j ≠ m`, the margin is
`Σ_{t ∈ x} (M[m, t] - M[j, t])`, and:

* `diag`: the margin is `k (M[m, m] - M[j, m]) ≥ k dm_m > 0`.
* `box`: `x` holds `m` `c ≥ 1` times and `k - c` tokens of `[lo, hi]`. A token `t` of these gives at
  least `M[m, t] - top_t = -ℓ(t) ≥ -α`, with `α` the largest loss, and `m` gives at least `dm_m`.
  So the margin is at least `c dm_m - (k - c) α`, which is positive when `(k - 1) α < dm_m`, as
  `α ≥ 0`.
* `refined`: if `j` is not a token of `x`, a token `t ≠ m` gives at least `M[m, t] - mx_t`, and `m`
  gives at least `dm_m`; if it is, the test is its exact margin.
* `exact`: the test compares the logits themselves.

A valid plan's sorted inputs are distinct, so their classes of reorderings are disjoint, and the
count, the sum of the sizes of the terms that pass, is at most the number of inputs answered
correctly (`check_sound`).
-/

namespace LinearMaxKColumnMax

open CompactCheck Common LinearMaxK

/-! ## Maxima -/

theorem le_foldl_max_self : ∀ (l : List ℚ) (a : ℚ), a ≤ l.foldl max a
  | [], _ => le_rfl
  | v :: l, a => le_trans (le_max_left a v) (le_foldl_max_self l _)

theorem le_foldl_max_of_mem : ∀ (l : List ℚ) (a : ℚ) {v : ℚ}, v ∈ l → v ≤ l.foldl max a
  | [], _, _, h => absurd h List.not_mem_nil
  | u :: l, a, v, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact le_trans (le_max_right a v) (le_foldl_max_self l _)
    · exact le_foldl_max_of_mem l _ h

theorem le_maxOfV {vs : List ℚ} {v : ℚ} (h : v ∈ vs) : v ≤ maxOfV vs := by
  cases vs with
  | nil => exact absurd h List.not_mem_nil
  | cons u vs =>
    rcases List.mem_cons.mp h with rfl | h
    · exact le_foldl_max_self vs v
    · exact le_foldl_max_of_mem vs u h

/-! ## The summaries of the columns of `M` -/

section Summaries

variable {V d : ℕ} {tE tL tU : Tensor ℚ}

theorem ent_colsQ {j t : ℕ} (hj : j < V) (ht : t < V) :
    ent (colsQ tE tL tU V d) j t = Mval tE tL tU V d j t := by
  simp [ent, entry_colsQ hj ht]

theorem sm_summsQ {t : ℕ} (ht : t < V) :
    sm K (summsQ tE tL tU V d) t = summQ (colsQ tE tL tU V d) V t := by
  simp [sm, summsQ, List.getD_eq_getElem?_getD, ht]

/-- No output other than `t` gains more from token `t` than `mx_t`. -/
theorem le_mx {j t : ℕ} (hj : j < V) (ht : t < V) (hjt : j ≠ t) :
    Mval tE tL tU V d j t ≤ (sm K (summsQ tE tL tU V d) t).mx.val := by
  rw [sm_summsQ ht, ← ent_colsQ hj ht]
  exact le_maxOfV (List.mem_map.mpr ⟨j, by simp [others, hj, hjt], rfl⟩)

/-- No output gains more from token `t` than `top_t`. -/
theorem le_top {j t : ℕ} (hj : j < V) (ht : t < V) :
    Mval tE tL tU V d j t ≤ (sm K (summsQ tE tL tU V d) t).top.val := by
  by_cases hjt : j = t
  · subst hjt
    rw [sm_summsQ ht]
    simp only [summQ, ent_colsQ ht ht]
    exact le_max_right _ _
  · refine le_trans (le_mx hj ht hjt) ?_
    rw [sm_summsQ ht]
    exact le_max_left _ _

theorem dm_eq {t : ℕ} (ht : t < V) :
    (sm K (summsQ tE tL tU V d) t).dm.val =
      Mval tE tL tU V d t t - (sm K (summsQ tE tL tU V d) t).mx.val := by
  rw [sm_summsQ ht]
  simp [summQ, ent_colsQ ht ht]

/-- Against `j ≠ m`, the token `m` gives at least `dm_m`. -/
theorem dm_le_dif {m j : ℕ} (hm : m < V) (hj : j < V) (hjm : j ≠ m) :
    (sm K (summsQ tE tL tU V d) m).dm.val ≤ Dif tE tL tU V d m j m := by
  rw [dm_eq hm, Dif]
  linarith [le_mx (tE := tE) (tL := tL) (tU := tU) (d := d) hj hm hjm]

end Summaries

/-! ## From margins to correct reorderings -/

section Classes

variable {V d : ℕ} {tE tL tU : Tensor ℚ}

/-- The margin of `x` against every other output is positive. -/
def MarginsOk (tE tL tU : Tensor ℚ) (V d : ℕ) (x : Input) : Prop :=
  ∀ j < V, j ≠ x.foldl max 0 → 0 < (x.map (Dif tE tL tU V d (x.foldl max 0) j)).sum

theorem label_perm {x y : List ℕ} (h : y.Perm x) : y.foldl max 0 = x.foldl max 0 :=
  le_antisymm (foldl_max_le (Nat.zero_le _) fun _ ht => le_foldl_max 0 (h.mem_iff.mp ht))
    (foldl_max_le (Nat.zero_le _) fun _ ht => le_foldl_max 0 (h.mem_iff.mpr ht))

/-- If the margins of `x` are positive, every reordering of `x` is answered correctly. -/
theorem correct_of_perm {g : Graph} (hg : IsLinearMaxK g = true) {w : Weights ℚ}
    (hw : WF w g.values d tE tL tU) {x : Input} (hlen : x.length = g.positions)
    (hxV : ∀ t ∈ x, t < g.values) (hx : MarginsOk tE tL tU g.values d x) {y : Input}
    (hy : y.isPerm x = true) : Correct g w (maxTask g.positions g.values) y := by
  have hp : y.Perm x := List.isPerm_iff.mp hy
  refine (correct_iff hg hw (hp.length_eq.trans hlen) fun t ht => hxV t (hp.mem_iff.mp ht)).mpr ?_
  intro j hj hne
  rw [label_perm hp] at hne ⊢
  rw [(hp.map _).sum_eq, (hp.map _).sum_eq]
  have h1 := hx j hj hne
  have h2 := margin_eq (V := g.values) (d := d) (tE := tE) (tL := tL) (tU := tU) x
    (x.foldl max 0) j
  linarith

end Classes

/-! ## Each test, when it passes -/

section Terms

variable {V d k : ℕ} {tE tL tU : Tensor ℚ}

set_option hygiene false in
/-- The columns of `M`. -/
local notation "cQ" => colsQ tE tL tU V d
set_option hygiene false in
/-- Their summaries. -/
local notation "sQ" => summsQ tE tL tU V d

theorem margins_diag (hk : 0 < k) {m : ℕ} (hm : m < V)
    (h : decide (0 < (sm K sQ m).dm.val) = true) :
    MarginsOk tE tL tU V d (List.replicate k m) := by
  have hlab : (List.replicate k m).foldl max 0 = m :=
    label_eq (fun t ht => le_of_eq (List.mem_replicate.mp ht).2)
      (List.mem_replicate.mpr ⟨by omega, rfl⟩)
  intro j hj hne
  rw [hlab] at hne ⊢
  simp only [List.map_replicate, List.sum_replicate, nsmul_eq_mul]
  have h1 := dm_le_dif (tE := tE) (tL := tL) (tU := tU) (d := d) hm hj hne
  have h2 := of_decide_eq_true h
  have hk' : (0 : ℚ) < k := by exact_mod_cast hk
  exact mul_pos hk' (by linarith)

/-- The sorted inputs of a box. -/
theorem mem_box_inputs {m lo hi : ℕ} {dg : Bool} {x : Input}
    (hx : x ∈ (Term.box m lo hi dg).inputs k) :
    ∃ i y, i < k ∧ y.length = k - 1 - i ∧ (∀ t ∈ y, lo ≤ t ∧ t ≤ hi) ∧
      x = y ++ List.replicate (i + 1) m := by
  simp only [Term.inputs, List.mem_flatMap, List.mem_range, List.mem_map] at hx
  obtain ⟨i, hi', y, hy, rfl⟩ := hx
  obtain ⟨hyl, -, hyr⟩ := Symmetry.mem_sortedFrom.mp hy
  refine ⟨i, y, by split at hi' <;> omega, hyl, fun t ht => ⟨(hyr t ht).1, ?_⟩, rfl⟩
  have := (hyr t ht).2
  omega

theorem loss_le_lossMax {m lo hi t : ℕ} (hlo : lo ≤ t) (hhi : t ≤ hi) :
    loss cQ sQ m t ≤ lossMax cQ sQ m lo hi := by
  unfold lossMax
  rcases Nat.eq_or_lt_of_le hlo with rfl | hlt
  · exact le_foldl_max_self _ _
  · exact le_foldl_max_of_mem _ _
      (List.mem_map.mpr ⟨t, List.mem_range'_1.mpr ⟨hlt, by omega⟩, rfl⟩)

theorem margins_box (hk : 0 < k) {m lo hi : ℕ} {dg : Bool}
    (hv : (Term.box m lo hi dg).valid V = true) (h : boxOk cQ sQ k m lo hi = true) {x : Input}
    (hx : x ∈ (Term.box m lo hi dg).inputs k) : MarginsOk tE tL tU V d x := by
  simp only [Term.valid, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hv
  obtain ⟨⟨hlh, hhm⟩, hmV⟩ := hv
  obtain ⟨i, y, hik, hyl, hyr, rfl⟩ := mem_box_inputs hx
  have hlab : (y ++ List.replicate (i + 1) m).foldl max 0 = m := by
    refine label_eq (fun t ht => ?_)
      (List.mem_append_right _ (List.mem_replicate.mpr ⟨by omega, rfl⟩))
    rcases List.mem_append.mp ht with ht | ht
    · have := (hyr t ht).2; omega
    · exact le_of_eq (List.mem_replicate.mp ht).2
  intro j hj hne
  rw [hlab] at hne ⊢
  have hlossV : ∀ t, t < V → loss cQ sQ m t = (sm K sQ t).top.val - Mval tE tL tU V d m t := by
    intro t ht
    simp only [loss, ent_colsQ hmV ht]
  have hα0 : 0 ≤ lossMax cQ sQ m lo hi := by
    have h1 := loss_le_lossMax (tE := tE) (tL := tL) (tU := tU) (V := V) (d := d) (m := m)
      (le_refl lo) hlh
    rw [hlossV lo (by omega)] at h1
    have h2 := le_top (tE := tE) (tL := tL) (tU := tU) (d := d) hmV (show lo < V by omega)
    linarith
  have hy : ∀ t ∈ y, -lossMax cQ sQ m lo hi ≤ Dif tE tL tU V d m j t := by
    intro t ht
    obtain ⟨h1, h2⟩ := hyr t ht
    have htV : t < V := by omega
    have h3 := loss_le_lossMax (tE := tE) (tL := tL) (tU := tU) (V := V) (d := d) (m := m) h1 h2
    rw [hlossV t htV] at h3
    have h4 := le_top (tE := tE) (tL := tL) (tU := tU) (d := d) hj htV
    simp only [Dif]
    linarith
  have hsum := list_sum_ge y (Dif tE tL tU V d m j) (-lossMax cQ sQ m lo hi) hy
  rw [mul_neg] at hsum
  have hdm := dm_le_dif (tE := tE) (tL := tL) (tU := tU) (d := d) hmV hj hne
  have htest := of_decide_eq_true h
  have hk1 : ((k - 1 : ℕ) : ℚ) = (y.length : ℚ) + i := by
    rw [show k - 1 = y.length + i by omega, Nat.cast_add]
  rw [hk1] at htest
  simp only [List.map_append, List.sum_append, List.map_replicate, List.sum_replicate,
    nsmul_eq_mul]
  push_cast
  have hi0 : (0 : ℚ) ≤ i := by positivity
  have hyα : 0 ≤ ((y.length : ℚ) + i) * lossMax cQ sQ m lo hi :=
    mul_nonneg (by positivity) hα0
  have hdm0 : 0 ≤ (sm K sQ m).dm.val := by linarith
  linarith [mul_nonneg hi0 hα0, mul_nonneg hi0 hdm0, mul_le_mul_of_nonneg_left hdm hi0]

/-- Splitting a sum over the tokens of `x` into the tokens other than `m` and the copies of `m`. -/
theorem sum_split (x : List ℕ) (m : ℕ) (f : ℕ → ℚ) :
    (x.map f).sum = ((x.filter fun t => t != m).map f).sum +
      ((x.filter fun t => t == m).length : ℚ) * f m := by
  induction x with
  | nil => simp
  | cons a x ih =>
    by_cases ha : a = m
    · subst ha; simp [ih]; ring
    · have : (a != m) = true := by simp [ha]
      have : (a == m) = false := by simp [ha]
      simp [*]; ring

/-- The same, with the largest token of `x`. -/
theorem sum_split_label (x : List ℕ) (f : ℕ → ℚ) :
    (x.map f).sum = ((othersOf x).map f).sum + (copies x : ℚ) * f (x.foldl max 0) :=
  sum_split x _ f

theorem exists_V {x : Input} (hxV : ∀ t ∈ x, t < V) (hx0 : x ≠ []) : 0 < V := by
  obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil x hx0
  exact lt_of_le_of_lt (Nat.zero_le _) (hxV a ha)

theorem sum_ent_eq (j m : ℕ) (hj : j < V) (hm : m < V) {l : List ℕ} (hl : ∀ t ∈ l, t < V) :
    (l.map fun t => ent cQ j t - ent cQ m t).sum =
      (l.map fun t => Mval tE tL tU V d j t - Mval tE tL tU V d m t).sum := by
  congr 1
  exact List.map_congr_left fun t ht => by rw [ent_colsQ hj (hl t ht), ent_colsQ hm (hl t ht)]

theorem margins_refined {x : Input} (hxV : ∀ t ∈ x, t < V) (hx0 : x ≠ [])
    (h : refinedOk cQ sQ x = true) : MarginsOk tE tL tU V d x := by
  have hV := exists_V hxV hx0
  have hmV : x.foldl max 0 < V := label_lt hV hxV
  simp only [refinedOk, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hA, hB⟩ := h
  have hA := of_decide_eq_true hA
  intro j hj hne
  have hos : ∀ t ∈ othersOf x, t < V := fun t ht => hxV t (List.mem_of_mem_filter ht)
  rw [sum_split_label x]
  have hc0 : (0 : ℚ) ≤ (copies x : ℚ) := Nat.cast_nonneg _
  have hdm := dm_le_dif (tE := tE) (tL := tL) (tU := tU) (d := d) hmV hj hne
  -- the sum over the other tokens, against `j`, and the same with the signs reversed
  have hneg : ((othersOf x).map (Dif tE tL tU V d (x.foldl max 0) j)).sum +
      ((othersOf x).map fun t =>
        Mval tE tL tU V d j t - Mval tE tL tU V d (x.foldl max 0) t).sum = 0 := by
    rw [← List.sum_map_add]
    exact List.sum_eq_zero fun y hy => by
      obtain ⟨t, -, rfl⟩ := List.mem_map.mp hy
      simp only [Dif]; ring
  by_cases hjx : j ∈ x
  · -- `j` is a token of `x`: its exact margin
    have hjd : j ∈ distinctOf x := by
      simp only [distinctOf, List.mem_filter, List.mem_range, List.contains_iff_mem]
      exact ⟨lt_of_le_of_ne (le_foldl_max 0 hjx) hne, hjx⟩
    have hJ := of_decide_eq_true (hB j hjd)
    rw [sum_ent_eq j _ hj hmV hos, ent_colsQ hmV hmV, ent_colsQ hj hmV] at hJ
    have hJ' : ((othersOf x).map fun t =>
        Mval tE tL tU V d j t - Mval tE tL tU V d (x.foldl max 0) t).sum <
        (copies x : ℚ) * Dif tE tL tU V d (x.foldl max 0) j (x.foldl max 0) := hJ
    linarith
  · -- `j` is not a token of `x`: the summaries
    have hkey : ∀ t ∈ othersOf x, 0 ≤ ((sm K sQ t).mx.val - ent cQ (x.foldl max 0) t) +
        Dif tE tL tU V d (x.foldl max 0) j t := by
      intro t ht
      have htx : t ∈ x := List.mem_of_mem_filter ht
      have hjt : j ≠ t := fun hjt => hjx (hjt ▸ htx)
      rw [ent_colsQ hmV (hos t ht)]
      have := le_mx (tE := tE) (tL := tL) (tU := tU) (d := d) hj (hos t ht) hjt
      simp only [Dif]; linarith
    have hsum := List.sum_nonneg (l := (othersOf x).map fun t =>
      ((sm K sQ t).mx.val - ent cQ (x.foldl max 0) t) + Dif tE tL tU V d (x.foldl max 0) j t)
      fun y hy => by
        obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hy
        exact hkey t ht
    rw [List.sum_map_add] at hsum
    have hcd := mul_le_mul_of_nonneg_left hdm hc0
    linarith

/-- Logit `j` of `x`, from the columns of `M`. -/
theorem logitV_eq {x : Input} (hxV : ∀ t ∈ x, t < V) (hx0 : x ≠ []) {j : ℕ} (hj : j < V) :
    logitV cQ x j = (x.map (Mval tE tL tU V d j)).sum := by
  obtain ⟨a, rest, rfl⟩ := List.exists_cons_of_ne_nil hx0
  simp only [logitV, List.headD_cons, List.tail_cons, List.map_cons, List.sum_cons]
  rw [ent_colsQ hj (hxV a List.mem_cons_self)]
  congr 1
  exact congrArg List.sum
    (List.map_congr_left fun t ht => ent_colsQ hj (hxV t (List.mem_cons_of_mem _ ht)))

theorem margins_exact {x : Input} (hxV : ∀ t ∈ x, t < V) (hx0 : x ≠ [])
    (h : exactOk cQ V x = true) : MarginsOk tE tL tU V d x := by
  have hV := exists_V hxV hx0
  have hmV : x.foldl max 0 < V := label_lt hV hxV
  have h1 := of_decide_eq_true h
  intro j hj hne
  have h2 : logitV cQ x j ≤ maxOfV ((others V (x.foldl max 0)).map (logitV cQ x)) :=
    le_maxOfV (List.mem_map.mpr ⟨j, by simp [others, hj, hne], rfl⟩)
  rw [logitV_eq hxV hx0 hj] at h2
  rw [logitV_eq hxV hx0 hmV] at h1
  have h3 := margin_eq (V := V) (d := d) (tE := tE) (tL := tL) (tU := tU) x (x.foldl max 0) j
  linarith

/-- The sorted inputs of a term that passes have positive margins. -/
theorem term_margins (hk : 0 < k) {t : Term} (hv : t.valid V = true)
    (hin : ∀ x ∈ t.inputs k, validInput V k x = true) (h : termOk cQ sQ V k t = true) :
    ∀ x ∈ t.inputs k, MarginsOk tE tL tU V d x := by
  intro x hx
  obtain ⟨-, hlen, hxV⟩ := validInput_spec.mp (hin x hx)
  have hx0 : x ≠ [] := by
    rintro rfl
    simp only [List.length_nil] at hlen
    omega
  rcases t with m | ⟨m, lo, hi, dg⟩ | y | y
  · simp only [Term.inputs, List.mem_singleton] at hx
    subst hx
    simp only [Term.valid, Nat.blt_eq] at hv
    exact margins_diag hk hv h
  · exact margins_box hk hv h hx
  · simp only [Term.inputs, List.mem_singleton] at hx
    subst hx
    exact margins_refined hxV hx0 h
  · simp only [Term.inputs, List.mem_singleton] at hx
    subst hx
    exact margins_exact hxV hx0 h

end Terms

/-! ## Counting -/

theorem size_eq (V k : ℕ) (t : Term) :
    t.size V k = ((t.inputs k).map (Symmetry.mult V k)).sum := by
  unfold Term.size
  generalize t.inputs k = l
  induction l with
  | nil => rfl
  | cons x l ih => rw [List.foldr_cons, List.map_cons, List.sum_cons, ← ih]; rfl

theorem nodup_of_nodupB : ∀ {S : List Input}, nodupB S = true → S.Nodup
  | [], _ => List.nodup_nil
  | x :: xs, h => by
    simp only [nodupB, Bool.and_eq_true, Bool.not_eq_true'] at h
    refine List.nodup_cons.mpr ⟨fun hx => ?_, nodup_of_nodupB h.2⟩
    have := List.contains_iff_mem.mpr hx
    rw [h.1] at this
    cases this

/-- Distinct sorted inputs have disjoint classes of reorderings. -/
theorem classes_disjoint {S : List Input} (hS : S.Nodup) (hs : ∀ x ∈ S, x.Pairwise (· ≤ ·)) :
    S.Pairwise fun a b => ∀ y : Input, y.isPerm a = true → y.isPerm b = false := by
  refine hS.imp_of_mem fun {a b} ha hb hab y hya => ?_
  rw [Bool.eq_false_iff]
  intro hyb
  rw [List.isPerm_iff] at hya hyb
  exact hab (List.Perm.eq_of_pairwise (fun a b _ _ h1 h2 => Nat.le_antisymm h1 h2)
    (hs a ha) (hs b hb) (hya.symm.trans hyb))

theorem sum_map_flatMap {α β : Type} (l : List α) (g : α → List β) (F : β → ℕ) :
    ((l.flatMap g).map F).sum = (l.map fun a => ((g a).map F).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, ih]

open Classical in
/-- The count of a valid plan, on well-formed weights, is at most the number of inputs answered
    correctly. -/
theorem count_le {g : Graph} (hg : IsLinearMaxK g = true) {w : Weights ℚ} {d : ℕ}
    {tE tL tU : Tensor ℚ} (hw : WF w g.values d tE tL tU) {plan : List Term}
    (hplan : planOk g.values g.positions plan = true) :
    (plan.map fun t => cond (termOk (colsQ tE tL tU g.values d) (summsQ tE tL tU g.values d)
        g.values g.positions t) (t.size g.values g.positions) 0).sum ≤
      numCorrect g w (maxTask g.positions g.values) := by
  obtain ⟨-, -, hk, -⟩ := isLinearMaxK_spec hg
  obtain ⟨hval, hin, hnd⟩ := planOk_spec hplan
  have hterm : ∀ t ∈ plan, cond (termOk (colsQ tE tL tU g.values d) (summsQ tE tL tU g.values d)
      g.values g.positions t) (t.size g.values g.positions) 0 ≤
      ((t.inputs g.positions).map fun x =>
        (allInputs (List.replicate g.positions g.values)).countP fun y =>
          y.isPerm x && decide (Correct g w (maxTask g.positions g.values) y)).sum := by
    intro t ht
    cases hok : termOk (colsQ tE tL tU g.values d) (summsQ tE tL tU g.values d) g.values
      g.positions t
    · simp
    · rw [Bool.cond_true, size_eq]
      refine List.sum_le_sum fun x hx => le_of_eq ?_
      obtain ⟨-, hlen, hxV⟩ := validInput_spec.mp (hin t ht x hx)
      have hm := term_margins (tE := tE) (tL := tL) (tU := tU) (d := d) hk (hval t ht) (hin t ht)
        hok x hx
      rw [← Symmetry.countP_perm g.positions x hlen hxV]
      refine List.countP_congr fun y _ => ?_
      constructor
      · intro hp
        simp only [hp, Bool.true_and, decide_eq_true_eq]
        exact correct_of_perm hg hw hlen hxV hm hp
      · intro hp
        simp only [Bool.and_eq_true] at hp
        exact hp.1
  refine le_trans (List.sum_le_sum hterm) ?_
  rw [← sum_map_flatMap]
  unfold numCorrect
  exact Symmetry.sum_countP_le_of_pairwise _ (fun (x y : Input) => y.isPerm x) _ _
    ((classes_disjoint (nodup_of_nodupB hnd) fun x hx => by
      obtain ⟨t, ht, hxt⟩ := List.mem_flatMap.mp hx
      exact (validInput_spec.mp (hin t ht x hxt)).1).imp fun h y _ => h y)

open Classical in
/-- **Soundness.** For every network of the family, whatever its weights, and every plan, the count
    the checker computes is at most the number of inputs the network answers correctly. -/
theorem check_sound {g : Graph} (hg : IsLinearMaxK g = true) (plan : List Term) (w : Weights ℚ)
    (c : Cert) (n : ℕ) (cost : Cost)
    (h : CostM.exec (check Interp.counting plan g (maxTask g.positions g.values)) ⟨w, c⟩ =
      some (n, cost)) :
    n ≤ numCorrect g w (maxTask g.positions g.values) := by
  obtain ⟨-, -, -, hV⟩ := isLinearMaxK_spec hg
  unfold CostM.exec at h
  have h0 := h
  simp only [check, Interp.counting_bind] at h
  obtain ⟨sE, c1, hsE, h⟩ := Runs.bind_some h
  obtain ⟨sL, c2, hsL, h⟩ := Runs.bind_some h
  obtain ⟨sU, c3, hsU, h⟩ := Runs.bind_some h
  obtain ⟨lE, c4, hlE, h⟩ := Runs.bind_some h
  obtain ⟨lL, c5, hlL, h⟩ := Runs.bind_some h
  obtain ⟨lU, c6, hlU, h⟩ := Runs.bind_some h
  obtain ⟨tE, hE, rfl⟩ := weightShape_some hsE
  obtain ⟨tL, hL, rfl⟩ := weightShape_some hsL
  obtain ⟨tU, hU, rfl⟩ := weightShape_some hsU
  obtain ⟨tE', hE', rfl⟩ := weightSize_some hlE
  obtain ⟨tL', hL', rfl⟩ := weightSize_some hlL
  obtain ⟨tU', hU', rfl⟩ := weightSize_some hlU
  have := hE.symm.trans hE'; cases this
  have := hL.symm.trans hL'; cases this
  have := hU.symm.trans hU'; cases this
  generalize hd : tE.shape.headD 0 = d at h
  by_cases hc : (wellFormed g.values d tE.shape tL.shape tU.shape tE.data.size tL.data.size
      tU.data.size && planOk g.values g.positions plan) = true
  · rw [Bool.and_eq_true] at hc
    have hw := WF_of_wellFormed hE hL hU hc.1
    rw [((runs_check (env := ⟨w, c⟩) hw hV hc.2 (maxTask g.positions g.values)).det h0).1]
    exact count_le hg hw hc.2
  · simp only [hc, Bool.false_eq_true, ↓reduceIte, Interp.counting_pure, CostM.run_pure,
      Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]
    exact Nat.zero_le _

/-- **Count and cost.** On well-formed weights and a valid plan, the count is the sum of the sizes
    of the terms whose tests pass, and the bill is `billPlan V k d plan`, whatever the weights'
    values. -/
theorem check_billed {g : Graph} {w : Weights ℚ} {d : ℕ} {tE tL tU : Tensor ℚ}
    (hw : WF w g.values d tE tL tU) (hV : 0 < g.values) {plan : List Term}
    (hplan : planOk g.values g.positions plan = true) (c : Cert) :
    CostM.billed (check Interp.counting plan g (maxTask g.positions g.values)) ⟨w, c⟩ =
      some ((plan.map fun t => cond (termOk (colsQ tE tL tU g.values d)
          (summsQ tE tL tU g.values d) g.values g.positions t) (t.size g.values g.positions) 0).sum,
        billPlan g.values g.positions d plan) :=
  (runs_check (env := ⟨w, c⟩) hw hV hplan _).billed

end LinearMaxKColumnMax
