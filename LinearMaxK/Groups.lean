import LinearMaxK.Family

/-!
# The groups of inputs

The checker certifies inputs by groups: the group of `m` is the set of inputs whose largest token
is `m`, which is the label of every input in it. Among the `V^k` inputs, `(m + 1)^k` have every
token at most `m`, so the group of `m` has `(m + 1)^k - m^k` inputs (`groupSize`), and the groups
partition the inputs (`countP_by_group`).
-/

namespace LinearMaxK

open CompactCheck Common

theorem mem_allInputs_replicate : ∀ {k V : ℕ} {x : Input},
    x ∈ allInputs (List.replicate k V) ↔ x.length = k ∧ ∀ t ∈ x, t < V
  | 0, V, x => by
    simp only [List.replicate_zero, allInputs, List.mem_singleton]
    constructor
    · rintro rfl; simp
    · rintro ⟨h, -⟩; exact List.eq_nil_of_length_eq_zero h
  | k + 1, V, x => by
    simp only [List.replicate_succ, allInputs, List.mem_flatMap, List.mem_range, List.mem_map]
    constructor
    · rintro ⟨t, ht, y, hy, rfl⟩
      obtain ⟨hyl, hyV⟩ := mem_allInputs_replicate.mp hy
      refine ⟨by simp [hyl], fun u hu => ?_⟩
      rcases List.mem_cons.mp hu with rfl | hu
      · exact ht
      · exact hyV u hu
    · rintro ⟨hl, hV⟩
      cases x with
      | nil => simp at hl
      | cons t y =>
        refine ⟨t, hV t List.mem_cons_self, y, ?_, rfl⟩
        exact mem_allInputs_replicate.mpr
          ⟨by simpa using hl, fun u hu => hV u (List.mem_cons_of_mem _ hu)⟩

theorem countP_range_lt (V b : ℕ) : (List.range V).countP (fun t => decide (t < b)) = min V b := by
  induction V with
  | zero => simp
  | succ V ih =>
    rw [List.range_succ, List.countP_append, ih]
    simp only [List.countP_cons, List.countP_nil, decide_eq_true_eq]
    split <;> omega

/-- `b^k` inputs have every token below `b`. -/
theorem countP_allLt : ∀ (k : ℕ) {V b : ℕ}, b ≤ V →
    (allInputs (List.replicate k V)).countP (fun x => x.all fun t => decide (t < b)) = b ^ k
  | 0, V, b, _ => by simp [allInputs]
  | k + 1, V, b, hb => by
    simp only [List.replicate_succ, allInputs, List.countP_flatMap, Function.comp_def,
      List.countP_map, List.all_cons]
    have : ∀ t, (allInputs (List.replicate k V)).countP
        (fun y => decide (t < b) && y.all fun u => decide (u < b)) =
        if decide (t < b) then b ^ k else 0 := by
      intro t
      by_cases ht : t < b
      · simp only [ht, decide_true, Bool.true_and, ite_true]
        exact countP_allLt k hb
      · simp [ht]
    simp only [this, sum_ite_const, countP_range_lt, Nat.min_eq_right hb, Nat.pow_succ,
      Nat.mul_comm]

theorem foldl_max_mem : ∀ (x : List ℕ) (a : ℕ), x.foldl max a = a ∨ x.foldl max a ∈ x
  | [], _ => Or.inl rfl
  | t :: x, a => by
    rcases foldl_max_mem x (max a t) with h | h
    · simp only [List.foldl_cons, h]
      rcases Nat.le_total a t with hat | hat
      · right; rw [max_eq_right hat]; exact List.mem_cons_self
      · left; exact max_eq_left hat
    · right; exact List.mem_cons_of_mem _ h

/-- On a nonempty input, the largest token is `m` iff every token is at most `m` and some token is
    at least `m`. -/
theorem label_eq_iff {x : List ℕ} (hx : x ≠ []) (m : ℕ) :
    x.foldl max 0 = m ↔ (∀ t ∈ x, t ≤ m) ∧ ∃ t ∈ x, m ≤ t := by
  constructor
  · rintro rfl
    refine ⟨fun t ht => le_foldl_max 0 ht, ?_⟩
    rcases foldl_max_mem x 0 with h | h
    · obtain ⟨t, ht⟩ := List.exists_mem_of_ne_nil x hx
      exact ⟨t, ht, by rw [h]; exact Nat.zero_le t⟩
    · exact ⟨_, h, le_rfl⟩
  · rintro ⟨hle, t, ht, hmt⟩
    have : t = m := le_antisymm (hle t ht) hmt
    exact label_eq hle (this ▸ ht)

theorem countP_split {α : Type} (L : List α) (p q : α → Bool) :
    L.countP p = L.countP (fun x => p x && q x) + L.countP (fun x => p x && !q x) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.countP_cons, ih]
    cases p a <;> cases q a <;> simp <;> omega

/-- Every token below `b`. -/
def allLt (b : ℕ) (x : Input) : Bool := x.all fun t => decide (t < b)

/-- The group of `m` has `(m + 1)^k - m^k` inputs. -/
theorem groupSize {k V m : ℕ} (hk : 0 < k) (hm : m < V) :
    (allInputs (List.replicate k V)).countP (fun x => x.foldl max 0 == m) =
      (m + 1) ^ k - m ^ k := by
  have hA : (allInputs (List.replicate k V)).countP (allLt (m + 1)) = (m + 1) ^ k :=
    countP_allLt k hm
  have hB : (allInputs (List.replicate k V)).countP (allLt m) = m ^ k :=
    countP_allLt k (by omega)
  have hsplit := countP_split (allInputs (List.replicate k V)) (allLt (m + 1)) (allLt m)
  have hAB : (allInputs (List.replicate k V)).countP (fun x => allLt (m + 1) x && allLt m x) =
      (allInputs (List.replicate k V)).countP (allLt m) := by
    apply List.countP_congr
    intro x _
    simp only [allLt, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨fun t ht => by have := h t ht; omega, h⟩⟩
  have hG : (allInputs (List.replicate k V)).countP (fun x => x.foldl max 0 == m) =
      (allInputs (List.replicate k V)).countP (fun x => allLt (m + 1) x && !allLt m x) := by
    apply List.countP_congr
    intro x hx
    have hne : x ≠ [] := by
      intro h
      have := (mem_allInputs_replicate.mp hx).1
      rw [h] at this
      simp only [List.length_nil] at this
      omega
    simp only [allLt, beq_iff_eq, label_eq_iff hne, Bool.and_eq_true, Bool.not_eq_eq_eq_not,
      Bool.not_true, List.all_eq_false, List.all_eq_true, decide_eq_true_eq, not_lt,
      Nat.lt_succ_iff]
  rw [hG]
  omega

/-- The groups of `m < V` partition a list of inputs whose labels are below `V`. -/
theorem countP_by_group {L : List Input} {V : ℕ} (hL : ∀ x ∈ L, x.foldl max 0 < V)
    (P : Input → Bool) :
    L.countP P = ∑ m ∈ Finset.range V, L.countP (fun x => P x && x.foldl max 0 == m) := by
  induction L with
  | nil => simp
  | cons x L ih =>
    have hx := hL x List.mem_cons_self
    simp only [List.countP_cons, ih fun y hy => hL y (List.mem_cons_of_mem _ hy),
      Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single (x.foldl max 0)]
    · simp
    · intro m _ hm
      simp [Ne.symm hm]
    · intro h; exact absurd (Finset.mem_range.mpr hx) h

/-- The sizes of the groups add up to `V^k`. -/
theorem sum_groupSize {k : ℕ} (hk : 0 < k) (V : ℕ) :
    ∑ m ∈ Finset.range V, ((m + 1) ^ k - m ^ k) = V ^ k := by
  induction V with
  | zero => simp [Nat.zero_pow hk]
  | succ V ih =>
    rw [Finset.sum_range_succ, ih]
    have : V ^ k ≤ (V + 1) ^ k := Nat.pow_le_pow_left (Nat.le_succ V) k
    omega

/-- Groups all of whose inputs satisfy `C` add up to at most the number of inputs satisfying
    `C`. -/
theorem sum_groups_le {k V : ℕ} (hk : 0 < k) (hV : 0 < V) (C : Input → Bool) (ok : ℕ → Bool)
    (h : ∀ m < V, ok m = true →
      ∀ x ∈ allInputs (List.replicate k V), x.foldl max 0 = m → C x = true) :
    ∑ m ∈ Finset.range V, (if ok m then (m + 1) ^ k - m ^ k else 0) ≤
      (allInputs (List.replicate k V)).countP C := by
  have hL : ∀ x ∈ allInputs (List.replicate k V), x.foldl max 0 < V :=
    fun x hx => label_lt hV (mem_allInputs_replicate.mp hx).2
  rw [countP_by_group hL C]
  apply Finset.sum_le_sum
  intro m hm
  rw [Finset.mem_range] at hm
  split
  · rename_i hok
    rw [← groupSize hk hm]
    apply le_of_eq
    apply List.countP_congr
    intro x hx
    simp only [Bool.and_eq_true, beq_iff_eq]
    exact ⟨fun hlab => ⟨h m hm hok x hx hlab, hlab⟩, fun h' => h'.2⟩
  · exact Nat.zero_le _

end LinearMaxK
