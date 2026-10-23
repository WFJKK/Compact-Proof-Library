import Common.Basic

/-!
# Sorted inputs and their reorderings

The symmetry entry checks one input of each class of reorderings: the sorted one.

* `sortedFrom V k lo`: the nondecreasing inputs of `k` tokens in `[lo, V)` (`mem_sortedFrom`), each
  once (`nodup_sortedFrom`); there are `(V - lo + k - 1).choose k` of them (`length_sortedFrom`).
* `mult V k x`: the number of inputs of `k` tokens in `[0, V)` that are reorderings of `x`
  (`countP_perm`), computed by choosing the first token.
* `sum_countP_le_of_pairwise`, `sum_countP_eq_of_pairwise`: counting over classes that share no
  element.
-/

namespace Symmetry

open CompactCheck

/-- The nondecreasing inputs of `k` tokens, each in `[lo, V)`. -/
def sortedFrom (V : ℕ) : ℕ → ℕ → List Input
  | 0, _ => [[]]
  | k + 1, lo => (List.range' lo (V - lo)).flatMap fun t => (sortedFrom V k t).map (t :: ·)

/-- The number of inputs of `k` tokens in `[0, V)` that are reorderings of `x`: a choice of the
    first token among those of `x`, then a reordering of the rest. -/
def mult (V : ℕ) : ℕ → List ℕ → ℕ
  | 0, _ => 1
  | k + 1, x =>
    (List.range V).foldr
      (fun t acc => Nat.add (if x.contains t then mult V k (x.erase t) else 0) acc) 0

theorem mult_succ (V k : ℕ) (x : List ℕ) :
    mult V (k + 1) x =
      ((List.range V).map fun t => if x.contains t then mult V k (x.erase t) else 0).sum := by
  rw [mult]
  generalize List.range V = l
  induction l with
  | nil => rfl
  | cons t l ih => rw [List.foldr_cons, List.map_cons, List.sum_cons, ih]; rfl

/-! ## Sorted inputs -/

theorem mem_sortedFrom {V : ℕ} : ∀ {k lo : ℕ} {x : Input},
    x ∈ sortedFrom V k lo ↔ x.length = k ∧ x.Pairwise (· ≤ ·) ∧ ∀ t ∈ x, lo ≤ t ∧ t < V
  | 0, lo, x => by
    simp only [sortedFrom, List.mem_singleton]
    constructor
    · rintro rfl; simp
    · rintro ⟨h, -, -⟩; exact List.eq_nil_of_length_eq_zero h
  | k + 1, lo, x => by
    simp only [sortedFrom, List.mem_flatMap, List.mem_range'_1, List.mem_map]
    constructor
    · rintro ⟨t, ⟨hlo, htV⟩, y, hy, rfl⟩
      obtain ⟨hyl, hys, hyr⟩ := mem_sortedFrom.mp hy
      refine ⟨by simp [hyl], List.pairwise_cons.mpr ⟨fun u hu => (hyr u hu).1, hys⟩, ?_⟩
      intro u hu
      rcases List.mem_cons.mp hu with rfl | hu
      · exact ⟨hlo, by omega⟩
      · exact ⟨le_trans hlo (hyr u hu).1, (hyr u hu).2⟩
    · rintro ⟨hl, hs, hr⟩
      cases x with
      | nil => simp at hl
      | cons t y =>
        obtain ⟨hty, hys⟩ := List.pairwise_cons.mp hs
        have ht := hr t List.mem_cons_self
        refine ⟨t, ⟨ht.1, by omega⟩, y, mem_sortedFrom.mpr ⟨by simpa using hl, hys, fun u hu =>
          ⟨hty u hu, (hr u (List.mem_cons_of_mem _ hu)).2⟩⟩, rfl⟩

theorem nodup_sortedFrom (V : ℕ) : ∀ (k lo : ℕ), (sortedFrom V k lo).Nodup
  | 0, _ => List.nodup_singleton _
  | k + 1, lo => by
    simp only [sortedFrom]
    refine List.nodup_flatMap.mpr ⟨fun t _ => (nodup_sortedFrom V k t).map List.cons_injective, ?_⟩
    refine (List.nodup_range' (s := lo) (n := V - lo)).imp fun {a b} hab => ?_
    simp only [List.disjoint_left, List.mem_map]
    rintro _ ⟨y, -, rfl⟩ ⟨z, -, hz⟩
    exact hab (List.cons_eq_cons.mp hz).1.symm

theorem length_sortedFrom (V : ℕ) : ∀ (k lo : ℕ),
    (sortedFrom V k lo).length = (V - lo + k - 1).choose k
  | 0, _ => by simp [sortedFrom]
  | k + 1, lo => by
    suffices h : ∀ n lo, V - lo = n → (sortedFrom V (k + 1) lo).length = (n + k).choose (k + 1) by
      rw [h (V - lo) lo rfl, show V - lo + (k + 1) - 1 = V - lo + k by omega]
    intro n
    induction n with
    | zero => intro lo h; simp [sortedFrom, h]
    | succ n ih =>
      intro lo h
      have hsplit : (sortedFrom V (k + 1) lo).length =
          (sortedFrom V k lo).length + (sortedFrom V (k + 1) (lo + 1)).length := by
        simp only [sortedFrom, h, List.range'_succ, List.flatMap_cons, List.length_append,
          List.length_map, show V - (lo + 1) = n by omega]
      rw [hsplit, length_sortedFrom V k lo, ih (lo + 1) (by omega), h,
        show n + 1 + k - 1 = n + k by omega, show n + 1 + k = n + k + 1 by omega,
        Nat.choose_succ_succ]

/-! ## Reorderings -/

theorem countP_perm {V : ℕ} : ∀ (k : ℕ) (x : List ℕ), x.length = k → (∀ t ∈ x, t < V) →
    (allInputs (List.replicate k V)).countP (fun y => y.isPerm x) = mult V k x
  | 0, x, hx, _ => by
    rw [List.eq_nil_of_length_eq_zero hx]
    simp [allInputs, mult, List.isPerm_iff]
  | k + 1, x, hx, hxV => by
    simp only [List.replicate_succ, allInputs, List.countP_flatMap, Function.comp_def,
      List.countP_map, mult_succ]
    congr 1
    refine List.map_congr_left fun t _ => ?_
    by_cases ht : t ∈ x
    · have hlen : (x.erase t).length = k := by rw [List.length_erase_of_mem ht]; omega
      rw [← countP_perm k (x.erase t) hlen fun u hu => hxV u (List.mem_of_mem_erase hu)]
      simp only [List.contains_iff_mem.mpr ht, ↓reduceIte]
      refine List.countP_congr fun y _ => ?_
      simp only [List.isPerm_iff, List.cons_perm_iff_perm_erase, ht, true_and]
    · have : x.contains t = false := by simpa using ht
      simp only [this, Bool.false_eq_true, ↓reduceIte, List.countP_eq_zero]
      intro y _
      simp only [List.isPerm_iff, List.cons_perm_iff_perm_erase, ht, false_and,
        not_false_eq_true]

/-! ## Counting over classes that share no element -/

theorem countP_split {α : Type} (L : List α) (p q : α → Bool) :
    L.countP p = L.countP (fun x => p x && q x) + L.countP (fun x => p x && !q x) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.countP_cons, ih]
    cases p a <;> cases q a <;> simp <;> omega

/-- Over classes `Q s` that pairwise share no element of `L`, the counts of `P` add up to at most
    the count of `P` in `L`. -/
theorem sum_countP_le_of_pairwise {α β : Type} (L : List α) (Q : β → α → Bool) (P : α → Bool) :
    ∀ (S : List β), S.Pairwise (fun a b => ∀ y ∈ L, Q a y = true → Q b y = false) →
      (S.map fun s => L.countP fun y => Q s y && P y).sum ≤ L.countP P
  | [], _ => by simp
  | s :: S, h => by
    obtain ⟨hs, hS⟩ := List.pairwise_cons.mp h
    have ih := sum_countP_le_of_pairwise L Q (fun y => P y && !Q s y) S hS
    have hcongr : (S.map fun s' => L.countP fun y => Q s' y && P y) =
        (S.map fun s' => L.countP fun y => Q s' y && (P y && !Q s y)) := by
      refine List.map_congr_left fun s' hs' => List.countP_congr fun y hy => ?_
      cases hq : Q s' y
      · simp
      · have : Q s y = false := by
          cases hqs : Q s y
          · rfl
          · rw [hs s' hs' y hy hqs] at hq; cases hq
        simp [this]
    have hsplit := countP_split L P (Q s)
    have hcomm : L.countP (fun y => Q s y && P y) = L.countP (fun y => P y && Q s y) :=
      List.countP_congr fun y _ => by simp [Bool.and_comm]
    rw [List.map_cons, List.sum_cons, hcongr]
    omega

end Symmetry
