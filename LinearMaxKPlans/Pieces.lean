import LinearMaxK.Groups

/-!
# Pieces of groups

A plan certifies inputs piece by piece. The piece `⟨m, lo, hi⟩` is the set of inputs whose largest
token is `m` and whose smallest token lies in `[lo, hi]`: the whole group of `m` is `⟨m, 0, m⟩`, the
inputs of the group whose tokens are all at least `lo` are `⟨m, lo, m⟩`.

* `countP_mem`: a piece has `tailSize k m lo - tailSize k m (hi + 1)` inputs, where
  `tailSize k m a = (m + 1 - a)^k - (m - a)^k` counts the inputs with largest token `m` and every
  token at least `a`.
* `planOk`: every piece has `lo ≤ hi ≤ m < V`, and two pieces of one group have disjoint ranges.
  Then no input is in two pieces, and the pieces' counts of correct inputs add up to at most the
  number of correct inputs (`sum_countP_le`).
-/

namespace LinearMaxKPlans

open CompactCheck Common LinearMaxK

/-- The inputs whose largest token is `m` and whose smallest token is in `[lo, hi]`. -/
structure Piece where
  m : ℕ
  lo : ℕ
  hi : ℕ

/-- Membership in a piece. -/
def Piece.mem (p : Piece) (x : Input) : Bool :=
  (x.foldl max 0 == p.m) && x.all (fun t => Nat.ble p.lo t) && x.any (fun t => Nat.ble t p.hi)

/-- The number of inputs with largest token `m` and every token at least `a`. -/
def tailSize (k m a : ℕ) : ℕ := Nat.pow (m + 1 - a) k - Nat.pow (m - a) k

/-- The number of inputs in a piece. -/
def Piece.size (k : ℕ) (p : Piece) : ℕ := tailSize k p.m p.lo - tailSize k p.m (p.hi + 1)

/-- `lo ≤ hi ≤ m < V`. -/
def Piece.valid (V : ℕ) (p : Piece) : Bool :=
  Nat.ble p.lo p.hi && Nat.ble p.hi p.m && Nat.blt p.m V

/-- Two pieces share no input: different groups, or disjoint ranges. -/
def Piece.apart (p q : Piece) : Bool :=
  !Nat.beq p.m q.m || Nat.blt p.hi q.lo || Nat.blt q.hi p.lo

/-- `p` is apart from every piece of `qs`. -/
def apartAll (p : Piece) : List Piece → Bool
  | [] => true
  | q :: qs => p.apart q && apartAll p qs

/-- A valid plan: valid pieces, pairwise apart. -/
def planOk (V : ℕ) : List Piece → Bool
  | [] => true
  | p :: ps => p.valid V && apartAll p ps && planOk V ps

/-! ## Membership -/

theorem mem_iff {p : Piece} {x : Input} (hx : x ≠ []) :
    p.mem x = true ↔ (∀ t ∈ x, t ≤ p.m) ∧ (∃ t ∈ x, p.m ≤ t) ∧ (∀ t ∈ x, p.lo ≤ t) ∧
      ∃ t ∈ x, t ≤ p.hi := by
  simp only [Piece.mem, Bool.and_eq_true, beq_iff_eq, label_eq_iff hx, List.all_eq_true,
    List.any_eq_true, Nat.ble_eq, and_assoc]

theorem not_mem_of_apart {p q : Piece} (h : p.apart q = true) {x : Input} (hx : x ≠ [])
    (hp : p.mem x = true) : q.mem x = false := by
  rw [Bool.eq_false_iff]
  intro hq
  obtain ⟨hpm, ⟨t1, ht1, hpm'⟩, hplo, t2, ht2, hphi⟩ := (mem_iff hx).mp hp
  obtain ⟨hqm, ⟨t3, ht3, hqm'⟩, hqlo, t4, ht4, hqhi⟩ := (mem_iff hx).mp hq
  simp only [Piece.apart, Bool.or_eq_true, Bool.not_eq_true', Nat.blt_eq] at h
  rcases h with (h | h) | h
  · exact Nat.ne_of_beq_eq_false h
      (le_antisymm (le_trans hpm' (hqm t1 ht1)) (le_trans hqm' (hpm t3 ht3)))
  · have := hqlo t2 ht2; omega
  · have := hplo t4 ht4; omega

/-! ## Counting -/

theorem countP_range_between (V a b : ℕ) :
    (List.range V).countP (fun t => decide (a ≤ t ∧ t < b)) = min V b - a := by
  induction V with
  | zero => simp
  | succ V ih =>
    rw [List.range_succ, List.countP_append, ih]
    simp only [List.countP_cons, List.countP_nil, decide_eq_true_eq]
    split <;> omega

/-- Every token in `[a, b)`. -/
def allIn (a b : ℕ) (x : Input) : Bool := x.all fun t => decide (a ≤ t ∧ t < b)

/-- `(b - a)^k` inputs have every token in `[a, b)`. -/
theorem countP_allIn : ∀ (k : ℕ) {V a b : ℕ}, b ≤ V →
    (allInputs (List.replicate k V)).countP (allIn a b) = (b - a) ^ k
  | 0, V, a, b, _ => by simp [allInputs, allIn]
  | k + 1, V, a, b, hb => by
    simp only [allIn, List.replicate_succ, allInputs, List.countP_flatMap, Function.comp_def,
      List.countP_map, List.all_cons]
    have : ∀ t, (allInputs (List.replicate k V)).countP
        (fun y => decide (a ≤ t ∧ t < b) && y.all fun u => decide (a ≤ u ∧ u < b)) =
        if decide (a ≤ t ∧ t < b) then (b - a) ^ k else 0 := by
      intro t
      by_cases ht : a ≤ t ∧ t < b
      · simp only [ht]
        exact countP_allIn k hb
      · simp [ht]
    simp only [this, sum_ite_const, countP_range_between V a b, Nat.min_eq_right hb, Nat.pow_succ,
      Nat.mul_comm]

theorem mem_allInputs_ne_nil {k V : ℕ} (hk : 0 < k) {x : Input}
    (hx : x ∈ allInputs (List.replicate k V)) : x ≠ [] := by
  rintro rfl
  have := (mem_allInputs_replicate.mp hx).1
  simp only [List.length_nil] at this
  omega

/-- `tailSize k m a` inputs have largest token `m` and every token at least `a`. -/
theorem countP_tail {k V m : ℕ} (hk : 0 < k) (hm : m < V) (a : ℕ) :
    (allInputs (List.replicate k V)).countP
      (fun x => (x.foldl max 0 == m) && x.all fun t => Nat.ble a t) = tailSize k m a := by
  have hA := countP_allIn k (V := V) (a := a) (b := m + 1) hm
  have hB := countP_allIn k (V := V) (a := a) (b := m) (by omega)
  have hsplit := countP_split (allInputs (List.replicate k V)) (allIn a (m + 1)) (allIn a m)
  have hAB : (allInputs (List.replicate k V)).countP (fun x => allIn a (m + 1) x && allIn a m x) =
      (allInputs (List.replicate k V)).countP (allIn a m) := by
    refine List.countP_congr fun x _ => ?_
    simp only [allIn, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨fun t ht => by have := h t ht; omega, h⟩⟩
  have hG : (allInputs (List.replicate k V)).countP
      (fun x => (x.foldl max 0 == m) && x.all fun t => Nat.ble a t) =
      (allInputs (List.replicate k V)).countP (fun x => allIn a (m + 1) x && !allIn a m x) := by
    refine List.countP_congr fun x hx => ?_
    have hne := mem_allInputs_ne_nil hk hx
    simp only [allIn, beq_iff_eq, label_eq_iff hne, Bool.and_eq_true, Bool.not_eq_eq_eq_not,
      Bool.not_true, List.all_eq_false, List.all_eq_true, decide_eq_true_eq, Nat.ble_eq]
    constructor
    · rintro ⟨⟨hle, t, ht, hmt⟩, hlo⟩
      exact ⟨fun u hu => ⟨hlo u hu, by have := hle u hu; omega⟩, t, ht, fun h => by omega⟩
    · rintro ⟨hin, t, ht, hnot⟩
      refine ⟨⟨fun u hu => by have := (hin u hu).2; omega, t, ht, ?_⟩, fun u hu => (hin u hu).1⟩
      have := hin t ht
      by_contra hlt
      exact hnot ⟨this.1, by omega⟩
  rw [hG, tailSize, Nat.pow_eq, Nat.pow_eq]
  omega

/-- A valid piece has `Piece.size k p` inputs. -/
theorem countP_mem {k V : ℕ} (hk : 0 < k) {p : Piece} (hp : p.valid V = true) :
    (allInputs (List.replicate k V)).countP p.mem = p.size k := by
  simp only [Piece.valid, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hp
  obtain ⟨⟨hlh, hhm⟩, hmV⟩ := hp
  have hT := countP_tail (V := V) hk hmV p.lo
  have hT' := countP_tail (V := V) hk hmV (p.hi + 1)
  have hsplit := countP_split (allInputs (List.replicate k V))
    (fun x => (x.foldl max 0 == p.m) && x.all fun t => Nat.ble p.lo t)
    (fun x => x.all fun t => Nat.ble (p.hi + 1) t)
  have h1 : (allInputs (List.replicate k V)).countP (fun x =>
      ((x.foldl max 0 == p.m) && x.all fun t => Nat.ble p.lo t) &&
        x.all fun t => Nat.ble (p.hi + 1) t) =
      (allInputs (List.replicate k V)).countP
        (fun x => (x.foldl max 0 == p.m) && x.all fun t => Nat.ble (p.hi + 1) t) := by
    refine List.countP_congr fun x _ => ?_
    simp only [Bool.and_eq_true, List.all_eq_true, Nat.ble_eq]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, fun t ht => by have := h.2 t ht; omega⟩, h.2⟩⟩
  have h2 : (allInputs (List.replicate k V)).countP p.mem =
      (allInputs (List.replicate k V)).countP (fun x =>
        ((x.foldl max 0 == p.m) && x.all fun t => Nat.ble p.lo t) &&
          !x.all fun t => Nat.ble (p.hi + 1) t) := by
    refine List.countP_congr fun x _ => ?_
    simp only [Piece.mem, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
      List.all_eq_false, List.any_eq_true, Nat.ble_eq]
    constructor
    · rintro ⟨h, t, ht, hth⟩; exact ⟨h, t, ht, by omega⟩
    · rintro ⟨h, t, ht, hth⟩; exact ⟨h, t, ht, by omega⟩
  rw [h2, Piece.size]
  omega

/-! ## Disjoint pieces -/

theorem apartAll_spec {p : Piece} : ∀ {qs : List Piece}, apartAll p qs = true →
    ∀ q ∈ qs, p.apart q = true
  | [], _, _, hq => absurd hq List.not_mem_nil
  | q :: qs, h, r, hr => by
    simp only [apartAll, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hr with rfl | hr
    · exact h.1
    · exact apartAll_spec h.2 r hr

/-- In a valid plan, the pieces' counts of inputs with a property add up to at most the count of
    inputs with the property. -/
theorem sum_countP_le {k V : ℕ} (hk : 0 < k) :
    ∀ (plan : List Piece), planOk V plan = true → ∀ (P : Input → Bool),
      (plan.map fun p => (allInputs (List.replicate k V)).countP fun x => p.mem x && P x).sum ≤
        (allInputs (List.replicate k V)).countP P
  | [], _, _ => by simp
  | p :: ps, h, P => by
    simp only [planOk, Bool.and_eq_true] at h
    obtain ⟨⟨-, hap⟩, hps⟩ := h
    have ih := sum_countP_le hk ps hps (fun x => P x && !p.mem x)
    have hcongr : (ps.map fun q => (allInputs (List.replicate k V)).countP
        fun x => q.mem x && P x) =
        (ps.map fun q => (allInputs (List.replicate k V)).countP
          fun x => q.mem x && (P x && !p.mem x)) := by
      refine List.map_congr_left fun q hq => List.countP_congr fun x hx => ?_
      have hne := mem_allInputs_ne_nil hk hx
      have hpq := apartAll_spec hap q hq
      cases hqx : q.mem x
      · simp
      · have : p.mem x = false := by
          cases hpx : p.mem x
          · rfl
          · rw [not_mem_of_apart hpq hne hpx] at hqx; cases hqx
        simp [this]
    have hsplit := countP_split (allInputs (List.replicate k V)) P p.mem
    rw [List.map_cons, List.sum_cons, hcongr]
    have hcomm : (allInputs (List.replicate k V)).countP (fun x => p.mem x && P x) =
        (allInputs (List.replicate k V)).countP (fun x => P x && p.mem x) :=
      List.countP_congr fun x _ => by simp [Bool.and_comm]
    omega

end LinearMaxKPlans
