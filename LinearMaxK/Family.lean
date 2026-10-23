import LinearMaxK.Basic

/-!
# The family: linear max-of-k networks

`models/max2/model.py` of the pipeline with `n_ctx = k`: one-hot tokens at `k` positions, summed
over the positions, then three linear maps without bias, the embedding `E` (`d × V`), a linear
layer `L` (`d × d`) and the unembedding `U` (`V × d`). The label is the largest token.

Everything a network computes is in the matrix `M = U L E` (`V × V`): the logits of an input are the
sum of the columns of `M` at its tokens (`eval_family`). `IsLinearMaxK` recognises the graph
`scripts/export_network.py` writes for such a network, and `WF` says the weights have the shapes it
needs.
-/

namespace LinearMaxK

open CompactCheck

/-! ## The graph and the weights -/

def nE : String := "embedding.weight"
def nL : String := "linear.weight"
def nU : String := "unembedding.weight"

/-- The graph of a linear max-of-k network: the one-hot input, the sum over the positions, the
    embedding, the linear layer and the unembedding, with at least one position and one token. -/
def IsLinearMaxK (g : Graph) : Bool :=
  match g.nodes with
  | [.input, .sum 0 1, .linear 1 e none, .linear 2 l none, .linear 3 u none] =>
    e == nE && l == nL && u == nU && g.output == 4 && 0 < g.positions && 0 < g.values
  | _ => false

theorem isLinearMaxK_spec {g : Graph} (h : IsLinearMaxK g = true) :
    g.nodes = [.input, .sum 0 1, .linear 1 nE none, .linear 2 nL none, .linear 3 nU none] ∧
      g.output = 4 ∧ 0 < g.positions ∧ 0 < g.values := by
  unfold IsLinearMaxK at h
  split at h
  · rename_i e l u hn
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨he, hl⟩, hu⟩, ho⟩, hk⟩, hV⟩ := h
    subst he hl hu
    exact ⟨hn, ho, hk, hV⟩
  · simp at h

/-- Well-formed weights of width `d` for `V` tokens. -/
structure WF (w : Weights ℚ) (V d : ℕ) (tE tL tU : Tensor ℚ) : Prop where
  hE : List.lookup nE w = some tE
  hEs : tE.shape = [d, V]
  hEn : tE.data.size = d * V
  hL : List.lookup nL w = some tL
  hLs : tL.shape = [d, d]
  hLn : tL.data.size = d * d
  hU : List.lookup nU w = some tU
  hUs : tU.shape = [V, d]
  hUn : tU.data.size = V * d

/-- Entry `(j, t)` of `M = U L E`: the logit `j` that token `t` contributes from one position. -/
def Mval (tE tL tU : Tensor ℚ) (V d j t : ℕ) : ℚ :=
  ∑ a ∈ Finset.range d, tU.get (j * d + a) *
    ∑ b ∈ Finset.range d, tL.get (a * d + b) * tE.get (b * V + t)

/-! ## One layer at a time -/

theorem get_map_range {s : List ℕ} {f : ℕ → ℚ} {n j : ℕ} (hj : j < n) :
    (Tensor.mk s ((Array.range n).map f)).get j = f j := by
  simp [Tensor.get, Array.getD, hj]

theorem linearOp_spec {W t : Tensor ℚ} {out inn : ℕ}
    (hWs : W.shape = [out, inn]) (hWn : W.data.size = out * inn)
    (hts : t.shape = [1, inn]) (htn : t.data.size = inn) :
    ∃ r, linearOp W none t = some r ∧ r.shape = [1, out] ∧ r.data.size = out ∧
      ∀ j < out, r.get j = ∑ i ∈ Finset.range inn, W.get (j * inn + i) * t.get i := by
  refine ⟨⟨[1, out], (Array.range (1 * out)).map fun j =>
      ((List.range inn).map fun i => W.get (j % out * inn + i) * t.get (j / out * inn + i)).sum⟩,
    ?_, rfl, by simp, fun j hj => ?_⟩
  · unfold linearOp
    simp [hWs, hts, hWn, htn, shapeSize]
  · rw [get_map_range (by omega), sum_range_eq]
    simp [Nat.mod_eq_of_lt hj, Nat.div_eq_of_lt hj]

theorem linearOp_size {W t r : Tensor ℚ} {b : Option (Tensor ℚ)} {out inn : ℕ}
    (hWs : W.shape = [out, inn]) (h : linearOp W b t = some r) : W.data.size = out * inn := by
  unfold linearOp at h
  rw [Option.ite_none_right_eq_some] at h
  have hc := h.1
  simp only [hWs, Bool.and_eq_true, beq_iff_eq, List.getD_cons_zero, List.getD_cons_succ] at hc
  exact hc.1.1.2

theorem div_mod_pos {p l V : ℕ} (hl : l < V) : (p * V + l) / V = p ∧ (p * V + l) % V = l := by
  have hV : 0 < V := by omega
  constructor
  · rw [add_comm, Nat.add_mul_div_right _ _ hV, Nat.div_eq_of_lt hl, zero_add]
  · rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hl]

theorem pos_lt {p l k V : ℕ} (hp : p < k) (hl : l < V) : p * V + l < k * V := by
  have : (p + 1) * V ≤ k * V := Nat.mul_le_mul_right V hp
  rw [Nat.add_mul, Nat.one_mul] at this
  omega

theorem oneHot_spec {k V : ℕ} {x : Input} (hx : x.length = k) (hxV : ∀ t ∈ x, t < V) :
    ∃ oh : Tensor ℚ, oneHotInput k V x = some oh ∧ oh.shape = [1, k, V] ∧
      oh.data.size = k * V ∧
      ∀ p < k, ∀ l < V, oh.get (p * V + l) = if x.getD p 0 = l then 1 else 0 := by
  refine ⟨⟨[1, k, V], (Array.range (k * V)).map fun j =>
      if x.getD (j / V) 0 = j % V then 1 else 0⟩, ?_, rfl, by simp, fun p hp l hl => ?_⟩
  · unfold oneHotInput
    have hall : x.all (· < V) = true := List.all_eq_true.mpr fun t ht => decide_eq_true (hxV t ht)
    simp [hx, hall]
  · rw [get_map_range (pos_lt hp hl), (div_mod_pos hl).1, (div_mod_pos hl).2]

theorem sumOp_spec {t : Tensor ℚ} {k V : ℕ} (hts : t.shape = [1, k, V])
    (htn : t.data.size = k * V) :
    ∃ r, sumOp 1 t = some r ∧ r.shape = [1, V] ∧ r.data.size = V ∧
      ∀ l < V, r.get l = ∑ p ∈ Finset.range k, t.get (p * V + l) := by
  refine ⟨⟨[1, V], (Array.range (1 * V)).map fun j =>
      ((List.range k).map fun p => t.get ((j / V * k + p) * V + j % V)).sum⟩,
    ?_, rfl, by simp, fun l hl => ?_⟩
  · unfold sumOp
    simp [hts, htn, normDim, shapeSize, Nat.mul_comm]
  · rw [get_map_range (by omega), sum_range_eq]
    simp [Nat.div_eq_of_lt hl, Nat.mod_eq_of_lt hl]

/-! ## The logits are sums of columns of `M` -/

theorem getD_mem {x : List ℕ} {p : ℕ} (hp : p < x.length) : x.getD p 0 ∈ x := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp, Option.getD_some]
  exact List.getElem_mem hp

/-- The embedding of the summed one-hot input: the sum of the embedding's columns at the tokens. -/
theorem embed_sum {tE oh s : Tensor ℚ} {x : Input} {V b : ℕ} (hxV : ∀ t ∈ x, t < V)
    (hoh : ∀ p < x.length, ∀ l < V, oh.get (p * V + l) = if x.getD p 0 = l then 1 else 0)
    (hs : ∀ l < V, s.get l = ∑ p ∈ Finset.range x.length, oh.get (p * V + l)) :
    ∑ l ∈ Finset.range V, tE.get (b * V + l) * s.get l =
      (x.map fun t => tE.get (b * V + t)).sum := by
  have h1 : ∀ l ∈ Finset.range V, tE.get (b * V + l) * s.get l =
      ∑ p ∈ Finset.range x.length, if x.getD p 0 = l then tE.get (b * V + l) else 0 := by
    intro l hl
    rw [Finset.mem_range] at hl
    rw [hs l hl, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.mem_range] at hp
    rw [hoh p hp l hl]
    split <;> simp
  rw [Finset.sum_congr rfl h1, Finset.sum_comm, ← sum_getD_eq]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.mem_range] at hp
  have hmem : x.getD p 0 ∈ Finset.range V := Finset.mem_range.mpr (hxV _ (getD_mem hp))
  simp only [Finset.sum_ite_eq, hmem, ↓reduceIte]

/-- The network on a valid input `x`: its logit `j` is the sum of `M[j, t]` over the tokens `t`
    of `x`. -/
theorem eval_family {g : Graph} (hg : IsLinearMaxK g = true) {w : Weights ℚ} {d : ℕ}
    {tE tL tU : Tensor ℚ} (hw : WF w g.values d tE tL tU) {x : Input}
    (hx : x.length = g.positions) (hxV : ∀ t ∈ x, t < g.values) :
    ∃ out, evalGraph g w x = some out ∧ out.shape = [1, g.values] ∧
      out.data.size = g.values ∧
      ∀ j < g.values, out.get j = (x.map (Mval tE tL tU g.values d j)).sum := by
  obtain ⟨hn, ho, -, -⟩ := isLinearMaxK_spec hg
  obtain ⟨oh, h0, hohs, hohn, hoh⟩ := oneHot_spec hx hxV
  obtain ⟨s, hs, hss, hsn, hsg⟩ := sumOp_spec hohs hohn
  obtain ⟨e1, he1, he1s, he1n, he1g⟩ := linearOp_spec hw.hEs hw.hEn hss hsn
  obtain ⟨e2, he2, he2s, he2n, he2g⟩ := linearOp_spec hw.hLs hw.hLn he1s he1n
  obtain ⟨e3, he3, he3s, he3n, he3g⟩ := linearOp_spec hw.hUs hw.hUn he2s he2n
  refine ⟨e3, ?_, he3s, he3n, fun j hj => ?_⟩
  · simp [evalGraph, evalOps, evalOp, hn, ho, h0, hs, hw.hE, hw.hL, hw.hU, he1, he2, he3]
  · have h1 : ∀ b < d, e1.get b = (x.map fun t => tE.get (b * g.values + t)).sum := by
      intro b hb
      rw [he1g b hb]
      exact embed_sum hxV (hx ▸ hoh) (hx ▸ hsg)
    have h2 : ∀ a < d, e2.get a = (x.map fun t =>
        ∑ b ∈ Finset.range d, tL.get (a * d + b) * tE.get (b * g.values + t)).sum := by
      intro a ha
      rw [he2g a ha, ← sum_mul_list_sum]
      exact Finset.sum_congr rfl fun b hb => by rw [h1 b (Finset.mem_range.mp hb)]
    unfold Mval
    rw [he3g j hj, ← sum_mul_list_sum]
    exact Finset.sum_congr rfl fun a ha => by rw [h2 a (Finset.mem_range.mp ha)]

theorem evalGraph_of_singleOk {g : Graph} {w : Weights ℚ} {task : Task} {x : Input}
    (h : singleOk g w task x = true) : ∃ out, evalGraph g w x = some out := by
  unfold singleOk at h
  split at h
  · rename_i out hout; exact ⟨out, hout⟩
  · cases h

/-- Weights on which the network runs have the sizes their shapes say. -/
theorem wf_of_eval {g : Graph} (hg : IsLinearMaxK g = true) {w : Weights ℚ} {d : ℕ}
    {tE tL tU : Tensor ℚ} (hE : List.lookup nE w = some tE) (hEs : tE.shape = [d, g.values])
    (hL : List.lookup nL w = some tL) (hLs : tL.shape = [d, d])
    (hU : List.lookup nU w = some tU) (hUs : tU.shape = [g.values, d]) {x : Input}
    (hx : x.length = g.positions) (hxV : ∀ t ∈ x, t < g.values) {out : Tensor ℚ}
    (h : evalGraph g w x = some out) : WF w g.values d tE tL tU := by
  obtain ⟨hn, ho, -, -⟩ := isLinearMaxK_spec hg
  obtain ⟨oh, h0, hohs, hohn, -⟩ := oneHot_spec hx hxV
  obtain ⟨s, hs, -, -, -⟩ := sumOp_spec hohs hohn
  simp only [evalGraph, hn, evalOps, evalOp, h0, List.push_toArray, List.nil_append,
    List.size_toArray, List.length_cons, List.length_nil, zero_add, Order.lt_one_iff, getElem?_pos,
    List.getElem_toArray, List.getElem_cons_zero, hs, List.cons_append, Nat.reduceAdd,
    Order.lt_two_iff, Std.le_refl, List.getElem_cons_succ, hE, Nat.lt_add_one, hL, hU, ho] at h
  cases h1 : linearOp tE none s with
  | none => simp [h1] at h
  | some v1 =>
    cases h2 : linearOp tL none v1 with
    | none => simp [h1, h2] at h
    | some v2 =>
      cases h3 : linearOp tU none v2 with
      | none => simp [h1, h2, h3] at h
      | some v3 =>
        exact ⟨hE, hEs, linearOp_size hEs h1, hL, hLs, linearOp_size hLs h2, hU, hUs,
          linearOp_size hUs h3⟩

/-! ## The label, and what "correct" means here -/

theorem le_foldl_max_init : ∀ (x : List ℕ) (a : ℕ), a ≤ x.foldl max a
  | [], _ => le_rfl
  | t :: x, a => le_trans (le_max_left a t) (le_foldl_max_init x (max a t))

theorem le_foldl_max : ∀ {x : List ℕ} {t : ℕ} (a : ℕ), t ∈ x → t ≤ x.foldl max a
  | [], _, _, h => absurd h List.not_mem_nil
  | u :: x, t, a, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact le_trans (le_max_right a t) (le_foldl_max_init x _)
    · exact le_foldl_max (max a u) h

theorem foldl_max_le : ∀ {x : List ℕ} {a m : ℕ}, a ≤ m → (∀ t ∈ x, t ≤ m) → x.foldl max a ≤ m
  | [], _, _, ha, _ => ha
  | t :: x, a, _, ha, h =>
    foldl_max_le (x := x) (a := max a t) (max_le ha (h t List.mem_cons_self))
      fun u hu => h u (List.mem_cons_of_mem _ hu)

/-- The label of an input whose tokens are at most `m` and one of them `m`. -/
theorem label_eq {x : List ℕ} {m : ℕ} (hle : ∀ t ∈ x, t ≤ m) (hm : m ∈ x) : x.foldl max 0 = m :=
  le_antisymm (foldl_max_le (Nat.zero_le m) hle) (le_foldl_max 0 hm)

theorem label_lt {x : List ℕ} {V : ℕ} (hV : 0 < V) (hxV : ∀ t ∈ x, t < V) : x.foldl max 0 < V :=
  Nat.lt_of_le_of_lt (foldl_max_le (Nat.zero_le (V - 1)) fun t ht => by have := hxV t ht; omega)
    (by omega)

/-- On a valid input, the network is correct iff the logit of the largest token beats every other
    logit. -/
theorem correct_iff {g : Graph} (hg : IsLinearMaxK g = true) {w : Weights ℚ} {d : ℕ}
    {tE tL tU : Tensor ℚ} (hw : WF w g.values d tE tL tU) {x : Input}
    (hx : x.length = g.positions) (hxV : ∀ t ∈ x, t < g.values) :
    Correct g w (maxTask g.positions g.values) x ↔
      ∀ j < g.values, j ≠ x.foldl max 0 →
        (x.map (Mval tE tL tU g.values d j)).sum <
          (x.map (Mval tE tL tU g.values d (x.foldl max 0))).sum := by
  obtain ⟨-, -, -, hV⟩ := isLinearMaxK_spec hg
  obtain ⟨out, hout, hs, hn, hget⟩ := eval_family hg hw hx hxV
  have hlab : (maxTask g.positions g.values).label x = x.foldl max 0 := rfl
  have hl := label_lt hV hxV
  have hro := realOutput_of_evalGraph hout
  constructor
  · rintro ⟨out', hro', -, -, hlt⟩ j hj hne
    rw [hro] at hro'
    cases Option.some.inj hro'
    have := hlt j (by simp [hn, hj]) (by rw [hlab]; exact hne)
    rw [hlab, Tensor.get_map_cast, Tensor.get_map_cast, Rat.cast_lt, hget j hj,
      hget _ hl] at this
    exact this
  · intro h
    refine ⟨out.map (fun q : ℚ => (q : ℝ)), hro, by simp [Tensor.map, hs, hn], ?_, ?_⟩
    · simp [Tensor.map, hn, hlab, hl]
    · intro j hj hne
      simp only [Tensor.map, Array.size_map, hn] at hj
      rw [hlab] at hne ⊢
      rw [Tensor.get_map_cast, Tensor.get_map_cast, Rat.cast_lt, hget j hj, hget _ hl]
      exact h j hj hne

/-- On a valid input, `singleOk` decides `Correct`. -/
theorem singleOk_iff {g : Graph} (hg : IsLinearMaxK g = true) {w : Weights ℚ} {d : ℕ}
    {tE tL tU : Tensor ℚ} (hw : WF w g.values d tE tL tU) {x : Input}
    (hx : x.length = g.positions) (hxV : ∀ t ∈ x, t < g.values) :
    singleOk g w (maxTask g.positions g.values) x = true ↔
      Correct g w (maxTask g.positions g.values) x := by
  refine ⟨singleOk_correct _ _ _ _, fun hc => ?_⟩
  obtain ⟨-, -, -, hV⟩ := isLinearMaxK_spec hg
  obtain ⟨out, hout, hs, hn, hget⟩ := eval_family hg hw hx hxV
  have hl := label_lt hV hxV
  have hm := (correct_iff hg hw hx hxV).mp hc
  unfold singleOk
  rw [hout]
  simp only [hs, hn, beq_self_eq_true, Bool.true_and]
  have hlab : (maxTask g.positions g.values).label x = x.foldl max 0 := rfl
  rw [hlab]
  apply strictMaxAt_of (by simp [hn, hl])
  intro j hj hne
  simp only [Array.length_toList, hn] at hj
  have hgj : out.data.toList[j] = out.get j := by
    simp [Tensor.get, Array.getD, hn, hj]
  have hgl : vecGet out.data.toList (x.foldl max 0) = out.get (x.foldl max 0) := by
    simp [vecGet, Tensor.get, Array.getD, hn, hl, List.getD_eq_getElem?_getD]
  rw [hgj, hgl, hget j hj, hget _ hl]
  exact hm j hj hne

end LinearMaxK
