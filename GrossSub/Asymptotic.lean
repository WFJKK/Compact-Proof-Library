import GrossSub.Check
import Common.Asymptotic

/-!
# Entry 9: the bill as the sizes grow

`check_billed` gives the bill of Gross et al.'s sub-cubic proofs as `subBill err eu gap V n d h`,
for any of their 100 configurations (`err`, `eu`) and any plan of gaps `gap`. This module reads
it: the tables and the steps before the blocks (`tableCost`, bounded for every method in
`tableCost_le`), one block per largest token (`subBill_eq`), and bounds that hold for every plan.

* In the vocabulary, at fixed `n`, `d`, `h` and whatever the plans, the bill is `Θ(V²)`
  (`subBill_le`, `mul_le_subBill`, `isTheta_sq`): Gross et al.'s "sub-cubic",
  `O(d_vocab² n_ctx² + d_vocab² d_model)` in their Table 1.
* In the context length, at fixed `V ≥ 1`, `d`, `h`, the bill is `Θ(n²)` (`isTheta_sq_n`), and
  the quadratic term is `V (n - 1)(n - 2)`, the sorting networks of the positional errors, one per
  query token: a factor `V` below their `d_vocab² n_ctx²`. The classes cost `O(n V²)`: for a
  largest rank and a number of other positions, one test per query rank, each `O(1)` from the
  prefix sums of the sorted bounds.

The plan enters the bill only through which classes it lets in (`rowCost`), at most `λ + 1` per
largest rank `λ` and number of positions, each `classTestCost 2 2 + 1 = 74` operations; the bounds
below take them all in, so they hold for every plan.
-/

namespace GrossSub

open Common Finset Asymptotics Filter

/-! ## The bill, read -/

/-- Everything the checker computes before the blocks: the tables, step 1 (`errCost`), the sorted
    positional errors (`sortedCost`), the paths, the direct path (`eupuCost`) and the running
    extrema. -/
def tableCost (err eu V n d h : ℕ) : ℕ :=
  h * d + V * d + V * d + n * d + d * d * h + errCost err V d h + h * n * d + d * n * h +
    V * n * d + V * sortedCost n + d * d * h + d * V * d + V * V * d + n * V * d + V * V * d +
    eupuCost eu V d + V * ((V - 1) + (V - 1)) + V * (2 * (V - 1) + 1) + (V - 1) + 1

/-- The bill is the tables plus one block per largest token. -/
theorem subBill_eq (err eu : ℕ) (gap : ℕ → ℕ → ℕ → ℕ) (V n d h : ℕ) :
    subBill err eu gap V n d h =
      tableCost err eu V n d h + ∑ lam ∈ range V, subBlockCost V n gap lam := by
  unfold subBill tableCost
  rw [list_sum_range]
  ring

/-! ## Step 1, for every method -/

theorem facR_le_d (d h : ℕ) : facR d h ≤ d := by unfold facR; split <;> omega

theorem facCost_le (V d h : ℕ) : facCost V d h ≤ 2 * V * h * d + V * d * d := by
  unfold facCost
  split <;> linarith [Nat.zero_le (V * h * d), Nat.zero_le (V * d * d)]

theorem svdSplitCost_eq (V r : ℕ) : svdSplitCost V r = 6 * r * V + V + r + 2 * V * V := by
  unfold svdSplitCost; ring

theorem psdCost_le (r : ℕ) : psdCost r ≤ r ^ 3 + 7 * r * r + 3 * r := by
  unfold psdCost
  have := Nat.mul_le_mul_left r (show 6 * (r - 1) + 2 ≤ 6 * r + 2 by omega)
  nlinarith

theorem svdBoundCost_le (V r : ℕ) :
    svdBoundCost V r ≤ 2 * r * r * V + 5 * r ^ 3 + 17 * r * r + 6 * r + 4 := by
  unfold svdBoundCost
  have := psdCost_le r
  nlinarith

theorem rowBoundCost_le (rows k cols : ℕ) :
    rowBoundCost rows k cols ≤ 3 * k * cols + k + 2 * cols + 4 * k * rows + rows + 1 := by
  unfold rowBoundCost
  have := Nat.mul_le_mul_left k (show 2 * (cols - 1) + 1 ≤ 2 * cols + 1 by omega)
  have : 2 * (cols - 1) + 1 ≤ 2 * cols + 1 := by omega
  nlinarith

/-- The bound of step 1, uniform over the six methods. -/
def errBound (V d h : ℕ) : ℕ :=
  V * V * (d + h + 10) + V * (4 * d * h + 3 * d * d + 39 * d + 7 * h + 22) +
    (5 * d ^ 3 + 21 * d * d + 17 * d * h + 8 * d + 2 * h + 6)

theorem errACost_le (err V d h : ℕ) :
    errACost err V d h ≤ V * V * (d + 4) + V * (2 * h * d + 3 * d * d + 13 * d + 5) +
      (5 * d ^ 3 + 17 * d * d + 8 * d + 5) := by
  unfold errACost
  have hr := facR_le_d d h
  set r := facR d h with hr_def
  have h1 := facCost_le V d h
  rw [svdSplitCost_eq]
  have hrr : r * r ≤ d * d := Nat.mul_le_mul hr hr
  have hr3 : r ^ 3 ≤ d ^ 3 := Nat.pow_le_pow_left hr 3
  have hrV : r * V ≤ d * V := Nat.mul_le_mul_right V hr
  have hrrV : r * r * V ≤ d * d * V := Nat.mul_le_mul_right V hrr
  have hVVr : V * V * r ≤ V * V * d := Nat.mul_le_mul_left _ hr
  have hb := svdBoundCost_le V r
  have hrow := rowBoundCost_le V r V
  have hrV' : 3 * r * V ≤ 3 * d * V := by nlinarith
  have hrV'' : 4 * r * V ≤ 4 * d * V := by nlinarith
  have hV1 : V * (2 * (V - 1) + 1) ≤ 2 * V * V + V := by
    have := Nat.mul_le_mul_left V (show 2 * (V - 1) + 1 ≤ 2 * V + 1 by omega)
    nlinarith
  split_ifs <;>
    nlinarith [Nat.zero_le (V * V * d), Nat.zero_le (V * V), Nat.zero_le (V * d * d),
      Nat.zero_le (V * d), Nat.zero_le V, Nat.zero_le (d ^ 3), Nat.zero_le (d * d), Nat.zero_le d,
      Nat.zero_le (V * h * d)]

theorem errBCost_eq (V d h : ℕ) : errBCost V d h = 2 * V * h * d + V * V * h := by
  unfold errBCost; ring

theorem subCost_eq (V d h : ℕ) :
    subCost V d h = 16 * V * d + 4 * V + 6 * h * d + 2 * d + 4 * d * d + 6 * V * V := by
  unfold subCost; ring

theorem breakCost_le (V d h : ℕ) :
    breakCost V d h ≤ 4 * V * d * h + 14 * d * V + 7 * h * V + 11 * V + 2 * d + h + 3 := by
  unfold breakCost
  have h1 := rowBoundCost_le V d V
  have h2 := rowBoundCost_le V h V
  nlinarith

theorem recCost_le (V d h : ℕ) :
    recCost V d h ≤ 9 * V * d + 7 * V + 11 * d * h + 2 * d + h + 3 := by
  unfold recCost
  have hV : 2 * (V - 1) + 1 ≤ 2 * V + 1 := by omega
  have h1 := Nat.mul_le_mul_left d hV
  nlinarith

theorem errCCost_le (err V d h : ℕ) :
    errCCost err V d h ≤ 6 * V * V + V * (4 * d * h + 39 * d + 7 * h + 22) +
      (4 * d * d + 17 * h * d + 6 * d + 2 * h + 6) := by
  unfold errCCost
  rw [subCost_eq]
  have h1 := breakCost_le V d h
  have h2 := recCost_le V d h
  split_ifs <;> nlinarith [Nat.zero_le (V * d * h), Nat.zero_le (V * d), Nat.zero_le (V * h),
    Nat.zero_le V, Nat.zero_le (d * h), Nat.zero_le d, Nat.zero_le h]

/-- **Step 1, bounded** for every method: `O(V² (d + h) + V (d h + d²) + d³)`. -/
theorem errCost_le (err V d h : ℕ) : errCost err V d h ≤ errBound V d h := by
  unfold errCost errBound
  have hA := errACost_le err V d h
  have hB := errBCost_eq V d h
  have hC := errCCost_le err V d h
  split_ifs <;> nlinarith [Nat.zero_le (V * V * h), Nat.zero_le (V * V * d), Nat.zero_le (V * V),
    Nat.zero_le (V * d * h), Nat.zero_le (V * d * d), Nat.zero_le (V * d), Nat.zero_le (V * h),
    Nat.zero_le V, Nat.zero_le (d ^ 3), Nat.zero_le (d * d), Nat.zero_le (d * h), Nat.zero_le d,
    Nat.zero_le h]

/-! ## The other steps -/

/-- The sorting network and the prefix sums of one query: `(n - 1)(n - 2) + 8 (n - 1)`. -/
theorem sortedCost_eq (n : ℕ) : sortedCost n = (n - 1) * (n - 1 - 1) + 8 * (n - 1) := by
  unfold sortedCost
  rw [sortCost_eq]
  ring

theorem sortedCost_le (n : ℕ) : sortedCost n ≤ n * n + 8 * n := by
  rw [sortedCost_eq]
  have : (n - 1) * (n - 1 - 1) ≤ n * n := Nat.mul_le_mul (Nat.sub_le n 1) (by omega)
  omega

theorem le_sortedCost (n : ℕ) : (n - 1) * (n - 2) ≤ sortedCost n := by
  rw [sortedCost_eq]
  have : n - 1 - 1 = n - 2 := by omega
  rw [this]
  omega

theorem eupuCost_le (eu V d : ℕ) : eupuCost eu V d ≤ 7 * V * d + 2 * V * V + 2 * V + d + 1 := by
  unfold eupuCost
  have h1 := Nat.mul_le_mul_left d (show 2 * (V - 1) + 1 ≤ 2 * V + 1 by omega)
  have h2 := Nat.mul_le_mul_left V (show 2 * (V - 1) + 1 ≤ 2 * V + 1 by omega)
  have h3 : V * (V - 1) ≤ V * V := Nat.mul_le_mul_left V (Nat.sub_le V 1)
  have h4 : V - 1 ≤ V := Nat.sub_le V 1
  split_ifs <;> nlinarith [Nat.zero_le (V * d), Nat.zero_le (V * V), Nat.zero_le V, Nat.zero_le d]

/-- The bound of the tables and the steps before the blocks. -/
def tableBound (V n d h : ℕ) : ℕ :=
  V * V * (3 * d + h + 16) +
    V * (4 * d * h + 4 * d * d + 2 * n * d + n * n + 8 * n + 48 * d + 7 * h + 26) +
    (5 * d ^ 3 + 2 * d * d * h + 21 * d * d + 18 * d * h + 2 * h * n * d + n * d + 9 * d + 2 * h +
      8)

/-- **The tables, bounded** for every method: `O(V² (d + h) + V (d h + d² + n d + n²) + d³)`. -/
theorem tableCost_le (err eu V n d h : ℕ) : tableCost err eu V n d h ≤ tableBound V n d h := by
  unfold tableCost tableBound
  have h1 := errCost_le err V d h
  unfold errBound at h1
  have h2 := Nat.mul_le_mul_left V (sortedCost_le n)
  have h3 := eupuCost_le eu V d
  have h4 : V * ((V - 1) + (V - 1)) ≤ 2 * V * V := by
    have := Nat.mul_le_mul_left V (show (V - 1) + (V - 1) ≤ 2 * V by omega)
    nlinarith
  have h5 : V * (2 * (V - 1) + 1) ≤ 2 * V * V + V := by
    have := Nat.mul_le_mul_left V (show 2 * (V - 1) + 1 ≤ 2 * V + 1 by omega)
    nlinarith
  have h6 : V - 1 ≤ V := Nat.sub_le V 1
  linarith

/-! ## The blocks, for every plan -/

theorem endConstsCost_le (V : ℕ) : endConstsCost V ≤ 2 * V + 10 := by
  unfold endConstsCost; omega

/-- A row of a block: the two endpoints' constants and at most `λ + 1` class tests, each 74. -/
theorem rowCost_le {V lam : ℕ} (gap : ℕ → ℕ → ℕ → ℕ) (c0 : ℕ) (hlam : lam < V) :
    rowCost V lam gap c0 ≤ 78 * V + 22 := by
  unfold rowCost
  split
  · have h1 := endConstsCost_le V
    have h2 : ∑ rq ∈ range (lam + 1), (if valid gap rq lam (c0 + 1) = true then
        classTestCost 2 2 + 1 else 0) ≤ (lam + 1) * 74 :=
      sum_range_le_mul fun rq _ => by split <;> simp [classTestCost]
    rw [list_sum_range]
    omega
  · omega

/-- One block, for a largest token of rank `λ < V`: `O(n V)` whatever the plan. -/
theorem subBlockCost_le {V lam : ℕ} (n : ℕ) (gap : ℕ → ℕ → ℕ → ℕ) (hlam : lam < V) :
    subBlockCost V n gap lam ≤ 80 * n * V + 10 * V + 22 * n := by
  unfold subBlockCost
  rw [list_sum_range]
  have h1 : ∑ c0 ∈ range (n - 1), rowCost V lam gap c0 ≤ (n - 1) * (78 * V + 22) :=
    sum_range_le_mul fun c0 _ => rowCost_le gap c0 hlam
  have h2 : (n - 1) * (78 * V + 22) ≤ n * (78 * V + 22) := Nat.mul_le_mul_right _ (Nat.sub_le n 1)
  have h3 : V * (n + (n - 1)) ≤ V * (2 * n) := Nat.mul_le_mul_left _ (by omega)
  have h4 : V - 1 ≤ V := Nat.sub_le V 1
  have h5 : V - 1 - 1 ≤ V := by omega
  have h6 : 1 ≤ V := by omega
  linarith

/-- One block costs at least `n V`: the pessimised positional path of every output. -/
theorem le_subBlockCost (V n : ℕ) (gap : ℕ → ℕ → ℕ → ℕ) (lam : ℕ) :
    V * n ≤ subBlockCost V n gap lam := by
  unfold subBlockCost
  have : V * n ≤ V * (n + (n - 1)) := Nat.mul_le_mul_left _ (by omega)
  omega

theorem blocks_le (V n : ℕ) (gap : ℕ → ℕ → ℕ → ℕ) :
    ∑ lam ∈ range V, subBlockCost V n gap lam ≤ V * (80 * n * V + 10 * V + 22 * n) :=
  sum_range_le_mul fun _ hlam => subBlockCost_le n gap hlam

theorem le_blocks (V n : ℕ) (gap : ℕ → ℕ → ℕ → ℕ) :
    V * (V * n) ≤ ∑ lam ∈ range V, subBlockCost V n gap lam :=
  mul_le_sum_range fun lam _ => le_subBlockCost V n gap lam

/-! ## The bill -/

/-- **The bill, bounded above**, for every configuration and every plan. -/
theorem subBill_le (err eu : ℕ) (gap : ℕ → ℕ → ℕ → ℕ) (V n d h : ℕ) :
    subBill err eu gap V n d h ≤ tableBound V n d h + V * V * (80 * n + 10) + 22 * n * V := by
  rw [subBill_eq]
  have h1 := tableCost_le err eu V n d h
  have h2 := blocks_le V n gap
  nlinarith

/-- **Quadratic in `V`**: the blocks alone cost `n V²`. -/
theorem mul_le_subBill (err eu : ℕ) (gap : ℕ → ℕ → ℕ → ℕ) (V n d h : ℕ) :
    n * V * V ≤ subBill err eu gap V n d h := by
  rw [subBill_eq]
  have := le_blocks V n gap
  nlinarith

/-- The tables alone cost `V²` for `V ≥ 1`: the running extrema of the rows. -/
theorem sq_le_subBill (err eu : ℕ) (gap : ℕ → ℕ → ℕ → ℕ) {V : ℕ} (n d h : ℕ) (hV : 1 ≤ V) :
    V * V ≤ subBill err eu gap V n d h := by
  rw [subBill_eq]
  unfold tableCost
  have : V * V ≤ V * (2 * (V - 1) + 1) := Nat.mul_le_mul_left V (by omega)
  omega

/-- **Quadratic in `n`**: the sorting networks alone cost `V (n - 1)(n - 2)`. -/
theorem sort_le_subBill (err eu : ℕ) (gap : ℕ → ℕ → ℕ → ℕ) (V n d h : ℕ) :
    V * ((n - 1) * (n - 2)) ≤ subBill err eu gap V n d h := by
  rw [subBill_eq]
  unfold tableCost
  have := Nat.mul_le_mul_left V (le_sortedCost n)
  omega

/-! ## The asymptotic statements -/

/-- The bound of `subBill_le`, by powers of `V`: its coefficients. -/
def coefV2 (n d h : ℕ) : ℕ := (3 * d + h + 16) + (80 * n + 10)
def coefV1 (n d h : ℕ) : ℕ :=
  (4 * d * h + 4 * d * d + 2 * n * d + n * n + 8 * n + 48 * d + 7 * h + 26) + 22 * n
def coefV0 (n d h : ℕ) : ℕ :=
  5 * d ^ 3 + 2 * d * d * h + 21 * d * d + 18 * d * h + 2 * h * n * d + n * d + 9 * d + 2 * h + 8

theorem bound_eq_V (V n d h : ℕ) :
    tableBound V n d h + V * V * (80 * n + 10) + 22 * n * V =
      V * V * coefV2 n d h + V * coefV1 n d h + coefV0 n d h := by
  unfold tableBound coefV2 coefV1 coefV0; ring

/-- The bound of `subBill_le`, by powers of `n`: the quadratic term is `V n²`. -/
def coefN1 (V d h : ℕ) : ℕ := V * (2 * d + 8) + (2 * h * d + d) + V * V * 80 + 22 * V
def coefN0 (V d h : ℕ) : ℕ :=
  V * V * (3 * d + h + 16) + V * (4 * d * h + 4 * d * d + 48 * d + 7 * h + 26) +
    (5 * d ^ 3 + 2 * d * d * h + 21 * d * d + 18 * d * h + 9 * d + 2 * h + 8) + V * V * 10

theorem bound_eq_n (V n d h : ℕ) :
    tableBound V n d h + V * V * (80 * n + 10) + 22 * n * V =
      n * n * V + n * coefN1 V d h + coefN0 V d h := by
  unfold tableBound coefN1 coefN0; ring

/-- At fixed `n`, `d`, `h`, with any plan for each `V`, the bill is `Θ(V²)`. -/
theorem isTheta_sq (err eu n d h : ℕ) (gap : ℕ → ℕ → ℕ → ℕ → ℕ) :
    (fun V => (subBill err eu (gap V) V n d h : ℝ)) =Θ[atTop] fun V => (V : ℝ) ^ 2 := by
  have key := isTheta_of_le (fun V => subBill err eu (gap V) V n d h) (fun V => V ^ 2)
    (coefV2 n d h + coefV1 n d h + coefV0 n d h) 1 1
    (fun V hV => by
      show subBill err eu (gap V) V n d h ≤ (coefV2 n d h + coefV1 n d h + coefV0 n d h) * V ^ 2
      have h1 := subBill_le err eu (gap V) V n d h
      rw [bound_eq_V] at h1
      exact h1.trans (quad_le (coefV2 n d h) (coefV1 n d h) (coefV0 n d h) hV))
    (fun V hV => by
      show V ^ 2 ≤ 1 * subBill err eu (gap V) V n d h
      have := sq_le_subBill err eu (gap V) n d h hV
      have h4 : V ^ 2 = V * V := by ring
      rw [h4]
      omega)
  exact isTheta_cast_pow _ 2 key

/-- At fixed `V ≥ 1`, `d`, `h`, with any plan for each `n`, the bill is `Θ(n²)`. -/
theorem isTheta_sq_n (err eu V d h : ℕ) (gap : ℕ → ℕ → ℕ → ℕ → ℕ) (hV : 1 ≤ V) :
    (fun n => (subBill err eu (gap n) V n d h : ℝ)) =Θ[atTop] fun n => (n : ℝ) ^ 2 := by
  have key := isTheta_of_le (fun n => subBill err eu (gap n) V n d h) (fun n => n ^ 2)
    (V + coefN1 V d h + coefN0 V d h) 4 4
    (fun n hn => by
      show subBill err eu (gap n) V n d h ≤ (V + coefN1 V d h + coefN0 V d h) * n ^ 2
      have h1 := subBill_le err eu (gap n) V n d h
      rw [bound_eq_n] at h1
      exact h1.trans (quad_le V (coefN1 V d h) (coefN0 V d h) (by omega)))
    (fun n hn => by
      show n ^ 2 ≤ 4 * subBill err eu (gap n) V n d h
      have h1 := sort_le_subBill err eu (gap n) V n d h
      have h2 : n ^ 2 ≤ 4 * ((n - 1) * (n - 2)) := by
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
        simp only [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega]
        nlinarith
      have h3 : (n - 1) * (n - 2) ≤ V * ((n - 1) * (n - 2)) := Nat.le_mul_of_pos_left _ hV
      omega)
  exact isTheta_cast_pow _ 2 key

end GrossSub
