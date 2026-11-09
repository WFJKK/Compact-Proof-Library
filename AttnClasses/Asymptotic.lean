import AttnClasses.Sound
import Common.Asymptotic

/-!
# Entry 6: the bill as the sizes grow

`check_billed` gives the bill of the class method as `bill V n d h`. This module reads it: the
tables (`tableCost`) and the classes (`vtCost`), and their growth with explicit constants.

* In the vocabulary, at fixed `n`, `d`, `h`: for `n ≥ 3` the bill is `Θ(V³)` (`bill_le`,
  `pow_three_le_vtCost`, `isTheta_pow_three`), from the running minima of each position, which
  every pair of a query rank and a label rank pays for, and from the classes. For `n = 2` it is
  `Θ(V²)` (`isTheta_sq_two`): a class is one input, and all but the tables cost `O(1)` per input.
* In the context length, at fixed `V ≥ 1`, `d`, `h`, the bill is `Θ(n 2ⁿ)` (`isTheta_mul_two_pow`):
  a class is keyed by a set of positions, so there are `2^(n - 1)` of them per pair of ranks, and
  each pays for its set bits. Like entry 7 (and unlike Gross et al.'s `O(n²)` sorting), the method
  is exponential in the context length; the two agree for the zoo's `n ≤ 4`.
-/

namespace AttnClasses

open Common Finset Asymptotics Filter

/-! ## The bill, read -/

/-- Everything the checker computes before the classes: the tables of queries, keys, scores,
    paths and margins, and the bounds on `exp`. -/
def tableCost (V n d h : ℕ) : ℕ :=
  h * d + V * d + V * h * d + V * h * d + V * V * h + n * h * d + V * n * h + d * d * h +
    d * V * d + V * V * d + n * V * d + 1 * V * d + V * V * d + V * (V + margCost V) +
    V * (n * (V + margCost V)) + V * (V * (n * 4))

theorem bill_eq (V n d h : ℕ) : bill V n d h = tableCost V n d h + vtCost V n := by
  unfold bill tableCost; ring

theorem margCost_le (V : ℕ) : margCost V ≤ 4 * V := by unfold margCost; omega

/-- The tables, bounded: `O(V² (d + h + n) + V (d h + d² + n (d + h)) + d h (d + n))`. -/
theorem tableCost_le (V n d h : ℕ) :
    tableCost V n d h ≤ V * V * (h + 2 * d + 9 * n + 5) +
      V * (2 * h * d + d * d + n * d + n * h + 2 * d) + (h * d + n * h * d + d * d * h) := by
  unfold tableCost
  have h1 := margCost_le V
  have h2 : V * (V + margCost V) ≤ V * (5 * V) := Nat.mul_le_mul_left V (by omega)
  have h3 : V * (n * (V + margCost V)) ≤ V * (n * (5 * V)) :=
    Nat.mul_le_mul_left V (Nat.mul_le_mul_left n (by omega))
  nlinarith

/-- The classes, as a double sum. -/
theorem vtCost_eq (V n : ℕ) :
    vtCost V n = ∑ ρq ∈ range V, ∑ lam ∈ range V, if ρq ≤ lam then blockCost n ρq lam else 0 := by
  unfold vtCost
  rw [list_sum_range]
  exact sum_congr rfl fun ρq _ => list_sum_range _ V

/-! ## Upper bounds -/

/-- One pattern costs at most `(λ + 1)(n + 1)`: its set bits, and the running minimum of each
    other position, `λ` deep. -/
theorem patCost_le (n ρq lam pat : ℕ) : patCost n ρq lam pat ≤ (lam + 1) * (n + 1) := by
  unfold patCost
  have h1 := length_filter_range_le pat.testBit (n - 1)
  have h2 := length_filter_range_le (fun p => !pat.testBit p) (n - 1)
  have h3 : lam * (((List.range (n - 1)).filter fun p => !pat.testBit p).length + 1) ≤
      lam * (n + 1) := Nat.mul_le_mul_left lam (by omega)
  have h4 : n - 1 ≤ n := Nat.sub_le n 1
  split_ifs <;> nlinarith [Nat.zero_le (lam * n), Nat.zero_le lam]

/-- The constant of the `n`-dependence of a block: `2^(n - 1) (n + 1) + 9 n + 4`. -/
def classBound (n : ℕ) : ℕ := 2 ^ (n - 1) * (n + 1) + 9 * n + 4

theorem blockCost_le (n ρq lam : ℕ) : blockCost n ρq lam ≤ (lam + 1) * classBound n := by
  unfold blockCost classBound
  rw [list_sum_range]
  have h1 : ∑ pat ∈ range (2 ^ (n - 1)), patCost n ρq lam pat ≤
      2 ^ (n - 1) * ((lam + 1) * (n + 1)) :=
    sum_range_le_mul fun pat _ => patCost_le n ρq lam pat
  have h2 : (n - 1) * (lam * 4 + (lam - 1)) ≤ n * (5 * lam) :=
    Nat.mul_le_mul (Nat.sub_le n 1) (by omega)
  have h3 : 4 + (n - 1) * 4 ≤ 4 * n + 4 := by omega
  split_ifs <;> nlinarith [Nat.zero_le (2 ^ (n - 1) * (lam + 1) * (n + 1)), Nat.zero_le (n * lam),
    Nat.zero_le (2 ^ (n - 1) * (n + 1))]

theorem vtCost_le (V n : ℕ) : vtCost V n ≤ V ^ 3 * classBound n := by
  rw [vtCost_eq]
  have hin : ∀ ρq, ∑ lam ∈ range V, (if ρq ≤ lam then blockCost n ρq lam else 0) ≤
      V ^ 2 * classBound n := by
    intro ρq
    calc ∑ lam ∈ range V, (if ρq ≤ lam then blockCost n ρq lam else 0)
        ≤ ∑ lam ∈ range V, (lam + 1) * classBound n :=
          sum_range_le_sum_range fun lam _ => by
            split
            · exact blockCost_le n ρq lam
            · exact Nat.zero_le _
      _ = (∑ lam ∈ range V, (lam + 1)) * classBound n := by rw [sum_mul]
      _ ≤ V ^ 2 * classBound n := Nat.mul_le_mul_right _ (sum_succ_le_sq V)
  calc ∑ ρq ∈ range V, ∑ lam ∈ range V, (if ρq ≤ lam then blockCost n ρq lam else 0)
      ≤ V * (V ^ 2 * classBound n) := sum_range_le_mul fun ρq _ => hin ρq
    _ = V ^ 3 * classBound n := by ring

/-- **The bill, bounded above.** -/
theorem bill_le (V n d h : ℕ) :
    bill V n d h ≤ V * V * (h + 2 * d + 9 * n + 5) + V * (2 * h * d + d * d + n * d + n * h + 2 * d)
      + (h * d + n * h * d + d * d * h) + V ^ 3 * (2 ^ (n - 1) * (n + 1) + 9 * n + 4) := by
  rw [bill_eq]
  have h1 := tableCost_le V n d h
  have h2 := vtCost_le V n
  unfold classBound at h2
  omega

/-! ## Lower bounds -/

/-- For `n ≥ 3`, every pair of a query rank and a label rank `λ` pays `4 (n - 1) λ` for the
    running minima of the other positions. -/
theorem le_blockCost {n : ℕ} (ρq lam : ℕ) (hn : 3 ≤ n) :
    4 * (n - 1) * lam ≤ blockCost n ρq lam := by
  unfold blockCost
  rw [ite_eq_left (Or.inr hn)]
  have : 4 * (n - 1) * lam ≤ (n - 1) * (lam * 4 + (lam - 1)) := by
    have : 4 * (n - 1) * lam = (n - 1) * (lam * 4) := by ring
    rw [this]
    exact Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
  omega

/-- **Cubic in `V`** for `n ≥ 3`: the classes cost at least `(n - 1) V³` when `V ≥ 2`. -/
theorem pow_three_le_vtCost {V n : ℕ} (hn : 3 ≤ n) (hV : 2 ≤ V) :
    (n - 1) * V ^ 3 ≤ vtCost V n := by
  rw [vtCost_eq, sum_comm]
  have h1 : ∀ lam, lam < V → (lam + 1) * (4 * (n - 1) * lam) ≤
      ∑ ρq ∈ range V, (if ρq ≤ lam then blockCost n ρq lam else 0) := by
    intro lam hlam
    calc (lam + 1) * (4 * (n - 1) * lam)
        = ∑ ρq ∈ range (lam + 1), (if ρq ≤ lam then 4 * (n - 1) * lam else 0) := by
          rw [sum_congr rfl fun ρq hρq => ite_eq_left (by have := mem_range.mp hρq; omega)]
          simp
      _ ≤ ∑ ρq ∈ range V, (if ρq ≤ lam then 4 * (n - 1) * lam else 0) :=
          sum_le_sum_of_subset (range_mono hlam)
      _ ≤ ∑ ρq ∈ range V, (if ρq ≤ lam then blockCost n ρq lam else 0) :=
          sum_range_le_sum_range fun ρq _ => by
            split
            · exact le_blockCost ρq lam hn
            · exact le_refl _
  have h2 : ∑ lam ∈ range V, (lam + 1) * (4 * (n - 1) * lam) ≤
      ∑ lam ∈ range V, ∑ ρq ∈ range V, (if ρq ≤ lam then blockCost n ρq lam else 0) :=
    sum_range_le_sum_range h1
  have h3 : ∑ lam ∈ range V, (lam + 1) * (4 * (n - 1) * lam) =
      (n - 1) * (4 * ∑ lam ∈ range V, (lam + 1) * lam) := by
    rw [mul_sum, mul_sum]
    exact sum_congr rfl fun lam _ => by ring
  have h4 := pow_three_le_sum_succ_mul hV
  have h5 : (n - 1) * V ^ 3 ≤ (n - 1) * (4 * ∑ lam ∈ range V, (lam + 1) * lam) :=
    Nat.mul_le_mul_left _ h4
  omega

theorem pow_three_le_bill {V n : ℕ} (d h : ℕ) (hn : 3 ≤ n) (hV : 2 ≤ V) :
    (n - 1) * V ^ 3 ≤ bill V n d h := by
  rw [bill_eq]
  have := pow_three_le_vtCost hn hV (V := V)
  omega

/-- The tables alone cost `V²`: the margins of the direct path. -/
theorem sq_le_bill (V n d h : ℕ) : V * V ≤ bill V n d h := by
  rw [bill_eq]
  unfold tableCost
  have : V * V ≤ V * (V + margCost V) := Nat.mul_le_mul_left V (Nat.le_add_right _ _)
  omega

/-- When the query holds the label, every pattern pays at least its set bits. -/
theorem setBits_le_patCost (n lam pat : ℕ) : setBits (n - 1) pat ≤ patCost n lam lam pat := by
  unfold patCost setBits
  rw [ite_eq_right (by simp)]
  split <;> omega

/-- **Exponential in `n`**: the classes of the pairs with the query holding the label pay
    `V (n - 1) 2^(n - 2)` for their patterns' set bits. -/
theorem exp_le_vtCost (V n : ℕ) : V * ((n - 1) * 2 ^ (n - 1)) ≤ 2 * vtCost V n := by
  rw [vtCost_eq]
  have h1 : ∀ ρq, ρq < V → pcSum (n - 1) ≤
      ∑ lam ∈ range V, (if ρq ≤ lam then blockCost n ρq lam else 0) := by
    intro ρq hρq
    calc pcSum (n - 1) ≤ blockCost n ρq ρq := by
          unfold blockCost pcSum
          rw [list_sum_range]
          have := sum_range_le_sum_range (V := 2 ^ (n - 1)) fun pat _ => setBits_le_patCost n ρq pat
          omega
      _ = (if ρq ≤ ρq then blockCost n ρq ρq else 0) := by simp
      _ ≤ ∑ lam ∈ range V, (if ρq ≤ lam then blockCost n ρq lam else 0) :=
          single_le_sum (f := fun lam => if ρq ≤ lam then blockCost n ρq lam else 0)
            (fun _ _ => Nat.zero_le _) (mem_range.mpr hρq)
  have h2 := mul_le_sum_range h1
  have h3 := two_mul_pcSum (n - 1)
  nlinarith

/-! ## Two positions -/

/-- With two positions a class is one input: a block costs `10`, or `7 λ + 10` when the query
    holds the label. -/
theorem blockCost_two_le (ρq lam : ℕ) :
    blockCost 2 ρq lam ≤ 10 + (if ρq = lam then 7 * lam else 0) := by
  unfold blockCost patCost
  simp [List.range_succ]
  split_ifs <;> omega

theorem vtCost_two_le (V : ℕ) : vtCost V 2 ≤ 17 * V * V := by
  rw [vtCost_eq]
  have hin : ∀ ρq, ρq < V → ∑ lam ∈ range V, (if ρq ≤ lam then blockCost 2 ρq lam else 0) ≤
      17 * V := by
    intro ρq hρq
    calc ∑ lam ∈ range V, (if ρq ≤ lam then blockCost 2 ρq lam else 0)
        ≤ ∑ lam ∈ range V, (10 + if ρq = lam then 7 * lam else 0) :=
          sum_range_le_sum_range fun lam _ => by
            split
            · exact blockCost_two_le ρq lam
            · exact Nat.zero_le _
      _ = 10 * V + (if ρq ∈ range V then 7 * ρq else 0) := by
          rw [sum_add_distrib, sum_const, card_range, smul_eq_mul, sum_ite_eq, Nat.mul_comm]
      _ ≤ 17 * V := by
          rw [ite_eq_left (mem_range.mpr hρq)]
          omega
  calc ∑ ρq ∈ range V, ∑ lam ∈ range V, (if ρq ≤ lam then blockCost 2 ρq lam else 0)
      ≤ V * (17 * V) := sum_range_le_mul hin
    _ = 17 * V * V := by ring

/-! ## The asymptotic statements -/

/-- At fixed `n ≥ 3`, `d`, `h`, the bill is `Θ(V³)`. -/
theorem isTheta_pow_three {n : ℕ} (d h : ℕ) (hn : 3 ≤ n) :
    (fun V => (bill V n d h : ℝ)) =Θ[atTop] fun V => (V : ℝ) ^ 3 := by
  have key := isTheta_of_le (fun V => bill V n d h) (fun V => V ^ 3)
    ((h + 2 * d + 9 * n + 5) + (2 * h * d + d * d + n * d + n * h + 2 * d) +
      (h * d + n * h * d + d * d * h) + (2 ^ (n - 1) * (n + 1) + 9 * n + 4)) 1 2
    (fun V hV => by
      show bill V n d h ≤ _ * V ^ 3
      have h1 := bill_le V n d h
      have h2 : V * V ≤ V ^ 3 := by
        calc V * V = V * V * 1 := by ring
          _ ≤ V * V * V := by gcongr; omega
          _ = V ^ 3 := by ring
      have h3 : V ≤ V ^ 3 := by
        calc V = V * 1 * 1 := by ring
          _ ≤ V * V * V := by gcongr <;> omega
          _ = V ^ 3 := by ring
      have h4 := Nat.mul_le_mul_right (h + 2 * d + 9 * n + 5) h2
      have h5 := Nat.mul_le_mul_right (2 * h * d + d * d + n * d + n * h + 2 * d) h3
      have h6 : h * d + n * h * d + d * d * h ≤ V ^ 3 * (h * d + n * h * d + d * d * h) :=
        Nat.le_mul_of_pos_left _ (by positivity)
      linarith)
    (fun V hV => by
      show V ^ 3 ≤ 1 * bill V n d h
      have := pow_three_le_bill d h hn hV (V := V)
      have : V ^ 3 ≤ (n - 1) * V ^ 3 := Nat.le_mul_of_pos_left _ (by omega)
      omega)
  exact isTheta_cast_pow _ 3 key

/-- At `n = 2` and fixed `d`, `h`, the bill is `Θ(V²)`. -/
theorem isTheta_sq_two (d h : ℕ) :
    (fun V => (bill V 2 d h : ℝ)) =Θ[atTop] fun V => (V : ℝ) ^ 2 := by
  have key := isTheta_of_le (fun V => bill V 2 d h) (fun V => V ^ 2)
    ((h + 2 * d + 9 * 2 + 5) + (2 * h * d + d * d + 2 * d + 2 * h + 2 * d) +
      (h * d + 2 * h * d + d * d * h) + 17) 1 1
    (fun V hV => by
      show bill V 2 d h ≤ _ * V ^ 2
      rw [bill_eq]
      have h1 := tableCost_le V 2 d h
      have h2 := vtCost_two_le V
      have h3 : V * (2 * h * d + d * d + 2 * d + 2 * h + 2 * d) ≤
          V * V * (2 * h * d + d * d + 2 * d + 2 * h + 2 * d) :=
        Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left V hV)
      have h4 : h * d + 2 * h * d + d * d * h ≤ V * V * (h * d + 2 * h * d + d * d * h) :=
        Nat.le_mul_of_pos_left _ (by positivity)
      have h5 : V ^ 2 = V * V := by ring
      rw [h5]
      linarith)
    (fun V hV => by
      show V ^ 2 ≤ 1 * bill V 2 d h
      have := sq_le_bill V 2 d h
      have h5 : V ^ 2 = V * V := by ring
      omega)
  exact isTheta_cast_pow _ 2 key

/-- At fixed `V ≥ 1`, `d`, `h`, the bill is `Θ(n 2ⁿ)`. -/
theorem isTheta_mul_two_pow {V : ℕ} (d h : ℕ) (hV : 1 ≤ V) :
    (fun n => (bill V n d h : ℝ)) =Θ[atTop] fun n => (n : ℝ) * 2 ^ n := by
  have key := isTheta_of_le (fun n => bill V n d h) (fun n => n * 2 ^ n)
    ((V * V * (h + 2 * d + 5) + V * (2 * h * d + d * d + 2 * d) + (h * d + d * d * h)) +
      (V * V * 9 + V * (d + h) + h * d) + V ^ 3 * 14) 8 2
    (fun n hn => by
      show bill V n d h ≤ _ * (n * 2 ^ n)
      have h1 := bill_le V n d h
      have h0 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      have h2 : 1 ≤ n * 2 ^ n := by
        calc 1 = 1 * 1 := rfl
          _ ≤ n * 2 ^ n := Nat.mul_le_mul (by omega) h0
      have h3 : n ≤ n * 2 ^ n := Nat.le_mul_of_pos_right _ (by omega)
      have h4 : 2 ^ (n - 1) * (n + 1) ≤ n * 2 ^ n := by
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        simp only [Nat.add_sub_cancel, pow_succ]
        nlinarith [Nat.zero_le (2 ^ m)]
      have h5 : V ^ 3 * (2 ^ (n - 1) * (n + 1) + 9 * n + 4) ≤ V ^ 3 * (14 * (n * 2 ^ n)) :=
        Nat.mul_le_mul_left _ (by omega)
      have h6 : V * V * (h + 2 * d + 9 * n + 5) ≤
          (V * V * (h + 2 * d + 5) + V * V * 9) * (n * 2 ^ n) := by
        have : V * V * (h + 2 * d + 9 * n + 5) =
            V * V * (h + 2 * d + 5) * 1 + V * V * 9 * n := by ring
        rw [this]
        nlinarith [Nat.zero_le (V * V * (h + 2 * d + 5)), Nat.zero_le (V * V * 9)]
      have h7 : V * (2 * h * d + d * d + n * d + n * h + 2 * d) ≤
          (V * (2 * h * d + d * d + 2 * d) + V * (d + h)) * (n * 2 ^ n) := by
        have : V * (2 * h * d + d * d + n * d + n * h + 2 * d) =
            V * (2 * h * d + d * d + 2 * d) * 1 + V * (d + h) * n := by ring
        rw [this]
        nlinarith [Nat.zero_le (V * (2 * h * d + d * d + 2 * d)), Nat.zero_le (V * (d + h))]
      have h8 : h * d + n * h * d + d * d * h ≤ ((h * d + d * d * h) + h * d) * (n * 2 ^ n) := by
        have : h * d + n * h * d + d * d * h = (h * d + d * d * h) * 1 + h * d * n := by ring
        rw [this]
        nlinarith [Nat.zero_le (h * d + d * d * h), Nat.zero_le (h * d)]
      linarith)
    (fun n hn => by
      show n * 2 ^ n ≤ 8 * bill V n d h
      rw [bill_eq]
      have h1 := exp_le_vtCost V n
      have h2 : n * 2 ^ n ≤ 4 * ((n - 1) * 2 ^ (n - 1)) := by
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        simp only [Nat.add_sub_cancel, pow_succ]
        nlinarith [Nat.zero_le (2 ^ m)]
      have h3 : (n - 1) * 2 ^ (n - 1) ≤ V * ((n - 1) * 2 ^ (n - 1)) := Nat.le_mul_of_pos_left _ hV
      omega)
  exact isTheta_cast_mul_two_pow _ key

end AttnClasses
