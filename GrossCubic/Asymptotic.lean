import GrossCubic.Check
import Common.Asymptotic

/-!
# Entry 7: the bill as the sizes grow

`check_billed` gives the bill of Gross et al.'s cubic proof as `bill V n d h`, a right-nested sum
shaped by the proof that computes it. This module reads it: the bill is the tables plus one block
per largest token (`bill_eq`), each closed form is stated (`tableCost_eq_V`, `tableCost_eq_n`),
and the growth is proved with explicit constants.

* In the vocabulary, at fixed `n`, `d`, `h`, the bill is `Θ(V³)` (`bill_le`, `pow_three_le_bill`,
  `isTheta_pow_three`): Gross et al.'s "cubic", `O(d_vocab³ n_ctx²)` in their Table 1.
* In the context length, at fixed `V ≥ 2`, the bill is `Θ(n 2ⁿ)` (`bill_le`, `exp_le_bill`,
  `isTheta_mul_two_pow`), not `O(n²)`: the checker finds the worst positions of a non-maximal
  token by trying every pattern of positions (`kverd` runs over the `2^(n - 1)` patterns), where
  their code sorts the positional scores. The two agree for `n ≤ 4`, the sizes of the zoo; at
  `n = 10` the patterns cost 12 times the sorted version would, at `n = 16` 600 times.

The lower bound in `n` rests on counting bits (`Common.two_mul_pcSum`): over all patterns of `L`
bits the set bits add up to `L 2^(L - 1)`.
-/

namespace GrossCubic

open Common Finset Asymptotics Filter

/-! ## The bill, read -/

/-- Everything the checker computes before the blocks: the tables of queries, keys, scores and
    paths, the bounds on `exp`, and the numbers `1, ..., V - 1`. -/
def tableCost (V n d h : ℕ) : ℕ :=
  h * d + V * d + 2 * V * h * d + V * V * h + n * h * d + V * n * h + d * d * h + d * V * d +
    2 * V * V * d + n * V * d + 3 * V * V + 3 * V * n + (V - 1)

/-- The bill is the tables plus one block per largest token. -/
theorem bill_eq (V n d h : ℕ) :
    bill V n d h = tableCost V n d h + ∑ lam ∈ range V, blockCost V n lam := by
  unfold bill tableCost
  rw [list_sum_range]
  ring

/-- The tables, by powers of `V`. -/
theorem tableCost_eq_V (V n d h : ℕ) :
    tableCost V n d h = V * V * (h + 2 * d + 3) +
      V * (d + 2 * h * d + n * h + d * d + n * d + 3 * n) + (h * d + n * h * d + d * d * h) +
      (V - 1) := by
  unfold tableCost; ring

/-- The tables, by powers of `n`: affine. -/
theorem tableCost_eq_n (V n d h : ℕ) :
    tableCost V n d h = n * (h * d + V * h + V * d + 3 * V) +
      (h * d + V * d + 2 * V * h * d + V * V * h + d * d * h + d * V * d + 2 * V * V * d + 3 * V * V
        + (V - 1)) := by
  unfold tableCost; ring

/-! ## Upper bounds -/

theorem queryOnlyCost_le (V n : ℕ) : queryOnlyCost V n ≤ 13 * V + 2 * n + 11 := by
  unfold queryOnlyCost; omega

theorem length_inPat_le (L pat : ℕ) : (inPat L pat).length ≤ L :=
  length_filter_range_le _ L

theorem length_patsOf_le (L c : ℕ) : (patsOf L c).length ≤ 2 ^ L := by
  unfold patsOf
  simpa [Nat.pow_eq] using length_filter_range_le (fun pat => (inPat L pat).length == c) (2 ^ L)

/-- The verdicts of one non-maximal token cost at most `(n - 1) (2ⁿ + 2)`: the `2^(n - 1)`
    patterns, each summed over at most `n - 1` positions, and one maximum per number of
    positions. -/
theorem kverdCost_le {n ncs : ℕ} (h : ncs ≤ n - 1) : kverdCost n ncs ≤ (n - 1) * (2 ^ n + 2) := by
  rcases n with _ | n
  · have : ncs = 0 := by omega
    subst this; simp [kverdCost, inPat]
  unfold kverdCost
  simp only [Nat.pow_eq, Nat.add_sub_cancel, list_sum_range]
  have h1 : ∑ pat ∈ range (2 ^ n), ((inPat n pat).length - 1) ≤ 2 ^ n * n :=
    sum_range_le_mul fun pat _ => by have := length_inPat_le n pat; omega
  have h2 : ∑ c' ∈ range ncs, ((patsOf n (c' + 1)).length - 1 + 2) ≤ ncs * (2 ^ n + 1) :=
    sum_range_le_mul fun c' _ => by
      have := length_patsOf_le n (c' + 1)
      have := Nat.one_le_two_pow (n := n)
      omega
  have h3 : ncs * (2 ^ n + 1) ≤ n * (2 ^ n + 1) := Nat.mul_le_mul_right _ h
  have h4 : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
  rw [h4]
  linarith

theorem patCountCost_le (lam c' L : ℕ) : patCountCost lam c' L ≤ 2 * L + lam := by
  unfold patCountCost; split <;> omega

/-- The constant of the `n`-dependence of a class: `n 2ⁿ + 9 n + 8`. -/
def classBound (n : ℕ) : ℕ := n * 2 ^ n + 9 * n + 8

/-- The inputs with the query of one rank and non-maximal tokens cost at most
    `(λ + 1) classBound n`. -/
theorem withNonmaxCost_le {n lam ncs : ℕ} (h : ncs ≤ n - 1) :
    withNonmaxCost n lam ncs ≤ (lam + 1) * classBound n := by
  unfold withNonmaxCost classBound
  rw [list_sum_range]
  have h1 := kverdCost_le h
  have h2 : ∑ c' ∈ range ncs, patCountCost lam c' lam ≤ ncs * (3 * lam) :=
    sum_range_le_mul fun c' _ => by have := patCountCost_le lam c' lam; omega
  have h3 : ncs * (3 * lam) ≤ (n - 1) * (3 * lam) := Nat.mul_le_mul_right _ h
  have hn : n - 1 ≤ n := Nat.sub_le n 1
  have h4 : (n - 1) * (2 ^ n + 2) ≤ n * 2 ^ n + 2 * n := by
    have := Nat.mul_le_mul_right (2 ^ n + 2) hn
    linarith
  have h5 : (n - 1) * (3 * lam) ≤ 3 * n * lam := by
    have := Nat.mul_le_mul_right (3 * lam) hn
    linarith
  have h6 : lam * kverdCost n ncs ≤ lam * (n * 2 ^ n + 2 * n) :=
    Nat.mul_le_mul_left _ (h1.trans h4)
  have h7 : n - 1 - 1 ≤ n := by omega
  have h8 : (lam + 1) * ((n - 1) * 3) ≤ (lam + 1) * (3 * n) :=
    Nat.mul_le_mul_left _ (by omega)
  linarith [Nat.zero_le (lam * n), Nat.zero_le (n * 2 ^ n)]

theorem ncsOf_le (n lam rq : ℕ) : ncsOf n lam rq ≤ n - 1 := by
  unfold ncsOf; split <;> omega

/-- One block, for a largest token of rank `λ < V`. -/
theorem blockCost_le {V n lam : ℕ} (hlam : lam < V) :
    blockCost V n lam ≤ V * (16 * V + 4 * n + 14) + (lam + 1) ^ 2 * classBound n := by
  unfold blockCost
  rw [list_sum_range]
  have h1 : ∑ rq ∈ range (lam + 1), withNonmaxCost n lam (ncsOf n lam rq) ≤
      (lam + 1) * ((lam + 1) * classBound n) :=
    sum_range_le_mul fun rq _ => withNonmaxCost_le (ncsOf_le n lam rq)
  have h2 := queryOnlyCost_le V n
  have h3 : lam * queryOnlyCost V n ≤ lam * (13 * V + 2 * n + 11) := Nat.mul_le_mul_left _ h2
  have h4 : (lam + 1) * (V - 1 - 1 + 1) ≤ V * V :=
    Nat.mul_le_mul hlam (by omega)
  have h5 : (lam + 1) * (V - 1 + (V - 1 - 1) + 1) ≤ V * (2 * V) :=
    Nat.mul_le_mul hlam (by omega)
  have h6 : lam * (13 * V + 2 * n + 11) ≤ V * (13 * V + 2 * n + 11) :=
    Nat.mul_le_mul_right _ hlam.le
  have h7 : V * (n + (n - 1)) ≤ V * (2 * n) := by
    have : n + (n - 1) ≤ 2 * n := by omega
    exact Nat.mul_le_mul_left _ this
  have h8 : 2 * (V - 1) + (V - 1 - 1) + 2 ≤ 3 * V := by omega
  have h9 : (lam + 1) * ((lam + 1) * classBound n) = (lam + 1) ^ 2 * classBound n := by ring
  linarith

/-- The blocks together, for `V ≥ 1`. -/
theorem blocks_le {V : ℕ} (n : ℕ) (hV : 1 ≤ V) :
    ∑ lam ∈ range V, blockCost V n lam ≤
      V ^ 3 * (classBound n + 16) + V ^ 2 * (4 * n + 14) := by
  calc ∑ lam ∈ range V, blockCost V n lam
      ≤ ∑ lam ∈ range V, (V * (16 * V + 4 * n + 14) + (lam + 1) ^ 2 * classBound n) :=
        sum_range_le_sum_range fun lam hlam => blockCost_le hlam
    _ = V * (V * (16 * V + 4 * n + 14)) + (∑ lam ∈ range V, (lam + 1) ^ 2) * classBound n := by
        rw [sum_add_distrib, sum_const, card_range, smul_eq_mul, sum_mul]
    _ ≤ V * (V * (16 * V + 4 * n + 14)) + V ^ 3 * classBound n := by
        gcongr
        exact sum_succ_sq_le hV
    _ = V ^ 3 * (classBound n + 16) + V ^ 2 * (4 * n + 14) := by ring

/-- **The bill, bounded above.** For `V ≥ 1`: the tables, `V³ (n 2ⁿ + 9 n + 24)` and
    `V² (4 n + 14)`. -/
theorem bill_le {V : ℕ} (n d h : ℕ) (hV : 1 ≤ V) :
    bill V n d h ≤ tableCost V n d h + V ^ 3 * (n * 2 ^ n + 9 * n + 24) + V ^ 2 * (4 * n + 14) := by
  rw [bill_eq]
  have := blocks_le n hV (V := V)
  unfold classBound at this
  have e : V ^ 3 * (n * 2 ^ n + 9 * n + 8 + 16) = V ^ 3 * (n * 2 ^ n + 9 * n + 24) := by ring
  omega

/-! ## Lower bounds -/

/-- Each block tests the inputs `(m, ..., m, q)` for every query below `m`, against every other
    output: at least `12 (V - 1) λ` operations. -/
theorem le_blockCost (V n lam : ℕ) : lam * (12 * (V - 1)) ≤ blockCost V n lam := by
  unfold blockCost queryOnlyCost
  have : lam * (12 * (V - 1)) ≤
      lam * (2 * (n - 1 - 1) + 4 + 4 + 2 + 12 * (V - 1) + (V - 1 - 1) + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  omega

/-- **Cubic in `V`.** For `V ≥ 2` the blocks alone cost at least `V³`. -/
theorem pow_three_le_blocks {V : ℕ} (n : ℕ) (hV : 2 ≤ V) :
    V ^ 3 ≤ ∑ lam ∈ range V, blockCost V n lam := by
  have h1 : ∑ lam ∈ range V, lam * (12 * (V - 1)) ≤ ∑ lam ∈ range V, blockCost V n lam :=
    sum_range_le_sum_range fun lam _ => le_blockCost V n lam
  rw [← sum_mul] at h1
  have h2 := mul_pred_le_two_sum_range_id V
  have h3 : V ^ 3 ≤ V * (V - 1) * (6 * (V - 1)) := by
    obtain ⟨W, rfl⟩ : ∃ W, V = W + 1 := ⟨V - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    have hW : 1 ≤ W := by omega
    calc (W + 1) ^ 3 = (W + 1) * (W + 1) * (W + 1) := by ring
      _ ≤ (W + 1) * (2 * W) * (3 * W) := by gcongr <;> omega
      _ = (W + 1) * W * (6 * W) := by ring
  nlinarith

theorem pow_three_le_bill {V : ℕ} (n d h : ℕ) (hV : 2 ≤ V) : V ^ 3 ≤ bill V n d h := by
  rw [bill_eq]
  have := pow_three_le_blocks n hV (V := V)
  omega

/-! ### Counting bits: the patterns of positions -/

/-- What every verdict of a non-maximal token pays for the patterns: the set bits of each pattern
    but one. -/
def patSum (n : ℕ) : ℕ := ∑ pat ∈ range (2 ^ (n - 1)), (setBits (n - 1) pat - 1)

theorem patSum_le_kverdCost (n ncs : ℕ) : patSum n ≤ kverdCost n ncs := by
  unfold kverdCost patSum setBits inPat
  simp only [Nat.pow_eq, list_sum_range]
  omega

/-- `(n - 3) 2ⁿ ≤ 4 patSum n` for `n ≥ 1`. -/
theorem le_patSum {n : ℕ} (hn : 1 ≤ n) : (n - 3) * 2 ^ n ≤ 4 * patSum n := by
  obtain ⟨L, rfl⟩ : ∃ L, n = L + 1 := ⟨n - 1, by omega⟩
  have h := le_sum_setBits_pred L
  have h2 : patSum (L + 1) = ∑ pat ∈ range (2 ^ L), (setBits L pat - 1) := by
    unfold patSum; simp
  rw [h2]
  have h3 : 2 ^ (L + 1) = 2 * 2 ^ L := by ring
  have h4 : L + 1 - 3 = L - 2 := by omega
  rw [h3, h4]
  nlinarith

/-- **Exponential in `n`.** For `V ≥ 2`: `(n - 3) 2ⁿ V³ ≤ 16 bill`. The verdicts of the
    non-maximal tokens alone cost `patSum n` each, `λ (λ + 1)` of them per block. -/
theorem exp_le_bill {V n : ℕ} (d h : ℕ) (hV : 2 ≤ V) (hn : 1 ≤ n) :
    (n - 3) * 2 ^ n * V ^ 3 ≤ 16 * bill V n d h := by
  have hb : ∀ lam, (lam + 1) * lam * patSum n ≤ blockCost V n lam := by
    intro lam
    unfold blockCost
    rw [list_sum_range]
    have h1 : ∀ rq, lam * patSum n ≤ withNonmaxCost n lam (ncsOf n lam rq) := by
      intro rq
      unfold withNonmaxCost
      have := Nat.mul_le_mul_left lam (patSum_le_kverdCost n (ncsOf n lam rq))
      omega
    have h2 : ∑ rq ∈ range (lam + 1), lam * patSum n ≤
        ∑ rq ∈ range (lam + 1), withNonmaxCost n lam (ncsOf n lam rq) :=
      sum_range_le_sum_range fun rq _ => h1 rq
    rw [sum_const, card_range, smul_eq_mul] at h2
    have : (lam + 1) * lam * patSum n = (lam + 1) * (lam * patSum n) := by ring
    omega
  have h1 : ∑ lam ∈ range V, (lam + 1) * lam * patSum n ≤ ∑ lam ∈ range V, blockCost V n lam :=
    sum_range_le_sum_range fun lam _ => hb lam
  rw [← sum_mul] at h1
  have h2 := pow_three_le_sum_succ_mul hV
  have h3 := le_patSum hn
  rw [bill_eq]
  have h4 : V ^ 3 * patSum n ≤ 4 * ((∑ i ∈ range V, (i + 1) * i) * patSum n) := by
    rw [← mul_assoc]; exact Nat.mul_le_mul_right _ h2
  have h5 : (n - 3) * 2 ^ n * V ^ 3 ≤ 4 * patSum n * V ^ 3 := Nat.mul_le_mul_right _ h3
  nlinarith

/-! ## The asymptotic statements -/

/-- At fixed `n`, `d`, `h`, the bill is `Θ(V³)`. -/
theorem isTheta_pow_three (n d h : ℕ) :
    (fun V => (bill V n d h : ℝ)) =Θ[atTop] fun V => (V : ℝ) ^ 3 := by
  have hT : ∀ V, 1 ≤ V → tableCost V n d h ≤
      V ^ 3 * ((h + 2 * d + 3) + (d + 2 * h * d + n * h + d * d + n * d + 3 * n) +
        (h * d + n * h * d + d * d * h) + 1) := by
    intro V hV
    rw [tableCost_eq_V]
    have h1 : V * V ≤ V ^ 3 := by
      calc V * V = V * V * 1 := by ring
        _ ≤ V * V * V := by gcongr
        _ = V ^ 3 := by ring
    have h2 : V ≤ V ^ 3 := by
      calc V = V * 1 * 1 := by ring
        _ ≤ V * V * V := by gcongr
        _ = V ^ 3 := by ring
    have h3 : V - 1 ≤ V ^ 3 := (Nat.sub_le V 1).trans h2
    have h4 := Nat.mul_le_mul_right (h + 2 * d + 3) h1
    have h5 := Nat.mul_le_mul_right (d + 2 * h * d + n * h + d * d + n * d + 3 * n) h2
    have h6 : h * d + n * h * d + d * d * h ≤ V ^ 3 * (h * d + n * h * d + d * d * h) :=
      Nat.le_mul_of_pos_left _ (by omega)
    linarith
  have key := isTheta_of_le (fun V => bill V n d h) (fun V => V ^ 3)
    ((h + 2 * d + 3) + (d + 2 * h * d + n * h + d * d + n * d + 3 * n) +
      (h * d + n * h * d + d * d * h) + 1 + (n * 2 ^ n + 9 * n + 24) + (4 * n + 14)) 1 2
    (fun V hV => by
      have h1 := bill_le n d h (V := V) (by omega)
      have h2 := hT V (by omega)
      have h3 : V ^ 2 ≤ V ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
      have h4 := Nat.mul_le_mul_right (4 * n + 14) h3
      linarith)
    (fun V hV => by simpa using pow_three_le_bill n d h hV)
  exact isTheta_cast_pow _ 3 key

/-- At fixed `V ≥ 2`, `d`, `h`, the bill is `Θ(n 2ⁿ)`. -/
theorem isTheta_mul_two_pow {V : ℕ} (d h : ℕ) (hV : 2 ≤ V) :
    (fun n => (bill V n d h : ℝ)) =Θ[atTop] fun n => (n : ℝ) * 2 ^ n := by
  have hT : ∀ n, 1 ≤ n → tableCost V n d h ≤ n * 2 ^ n *
      ((h * d + V * h + V * d + 3 * V) + (h * d + V * d + 2 * V * h * d + V * V * h + d * d * h +
        d * V * d + 2 * V * V * d + 3 * V * V + V)) := by
    intro n hn
    rw [tableCost_eq_n]
    have h1 : n ≤ n * 2 ^ n := by
      have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      nlinarith
    have h2 : 1 ≤ n * 2 ^ n := by omega
    have h3 : V - 1 ≤ V := Nat.sub_le V 1
    have h4 := Nat.mul_le_mul_right (h * d + V * h + V * d + 3 * V) h1
    have h5 : h * d + V * d + 2 * V * h * d + V * V * h + d * d * h + d * V * d + 2 * V * V * d +
        3 * V * V + V ≤ n * 2 ^ n * (h * d + V * d + 2 * V * h * d + V * V * h + d * d * h +
          d * V * d + 2 * V * V * d + 3 * V * V + V) :=
      Nat.le_mul_of_pos_left _ (by omega)
    linarith
  have key := isTheta_of_le (fun n => bill V n d h) (fun n => n * 2 ^ n)
    (((h * d + V * h + V * d + 3 * V) + (h * d + V * d + 2 * V * h * d + V * V * h + d * d * h +
        d * V * d + 2 * V * V * d + 3 * V * V + V)) + V ^ 3 * 34 + V ^ 2 * 18) 32 6
    (fun n hn => by
      have h1 := bill_le n d h (V := V) (by omega)
      have h2 := hT n (by omega)
      have h0 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      have h3 : 1 ≤ n * 2 ^ n := by
        calc 1 = 1 * 1 := rfl
          _ ≤ n * 2 ^ n := Nat.mul_le_mul (by omega) h0
      have h4 : n ≤ n * 2 ^ n := Nat.le_mul_of_pos_right _ (by omega)
      have h5 : V ^ 3 * (n * 2 ^ n + 9 * n + 24) ≤ V ^ 3 * (34 * (n * 2 ^ n)) :=
        Nat.mul_le_mul_left _ (by omega)
      have h6 : V ^ 2 * (4 * n + 14) ≤ V ^ 2 * (18 * (n * 2 ^ n)) :=
        Nat.mul_le_mul_left _ (by omega)
      linarith)
    (fun n hn => by
      have h1 := exp_le_bill d h hV (n := n) (by omega)
      have h2 : n ≤ 2 * (n - 3) := by omega
      have h3 : 8 ≤ V ^ 3 := by
        calc 8 = 2 ^ 3 := by norm_num
          _ ≤ V ^ 3 := Nat.pow_le_pow_left hV 3
      have h4 : n * 2 ^ n ≤ 2 * (n - 3) * 2 ^ n := Nat.mul_le_mul_right (2 ^ n) h2
      have h5 : (n - 3) * 2 ^ n * 8 ≤ (n - 3) * 2 ^ n * V ^ 3 := Nat.mul_le_mul_left _ h3
      linarith)
  exact isTheta_cast_mul_two_pow _ key

end GrossCubic
