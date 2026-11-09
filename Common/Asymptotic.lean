import Common.Basic
import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Tactic.LinearCombination

/-!
# Tools for the asymptotic statements about bills

Every entry proves its bill as an exact function of the sizes. The modules `*/Asymptotic.lean`
state what those functions do as the sizes grow: explicit two-sided bounds first (the content), and
then Mathlib's `=O[atTop]` and `=Θ[atTop]` as corollaries, one size growing with the others fixed.

Two kinds of tools:

* `isBigO_of_le`, `isTheta_of_le`: from bounds `f k ≤ C g k` on natural numbers, the asymptotic
  statement about their casts to `ℝ`.
* bounds on sums over `Finset.range V` of polynomials in the index, which is how every bill adds
  up its blocks: an upper bound by the largest term, and the closed forms `∑ (i + 1) i` and
  `∑ (i + 1)²` that the cubic terms come from;
* counting bits: the checkers of the attention entries run over the `2^(n - 1)` patterns of
  positions, and what they pay for a pattern grows with its set bits. Over all patterns of `L`
  bits, `L 2^(L - 1)` bits are set (`two_mul_pcSum`).
-/

namespace Common

open Asymptotics Filter Finset

/-! ## From bounds on naturals to `O` and `Θ` -/

/-- `f = O(g)` along `atTop`, from `f k ≤ C g k` for every `k ≥ k₀`. -/
theorem isBigO_of_le (f g : ℕ → ℕ) (C k₀ : ℕ) (h : ∀ k, k₀ ≤ k → f k ≤ C * g k) :
    (fun k => (f k : ℝ)) =O[atTop] fun k => (g k : ℝ) := by
  refine IsBigO.of_bound C ?_
  filter_upwards [eventually_ge_atTop k₀] with k hk
  rw [Real.norm_natCast, Real.norm_natCast]
  exact_mod_cast h k hk

/-- `f = Θ(g)` along `atTop`, from `f k ≤ C g k` and `g k ≤ C' f k` for every `k ≥ k₀`. -/
theorem isTheta_of_le (f g : ℕ → ℕ) (C C' k₀ : ℕ) (h : ∀ k, k₀ ≤ k → f k ≤ C * g k)
    (h' : ∀ k, k₀ ≤ k → g k ≤ C' * f k) :
    (fun k => (f k : ℝ)) =Θ[atTop] fun k => (g k : ℝ) :=
  ⟨isBigO_of_le f g C k₀ h, isBigO_of_le g f C' k₀ h'⟩

/-- The target written over `ℝ`: from `Θ(g)` with `g` on the naturals to `Θ(g')` for any `g'`
    that `g` casts to. -/
theorem isTheta_cast (f g : ℕ → ℕ) (g' : ℕ → ℝ) (hg : ∀ k, ((g k : ℕ) : ℝ) = g' k)
    (h : (fun k => (f k : ℝ)) =Θ[atTop] fun k => (g k : ℝ)) :
    (fun k => (f k : ℝ)) =Θ[atTop] g' := by
  have e : g' = fun k => (g k : ℝ) := by funext k; exact (hg k).symm
  rw [e]; exact h

/-- The target `k ^ p`, cast after the power. -/
theorem isTheta_cast_pow (f : ℕ → ℕ) (p : ℕ)
    (h : (fun k => (f k : ℝ)) =Θ[atTop] fun k => ((k ^ p : ℕ) : ℝ)) :
    (fun k => (f k : ℝ)) =Θ[atTop] fun k => (k : ℝ) ^ p := by
  have e : (fun k : ℕ => (k : ℝ) ^ p) = fun k => ((k ^ p : ℕ) : ℝ) := by
    funext k; push_cast; ring
  rw [e]; exact h

/-- The target `k 2^k`, cast after the arithmetic. -/
theorem isTheta_cast_mul_two_pow (f : ℕ → ℕ)
    (h : (fun k => (f k : ℝ)) =Θ[atTop] fun k => ((k * 2 ^ k : ℕ) : ℝ)) :
    (fun k => (f k : ℝ)) =Θ[atTop] fun k => (k : ℝ) * 2 ^ k := by
  have e : (fun k : ℕ => (k : ℝ) * 2 ^ k) = fun k => ((k * 2 ^ k : ℕ) : ℝ) := by
    funext k; push_cast; ring
  rw [e]; exact h

/-! ## Sums over a range -/

/-- A sum of `V` terms, each at most `B`, is at most `V B`. -/
theorem sum_range_le_mul {f : ℕ → ℕ} {V B : ℕ} (h : ∀ i, i < V → f i ≤ B) :
    ∑ i ∈ range V, f i ≤ V * B := by
  have := Finset.sum_le_card_nsmul (range V) f B fun i hi => h i (mem_range.mp hi)
  simpa using this

/-- A sum of `V` terms, each at least `B`, is at least `V B`. -/
theorem mul_le_sum_range {f : ℕ → ℕ} {V B : ℕ} (h : ∀ i, i < V → B ≤ f i) :
    V * B ≤ ∑ i ∈ range V, f i := by
  have := Finset.card_nsmul_le_sum (range V) f B fun i hi => h i (mem_range.mp hi)
  simpa using this

/-- Termwise bounds add up. -/
theorem sum_range_le_sum_range {f g : ℕ → ℕ} {V : ℕ} (h : ∀ i, i < V → f i ≤ g i) :
    ∑ i ∈ range V, f i ≤ ∑ i ∈ range V, g i :=
  Finset.sum_le_sum fun i hi => h i (mem_range.mp hi)

/-- A quadratic in `V` with coefficients `a`, `b`, `c` is at most `(a + b + c) V²` for `V ≥ 1`. -/
theorem quad_le {V : ℕ} (a b c : ℕ) (hV : 1 ≤ V) : V * V * a + V * b + c ≤ (a + b + c) * V ^ 2 := by
  have h1 : V * b ≤ V * V * b := Nat.mul_le_mul_right b (Nat.le_mul_of_pos_left V hV)
  have h2 : c ≤ V * V * c := Nat.le_mul_of_pos_left c (by positivity)
  have h3 : (a + b + c) * V ^ 2 = V * V * a + V * V * b + V * V * c := by ring
  omega

/-- `3 Σ_{i < V} (i + 1) i + V = V³`. -/
theorem three_sum_succ_mul (V : ℕ) : 3 * (∑ i ∈ range V, (i + 1) * i) + V = V ^ 3 := by
  induction V with
  | zero => simp
  | succ V ih =>
    rw [sum_range_succ, Nat.mul_add]
    zify at ih ⊢
    linear_combination ih

/-- `V³ ≤ 4 Σ_{i < V} (i + 1) i` for `V ≥ 2`. -/
theorem pow_three_le_sum_succ_mul {V : ℕ} (hV : 2 ≤ V) :
    V ^ 3 ≤ 4 * ∑ i ∈ range V, (i + 1) * i := by
  have h := three_sum_succ_mul V
  have hle : V ≤ ∑ i ∈ range V, (i + 1) * i := by
    have hmem : V - 1 ∈ range V := mem_range.mpr (by omega)
    calc V ≤ (V - 1 + 1) * (V - 1) := by
          rcases V with _ | _ | V
          · omega
          · omega
          · simp only [Nat.add_sub_cancel]; nlinarith
      _ ≤ ∑ i ∈ range V, (i + 1) * i :=
          Finset.single_le_sum (f := fun i => (i + 1) * i) (fun _ _ => Nat.zero_le _) hmem
  omega

/-- `6 Σ_{i < V} (i + 1)² = V (V + 1) (2V + 1)`. -/
theorem six_sum_succ_sq (V : ℕ) : 6 * (∑ i ∈ range V, (i + 1) ^ 2) = V * (V + 1) * (2 * V + 1) := by
  induction V with
  | zero => simp
  | succ V ih => rw [sum_range_succ, Nat.mul_add, ih]; ring

/-- `Σ_{i < V} (i + 1)² ≤ V³` for `V ≥ 1`. -/
theorem sum_succ_sq_le {V : ℕ} (hV : 1 ≤ V) : ∑ i ∈ range V, (i + 1) ^ 2 ≤ V ^ 3 := by
  have h := six_sum_succ_sq V
  have h1 : V + 1 ≤ 2 * V := by omega
  have h2 : 2 * V + 1 ≤ 3 * V := by omega
  have : V * (V + 1) * (2 * V + 1) ≤ V * (2 * V) * (3 * V) := by gcongr
  have h3 : V * (2 * V) * (3 * V) = 6 * V ^ 3 := by ring
  omega

/-- `Σ_{i < V} i ≤ V²`. -/
theorem sum_range_id_le_sq (V : ℕ) : ∑ i ∈ range V, i ≤ V ^ 2 := by
  calc ∑ i ∈ range V, i ≤ V * V := sum_range_le_mul fun i hi => hi.le
    _ = V ^ 2 := (sq V).symm

/-- `Σ_{i < V} (i + 1) ≤ V²` for `V ≥ 1`. -/
theorem sum_succ_le_sq (V : ℕ) : ∑ i ∈ range V, (i + 1) ≤ V ^ 2 := by
  calc ∑ i ∈ range V, (i + 1) ≤ V * V := sum_range_le_mul fun i hi => hi
    _ = V ^ 2 := (sq V).symm

/-- `V (V - 1) ≤ 2 Σ_{i < V} i`: the sum of the first `V` naturals, bounded below. -/
theorem mul_pred_le_two_sum_range_id (V : ℕ) : V * (V - 1) ≤ 2 * ∑ i ∈ range V, i := by
  rw [← sum_range_id_mul_two]; ring_nf; exact le_refl _

/-- A list sum over `List.range` as a `Finset` sum, for the bills written with `List.map`. -/
theorem list_sum_range (f : ℕ → ℕ) (V : ℕ) :
    ((List.range V).map f).sum = ∑ i ∈ range V, f i :=
  sum_range_eq f V

/-- The length of a filtered range is at most the range. -/
theorem length_filter_range_le (p : ℕ → Bool) (L : ℕ) :
    ((List.range L).filter p).length ≤ L := by
  simpa using List.length_filter_le p (List.range L)

/-! ## Counting bits -/

/-- The set bits of `pat` among the first `L`: the positions of a pattern. -/
def setBits (L pat : ℕ) : ℕ := ((List.range L).filter pat.testBit).length

theorem setBits_le (L pat : ℕ) : setBits L pat ≤ L := length_filter_range_le _ L

theorem setBits_succ_of_lt {L pat : ℕ} (h : pat < 2 ^ L) : setBits (L + 1) pat = setBits L pat := by
  unfold setBits
  rw [List.range_succ, List.filter_append]
  simp [Nat.testBit_lt_two_pow h]

theorem setBits_succ_add {L pat : ℕ} (h : pat < 2 ^ L) :
    setBits (L + 1) (2 ^ L + pat) = setBits L pat + 1 := by
  unfold setBits
  rw [List.range_succ, List.filter_append, List.length_append]
  congr 1
  · congr 1
    exact List.filter_congr fun i hi => Nat.testBit_two_pow_add_gt (List.mem_range.mp hi) pat
  · simp [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow h]

/-- The set bits of all patterns of `L` bits, added up. -/
def pcSum (L : ℕ) : ℕ := ∑ pat ∈ range (2 ^ L), setBits L pat

/-- `2 pcSum L = L 2^L`: half of all the bits are set. -/
theorem two_mul_pcSum (L : ℕ) : 2 * pcSum L = L * 2 ^ L := by
  induction L with
  | zero => simp [pcSum, setBits]
  | succ L ih =>
    unfold pcSum at ih ⊢
    rw [pow_succ, mul_two, sum_range_add]
    have h1 : ∑ pat ∈ range (2 ^ L), setBits (L + 1) pat = ∑ pat ∈ range (2 ^ L), setBits L pat :=
      sum_congr rfl fun pat hpat => setBits_succ_of_lt (mem_range.mp hpat)
    have h2 : ∑ pat ∈ range (2 ^ L), setBits (L + 1) (2 ^ L + pat) =
        ∑ pat ∈ range (2 ^ L), (setBits L pat + 1) :=
      sum_congr rfl fun pat hpat => setBits_succ_add (mem_range.mp hpat)
    rw [h1, h2, sum_add_distrib, sum_const, card_range, smul_eq_mul, mul_one]
    nlinarith

/-- Each pattern's set bits but one, added up: at least `(L - 2) 2^(L - 1)`. -/
theorem le_sum_setBits_pred (L : ℕ) :
    (L - 2) * 2 ^ L ≤ 2 * ∑ pat ∈ range (2 ^ L), (setBits L pat - 1) := by
  rcases Nat.lt_or_ge L 2 with hL | hL
  · have : L - 2 = 0 := by omega
    simp [this]
  have h := two_mul_pcSum L
  unfold pcSum at h
  have h1 : ∑ pat ∈ range (2 ^ L), setBits L pat ≤
      ∑ pat ∈ range (2 ^ L), (setBits L pat - 1 + 1) :=
    Finset.sum_le_sum fun pat _ => by omega
  rw [sum_add_distrib, sum_const, card_range, smul_eq_mul, mul_one] at h1
  have h4 : (L - 2) * 2 ^ L + 2 * 2 ^ L ≤ L * 2 ^ L := by
    have : L - 2 + 2 ≤ L := by omega
    have := Nat.mul_le_mul_right (2 ^ L) this
    linarith
  omega

end Common
