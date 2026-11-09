import LinearMaxK.Exact
import Common.Asymptotic

/-!
# Entry 1: the bill as the sizes grow

`bill_eq` gives the bill of the group method in closed form: the columns of `M`, `V (d² + V d)`,
the literal `k - 1`, and the tests, `(V - 1) V (V + 3)`. It does not depend on `k`. This module
proves its growth: `Θ(V³)` in the vocabulary (`isTheta_pow_three`), from the `V (V - 1)` tests of
`V + 3` operations each, and `Θ(d²)` in the width (`isTheta_sq_d`), from the columns, while brute
force (entry 2) grows as `V^(k + 1)`.
-/

namespace LinearMaxK

open Common Asymptotics Filter

/-- **At most `(d² + d + 5) V³`** for `V ≥ 1`. -/
theorem bill_le {V : ℕ} (d : ℕ) (hV : 1 ≤ V) : bill V d ≤ (d * d + d + 5) * V ^ 3 := by
  rw [bill_eq]
  have h1 : V ≤ V ^ 3 := by
    calc V = V ^ 1 := by ring
      _ ≤ V ^ 3 := Nat.pow_le_pow_right hV (by omega)
  have h2 : V * V ≤ V ^ 3 := by
    calc V * V = V ^ 2 := by ring
      _ ≤ V ^ 3 := Nat.pow_le_pow_right hV (by omega)
  have h3 : (V - 1) * V * (V + 3) ≤ V * V * (4 * V) :=
    Nat.mul_le_mul (Nat.mul_le_mul_right V (Nat.sub_le V 1)) (by omega)
  have h4 : V * V * (4 * V) = 4 * V ^ 3 := by ring
  have h5 : 1 ≤ V ^ 3 := Nat.one_le_pow _ _ hV
  have h6 := Nat.mul_le_mul_right (d * d) h1
  have h7 := Nat.mul_le_mul_right d h2
  linarith

/-- **At least `V³ / 2`** for `V ≥ 2`: the tests alone. -/
theorem pow_three_le_bill {V : ℕ} (d : ℕ) (hV : 2 ≤ V) : V ^ 3 ≤ 2 * bill V d := by
  rw [bill_eq]
  have : V ^ 3 ≤ 2 * ((V - 1) * V * (V + 3)) := by
    obtain ⟨W, rfl⟩ : ∃ W, V = W + 2 := ⟨V - 2, by omega⟩
    simp only [show W + 2 - 1 = W + 1 by omega]
    calc (W + 2) ^ 3 = (W + 2) * (W + 2) * (W + 2) := by ring
      _ ≤ (2 * (W + 1)) * (W + 2) * (W + 2 + 3) := by gcongr <;> omega
      _ = 2 * ((W + 1) * (W + 2) * (W + 2 + 3)) := by ring
  omega

/-- At fixed `d`, the bill is `Θ(V³)`. -/
theorem isTheta_pow_three (d : ℕ) :
    (fun V => (bill V d : ℝ)) =Θ[atTop] fun V => (V : ℝ) ^ 3 := by
  have key := isTheta_of_le (fun V => bill V d) (fun V => V ^ 3) (d * d + d + 5) 2 2
    (fun V hV => bill_le d (by omega))
    (fun V hV => pow_three_le_bill d hV)
  exact isTheta_cast_pow _ 3 key

/-- At fixed `V ≥ 1`, the bill is `Θ(d²)`: the columns of `M`. -/
theorem isTheta_sq_d {V : ℕ} (hV : 1 ≤ V) :
    (fun d => (bill V d : ℝ)) =Θ[atTop] fun d => (d : ℝ) ^ 2 := by
  have key := isTheta_of_le (fun d => bill V d) (fun d => d ^ 2)
    (V + V * V + 1 + (V - 1) * V * (V + 3)) 1 1
    (fun d hd => by
      show bill V d ≤ _ * d ^ 2
      rw [bill_eq]
      have h1 : d ≤ d ^ 2 := by nlinarith
      have h2 : 1 ≤ d ^ 2 := by nlinarith
      have h3 : V * V * d ≤ V * V * d ^ 2 := Nat.mul_le_mul_left _ h1
      have h4 : 1 + (V - 1) * V * (V + 3) ≤ (1 + (V - 1) * V * (V + 3)) * d ^ 2 :=
        Nat.le_mul_of_pos_right _ (by omega)
      nlinarith)
    (fun d hd => by
      show d ^ 2 ≤ 1 * bill V d
      rw [bill_eq]
      have : d ^ 2 ≤ V * (d * d + V * d) := by
        calc d ^ 2 = 1 * (d * d) := by ring
          _ ≤ V * (d * d) := Nat.mul_le_mul_right _ hV
          _ ≤ V * (d * d + V * d) := Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
      omega)
  exact isTheta_cast_pow _ 2 key

end LinearMaxK
