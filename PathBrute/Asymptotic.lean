import PathBrute.Sound
import Common.Asymptotic

/-!
# Entry 8: the bill as the sizes grow

`check_billed` gives the bill of brute force from the path tables as `bill V n d h`: the tables,
then `5 n` operations per input and other output. This module states it in closed form and proves
its growth: `Θ(V^(n + 1))` in the vocabulary (`isTheta_pow_succ`), from the `V^n` inputs, and
`Θ(n V^n)` in the context length (`isTheta_mul_pow`), against the `Θ(V³ n²)` of Gross et al.'s
cubic proof (entry 7, at the sizes where its patterns do not dominate) and the `Θ(n 2^n V³)` of
the library's cubic entries.
-/

namespace PathBrute

open Common Asymptotics Filter

/-- The tables, by powers of `V`. -/
theorem tableCost_eq (V n d h : ℕ) :
    tableCost V n d h = V ^ 3 * (n + 1) + V * V * (h + 2 * d + 5 * n) +
      V * (d + 2 * h * d + n * h + d * d + n * d) + (h * d + n * h * d + d * d * h) := by
  unfold tableCost; ring

/-- Each input costs `5 n (V - 1)`: `5 n` per other output. -/
theorem perInput_eq {V n : ℕ} (hV : 2 ≤ V) (hn : 1 ≤ n) :
    (V - 1) * (n * 4 + (n - 1)) + (V - 1 - 1) + 1 = 5 * n * (V - 1) := by
  obtain ⟨W, rfl⟩ : ∃ W, V = W + 2 := ⟨V - 2, by omega⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel, show W + 2 - 1 = W + 1 by omega, show W + 1 - 1 = W by omega]
  ring

/-- **The bill, read**: the tables and `5 n (V - 1)` per input. -/
theorem bill_eq {V n : ℕ} (d h : ℕ) (hV : 2 ≤ V) (hn : 1 ≤ n) :
    bill V n d h = tableCost V n d h + 5 * n * (V - 1) * V ^ n := by
  unfold bill
  rw [perInput_eq hV hn]
  ring

/-- **At least `V^(n + 1)`** for `V ≥ 2`, `n ≥ 1`: the inputs alone. -/
theorem pow_succ_le_bill {V n : ℕ} (d h : ℕ) (hV : 2 ≤ V) (hn : 1 ≤ n) :
    V ^ (n + 1) ≤ bill V n d h := by
  rw [bill_eq d h hV hn]
  have h1 : V ≤ 5 * n * (V - 1) := by
    have : 2 * (V - 1) ≤ 5 * n * (V - 1) := Nat.mul_le_mul_right _ (by omega)
    omega
  have h2 : V * V ^ n ≤ 5 * n * (V - 1) * V ^ n := Nat.mul_le_mul_right _ h1
  rw [pow_succ, mul_comm]
  omega

/-- **At most `(T + 5 n) V^(n + 1)`** for `V ≥ 2`, `n ≥ 2`, with `T` the tables' coefficients. -/
theorem bill_le {V n : ℕ} (d h : ℕ) (hV : 2 ≤ V) (hn : 2 ≤ n) :
    bill V n d h ≤ ((n + 1) + (h + 2 * d + 5 * n) + (d + 2 * h * d + n * h + d * d + n * d) +
      (h * d + n * h * d + d * d * h) + 5 * n) * V ^ (n + 1) := by
  rw [bill_eq d h hV (by omega), tableCost_eq]
  have hV1 : 0 < V := by omega
  have h3 : V ^ 3 ≤ V ^ (n + 1) := Nat.pow_le_pow_right hV1 (by omega)
  have h2 : V * V ≤ V ^ (n + 1) := by
    calc V * V = V ^ 2 := by ring
      _ ≤ V ^ (n + 1) := Nat.pow_le_pow_right hV1 (by omega)
  have h1 : V ≤ V ^ (n + 1) := by
    calc V = V ^ 1 := by ring
      _ ≤ V ^ (n + 1) := Nat.pow_le_pow_right hV1 (by omega)
  have h0 : 1 ≤ V ^ (n + 1) := Nat.one_le_pow _ _ hV1
  have h4 : 5 * n * (V - 1) * V ^ n ≤ 5 * n * V ^ (n + 1) := by
    rw [pow_succ]
    have : (V - 1) * V ^ n ≤ V * V ^ n := Nat.mul_le_mul_right _ (Nat.sub_le V 1)
    calc 5 * n * (V - 1) * V ^ n = 5 * n * ((V - 1) * V ^ n) := by ring
      _ ≤ 5 * n * (V * V ^ n) := Nat.mul_le_mul_left _ this
      _ = 5 * n * (V ^ n * V) := by ring
  have e3 := Nat.mul_le_mul_right (n + 1) h3
  have e2 := Nat.mul_le_mul_right (h + 2 * d + 5 * n) h2
  have e1 := Nat.mul_le_mul_right (d + 2 * h * d + n * h + d * d + n * d) h1
  have e0 := Nat.mul_le_mul_right (h * d + n * h * d + d * d * h) h0
  nlinarith

/-- At fixed `n ≥ 2`, `d`, `h`, the bill is `Θ(V^(n + 1))`. -/
theorem isTheta_pow_succ {n : ℕ} (d h : ℕ) (hn : 2 ≤ n) :
    (fun V => (bill V n d h : ℝ)) =Θ[atTop] fun V => (V : ℝ) ^ (n + 1) := by
  have key := isTheta_of_le (fun V => bill V n d h) (fun V => V ^ (n + 1))
    ((n + 1) + (h + 2 * d + 5 * n) + (d + 2 * h * d + n * h + d * d + n * d) +
      (h * d + n * h * d + d * d * h) + 5 * n) 1 2
    (fun V hV => bill_le d h hV hn)
    (fun V hV => by
      show V ^ (n + 1) ≤ 1 * bill V n d h
      rw [one_mul]
      exact pow_succ_le_bill d h hV (by omega))
  exact isTheta_cast_pow _ (n + 1) key

/-- At fixed `V ≥ 2`, `d`, `h`, the bill is `Θ(n V^n)`. -/
theorem isTheta_mul_pow {V : ℕ} (d h : ℕ) (hV : 2 ≤ V) :
    (fun n => (bill V n d h : ℝ)) =Θ[atTop] fun n => (n : ℝ) * (V : ℝ) ^ n := by
  have key := isTheta_of_le (fun n => bill V n d h) (fun n => n * V ^ n)
    ((V ^ 3 + V * V * 5 + V * (h + d)) + (V ^ 3 + V * V * (h + 2 * d) +
      V * (d + 2 * h * d + d * d) + (h * d + d * d * h)) + h * d + 5 * V) 1 1
    (fun n hn => by
      show bill V n d h ≤ _ * (n * V ^ n)
      rw [bill_eq d h hV hn, tableCost_eq]
      have h0 : 1 ≤ V ^ n := Nat.one_le_pow _ _ (by omega)
      have h1 : 1 ≤ n * V ^ n := by
        calc 1 = 1 * 1 := rfl
          _ ≤ n * V ^ n := Nat.mul_le_mul hn h0
      have h2 : n ≤ n * V ^ n := Nat.le_mul_of_pos_right _ (by omega)
      have h3 : 5 * n * (V - 1) * V ^ n ≤ 5 * V * (n * V ^ n) := by
        have : V - 1 ≤ V := Nat.sub_le V 1
        calc 5 * n * (V - 1) * V ^ n = 5 * (V - 1) * (n * V ^ n) := by ring
          _ ≤ 5 * V * (n * V ^ n) := Nat.mul_le_mul_right _ (by omega)
      have h4 : V ^ 3 * (n + 1) ≤ (V ^ 3 + V ^ 3) * (n * V ^ n) := by
        have a1 : V ^ 3 * n ≤ V ^ 3 * (n * V ^ n) := Nat.mul_le_mul_left _ h2
        have a2 : V ^ 3 ≤ V ^ 3 * (n * V ^ n) := Nat.le_mul_of_pos_right _ h1
        linarith
      have h5 : V * V * (h + 2 * d + 5 * n) ≤
          (V * V * 5 + V * V * (h + 2 * d)) * (n * V ^ n) := by
        have a1 : V * V * 5 * n ≤ V * V * 5 * (n * V ^ n) := Nat.mul_le_mul_left _ h2
        have a2 : V * V * (h + 2 * d) ≤ V * V * (h + 2 * d) * (n * V ^ n) :=
          Nat.le_mul_of_pos_right _ h1
        linarith
      have h6 : V * (d + 2 * h * d + n * h + d * d + n * d) ≤
          (V * (h + d) + V * (d + 2 * h * d + d * d)) * (n * V ^ n) := by
        have a1 : V * (h + d) * n ≤ V * (h + d) * (n * V ^ n) := Nat.mul_le_mul_left _ h2
        have a2 : V * (d + 2 * h * d + d * d) ≤ V * (d + 2 * h * d + d * d) * (n * V ^ n) :=
          Nat.le_mul_of_pos_right _ h1
        linarith
      have h7 : h * d + n * h * d + d * d * h ≤ ((h * d + d * d * h) + h * d) * (n * V ^ n) := by
        have a1 : h * d * n ≤ h * d * (n * V ^ n) := Nat.mul_le_mul_left _ h2
        have a2 : h * d + d * d * h ≤ (h * d + d * d * h) * (n * V ^ n) :=
          Nat.le_mul_of_pos_right _ h1
        linarith
      linarith)
    (fun n hn => by
      show n * V ^ n ≤ 1 * bill V n d h
      rw [one_mul, bill_eq d h hV hn]
      have : n * V ^ n ≤ 5 * n * (V - 1) * V ^ n := by
        have : 1 ≤ 5 * (V - 1) := by omega
        calc n * V ^ n = 1 * (n * V ^ n) := by ring
          _ ≤ 5 * (V - 1) * (n * V ^ n) := Nat.mul_le_mul_right _ this
          _ = 5 * n * (V - 1) * V ^ n := by ring
      omega)
  exact isTheta_cast _ _ _ (fun k => by push_cast; ring) key

end PathBrute
