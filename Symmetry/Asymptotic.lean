import Symmetry.MaxK
import Common.Asymptotic

/-!
# Entry 4: the bill as the sizes grow

On the linear max-of-k family, `check_billed_maxK` bills the symmetry method at
`C(V + k - 1, k) (k d + d² + d V + V - 1)`: one forward pass per sorted input. This module names
that bill and proves its growth: `Θ(V^(k + 1))` in the vocabulary (`isTheta_pow_succ`), like
brute force (entry 2), but with the constant `1 / k!`: `V^k ≤ k! C(V + k - 1, k) ≤ k! (k V)^k`.
-/

namespace Symmetry

open CompactCheck Common Asymptotics Filter Nat

/-- The bill of symmetry on the linear max-of-k family: `C(V + k - 1, k)` forward passes of
    `k d + d² + d V + V - 1` operations. -/
def bill (V k d : ℕ) : ℕ := (V + k - 1).choose k * (k * d + d * d + d * V + (V - 1))

/-- `check_billed_maxK`, with the bill named. -/
theorem check_billed_maxK_bill {g : Graph} (hg : LinearMaxK.IsLinearMaxK g = true) {w : Weights ℚ}
    {d : ℕ} {tE tL tU : Tensor ℚ} (hw : LinearMaxK.WF w g.values d tE tL tU) (c : Cert) :
    CostM.billed (check Interp.counting g (maxTask g.positions g.values)) ⟨w, c⟩ =
      some (numCorrect g w (maxTask g.positions g.values), bill g.values g.positions d) :=
  check_billed_maxK hg hw c

/-- The sorted inputs, bounded below: `V^k ≤ k! C(V + k - 1, k)`. -/
theorem pow_le_factorial_mul_choose (V k : ℕ) : V ^ k ≤ k ! * (V + k - 1).choose k := by
  rcases k with _ | k
  · simp
  rw [← descFactorial_eq_factorial_mul_choose]
  have h := pow_sub_le_descFactorial (V + (k + 1) - 1) (k + 1)
  have e : V + (k + 1) - 1 + 1 - (k + 1) = V := by omega
  rw [e] at h
  exact h

/-- The sorted inputs, bounded above: `C(V + k - 1, k) ≤ (k V)^k` for `V ≥ 1`. -/
theorem choose_le_pow {V : ℕ} (k : ℕ) (hV : 1 ≤ V) : (V + k - 1).choose k ≤ (k * V) ^ k := by
  have h1 : k ! * (V + k - 1).choose k ≤ (V + k - 1) ^ k := by
    rw [← descFactorial_eq_factorial_mul_choose]
    exact descFactorial_le_pow _ _
  have h2 : (V + k - 1).choose k ≤ (V + k - 1) ^ k :=
    le_trans (Nat.le_mul_of_pos_left _ (factorial_pos k)) h1
  rcases k with _ | k
  · simp
  have h3 : V + (k + 1) - 1 ≤ (k + 1) * V := by
    have : k ≤ k * V := Nat.le_mul_of_pos_right _ hV
    calc V + (k + 1) - 1 = V + k := by omega
      _ ≤ V + k * V := by omega
      _ = (k + 1) * V := by ring
  exact h2.trans (Nat.pow_le_pow_left h3 (k + 1))

/-- **At least `V^(k + 1) / (2 k!)`** for `V ≥ 2`. -/
theorem pow_succ_le_bill {V : ℕ} (k d : ℕ) (hV : 2 ≤ V) : V ^ (k + 1) ≤ 2 * k ! * bill V k d := by
  unfold bill
  have h1 := pow_le_factorial_mul_choose V k
  have h2 : V ≤ 2 * (k * d + d * d + d * V + (V - 1)) := by omega
  calc V ^ (k + 1) = V ^ k * V := pow_succ V k
    _ ≤ (k ! * (V + k - 1).choose k) * (2 * (k * d + d * d + d * V + (V - 1))) :=
        Nat.mul_le_mul h1 h2
    _ = 2 * k ! * ((V + k - 1).choose k * (k * d + d * d + d * V + (V - 1))) := by ring

/-- **At most `k^k (k d + d² + d + 1) V^(k + 1)`** for `V ≥ 1`. -/
theorem bill_le {V : ℕ} (k d : ℕ) (hV : 1 ≤ V) :
    bill V k d ≤ k ^ k * (k * d + d * d + d + 1) * V ^ (k + 1) := by
  unfold bill
  have h1 := choose_le_pow k hV
  have h2 : k * d + d * d + d * V + (V - 1) ≤ (k * d + d * d + d + 1) * V := by
    have h3 : k * d + d * d ≤ (k * d + d * d) * V := Nat.le_mul_of_pos_right _ hV
    have h4 : V - 1 ≤ V := Nat.sub_le V 1
    nlinarith
  calc (V + k - 1).choose k * (k * d + d * d + d * V + (V - 1))
      ≤ (k * V) ^ k * ((k * d + d * d + d + 1) * V) := Nat.mul_le_mul h1 h2
    _ = k ^ k * (k * d + d * d + d + 1) * V ^ (k + 1) := by ring

/-- At fixed `k`, `d`, the bill is `Θ(V^(k + 1))`. -/
theorem isTheta_pow_succ (k d : ℕ) :
    (fun V => (bill V k d : ℝ)) =Θ[atTop] fun V => (V : ℝ) ^ (k + 1) := by
  have key := isTheta_of_le (fun V => bill V k d) (fun V => V ^ (k + 1))
    (k ^ k * (k * d + d * d + d + 1)) (2 * k !) 2
    (fun V hV => bill_le k d (by omega))
    (fun V hV => pow_succ_le_bill k d hV)
  exact isTheta_cast_pow _ (k + 1) key

end Symmetry
