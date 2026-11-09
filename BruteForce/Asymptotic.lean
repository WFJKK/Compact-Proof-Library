import BruteForce.MaxK
import Common.Asymptotic

/-!
# Entry 2: the bill as the sizes grow

On the linear max-of-k family, `check_billed_maxK` bills brute force at
`V^k (k d + d² + d V + V - 1)`: one forward pass per input. This module names that bill and proves
its growth: `Θ(V^(k + 1))` in the vocabulary (`isTheta_pow_succ`), Gross et al.'s
`O(d_vocab^(n_ctx + 1) n_ctx d_model)`, and `Θ(k V^k)` in the context length (`isTheta_mul_pow`).

On the attention networks the charge of a forward pass is computed per instance (`General.lean`),
so there is no formula here to bound.
-/

namespace BruteForce

open CompactCheck Common Asymptotics Filter

/-- The bill of brute force on the linear max-of-k family: `V^k` forward passes of
    `k d + d² + d V + V - 1` operations. -/
def bill (V k d : ℕ) : ℕ := V ^ k * (k * d + d * d + d * V + (V - 1))

/-- `check_billed_maxK`, with the bill named. -/
theorem check_billed_maxK_bill {g : Graph} (hg : LinearMaxK.IsLinearMaxK g = true) {w : Weights ℚ}
    {d : ℕ} {tE tL tU : Tensor ℚ} (hw : LinearMaxK.WF w g.values d tE tL tU) (c : Cert) :
    CostM.billed (check Interp.counting g (maxTask g.positions g.values)) ⟨w, c⟩ =
      some (numCorrect g w (maxTask g.positions g.values), bill g.values g.positions d) :=
  check_billed_maxK hg hw c

/-- **At least `V^(k + 1) / 2`** for `V ≥ 2`. -/
theorem pow_succ_le_bill {V : ℕ} (k d : ℕ) (hV : 2 ≤ V) : V ^ (k + 1) ≤ 2 * bill V k d := by
  unfold bill
  have h1 : V ≤ 2 * (V - 1) := by omega
  have h2 : V ≤ 2 * (k * d + d * d + d * V + (V - 1)) := by omega
  rw [pow_succ]
  calc V ^ k * V ≤ V ^ k * (2 * (k * d + d * d + d * V + (V - 1))) := Nat.mul_le_mul_left _ h2
    _ = 2 * (V ^ k * (k * d + d * d + d * V + (V - 1))) := by ring

/-- **At most `(k d + d² + d + 1) V^(k + 1)`** for `V ≥ 1`. -/
theorem bill_le {V : ℕ} (k d : ℕ) (hV : 1 ≤ V) :
    bill V k d ≤ (k * d + d * d + d + 1) * V ^ (k + 1) := by
  unfold bill
  have : k * d + d * d + d * V + (V - 1) ≤ (k * d + d * d + d + 1) * V := by
    have h1 : k * d + d * d ≤ (k * d + d * d) * V := Nat.le_mul_of_pos_right _ hV
    have h2 : V - 1 ≤ V := Nat.sub_le V 1
    nlinarith
  calc V ^ k * (k * d + d * d + d * V + (V - 1)) ≤ V ^ k * ((k * d + d * d + d + 1) * V) :=
        Nat.mul_le_mul_left _ this
    _ = (k * d + d * d + d + 1) * V ^ (k + 1) := by ring

/-- At fixed `k`, `d`, the bill is `Θ(V^(k + 1))`. -/
theorem isTheta_pow_succ (k d : ℕ) :
    (fun V => (bill V k d : ℝ)) =Θ[atTop] fun V => (V : ℝ) ^ (k + 1) := by
  have key := isTheta_of_le (fun V => bill V k d) (fun V => V ^ (k + 1))
    (k * d + d * d + d + 1) 2 2
    (fun V hV => bill_le k d (by omega))
    (fun V hV => pow_succ_le_bill k d hV)
  exact isTheta_cast_pow _ (k + 1) key

/-- At fixed `V ≥ 2` and `d ≥ 1`, the bill is `Θ(k V^k)`. -/
theorem isTheta_mul_pow {V d : ℕ} (hV : 2 ≤ V) (hd : 1 ≤ d) :
    (fun k => (bill V k d : ℝ)) =Θ[atTop] fun k => (k : ℝ) * (V : ℝ) ^ k := by
  have key := isTheta_of_le (fun k => bill V k d) (fun k => k * V ^ k)
    (d + d * d + d * V + V) 1 1
    (fun k hk => by
      show bill V k d ≤ _ * (k * V ^ k)
      unfold bill
      have : k * d + d * d + d * V + (V - 1) ≤ (d + d * d + d * V + V) * k := by
        have h1 : d * d + d * V + V ≤ (d * d + d * V + V) * k := Nat.le_mul_of_pos_right _ hk
        have h2 : V - 1 ≤ V := Nat.sub_le V 1
        nlinarith
      calc V ^ k * (k * d + d * d + d * V + (V - 1)) ≤ V ^ k * ((d + d * d + d * V + V) * k) :=
            Nat.mul_le_mul_left _ this
        _ = (d + d * d + d * V + V) * (k * V ^ k) := by ring)
    (fun k hk => by
      show k * V ^ k ≤ 1 * bill V k d
      unfold bill
      have : k ≤ k * d + d * d + d * V + (V - 1) := by nlinarith
      calc k * V ^ k = V ^ k * k := by ring
        _ ≤ V ^ k * (k * d + d * d + d * V + (V - 1)) := Nat.mul_le_mul_left _ this
        _ = 1 * (V ^ k * (k * d + d * d + d * V + (V - 1))) := by ring)
  exact isTheta_cast _ _ _ (fun k => by push_cast; ring) key

end BruteForce
