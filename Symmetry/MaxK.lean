import Symmetry.Checker
import LinearMaxK.Runs

/-!
# Symmetry on the linear max-of-k family

A network of the family sums its one-hot input over the positions first (`symmetricNet`), and the
label, the largest token, does not depend on the order. On well-formed weights the single-input
rule is exact (`singleOk_iff`) and a forward pass costs `k d + d² + d V + V - 1`. So symmetry
certifies exactly `numCorrect`, at `(V + k - 1).choose k` forward passes instead of brute force's
`V^k` (`check_billed_maxK`).
-/

namespace Symmetry

open CompactCheck Common LinearMaxK

/-- A network of the family is symmetric in its positions. -/
theorem symmetricNet_of_isLinearMaxK {g : Graph} (hg : IsLinearMaxK g = true) :
    symmetricNet g = true := by
  obtain ⟨hn, ho, -, -⟩ := isLinearMaxK_spec hg
  unfold symmetricNet
  rw [hn, ho]
  decide

open Classical in
/-- **Symmetry on the family.** On well-formed weights the count is exactly `numCorrect`, and the
    bill is `(V + k - 1).choose k` forward passes of `k d + d² + d V + V - 1` operations each. -/
theorem check_billed_maxK {g : Graph} (hg : IsLinearMaxK g = true) {w : Weights ℚ} {d : ℕ}
    {tE tL tU : Tensor ℚ} (hw : WF w g.values d tE tL tU) (c : Cert) :
    CostM.billed (check Interp.counting g (maxTask g.positions g.values)) ⟨w, c⟩ =
      some (numCorrect g w (maxTask g.positions g.values),
        (g.values + g.positions - 1).choose g.positions *
          (g.positions * d + d * d + d * g.values + (g.values - 1))) := by
  obtain ⟨-, -, hk, -⟩ := isLinearMaxK_spec hg
  rw [check_billed (k := g.positions) (V := g.values) rfl hk (symmetricNet_of_isLinearMaxK hg) rfl
    (singleCost_family hg hw) c]
  congr 2
  unfold numCorrect
  refine List.countP_congr fun x hx => ?_
  obtain ⟨hlen, hxV⟩ := (mem_allInputs_replicate (k := g.positions) (V := g.values)).mp hx
  simp [singleOk_iff hg hw hlen hxV]

end Symmetry
