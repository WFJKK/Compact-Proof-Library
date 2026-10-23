import BruteForce.Checker
import LinearMaxK.Runs

/-!
# Brute force on the linear max-of-k family

On a network of the family with well-formed weights the single-input rule is exact: it passes
exactly the inputs the network answers correctly (`singleOk_iff`). A forward pass costs
`k d + d² + d V + V - 1` operations (`singleCost_family`). So brute force certifies exactly
`numCorrect`, at a bill of `V^k` forward passes (`check_billed_maxK`).
-/

namespace BruteForce

open CompactCheck Common LinearMaxK

/-- The input space has as many inputs as the product of its sizes. -/
theorem length_allInputs : ∀ s : List ℕ, (allInputs s).length = s.prod
  | [] => rfl
  | v :: vs => by
    simp [allInputs, List.length_flatMap, length_allInputs vs]

open Classical in
/-- **Brute force on the family.** On well-formed weights the count is exactly `numCorrect`, and the
    bill is `V^k` forward passes of `k d + d² + d V + V - 1` operations each. -/
theorem check_billed_maxK {g : Graph} (hg : IsLinearMaxK g = true) {w : Weights ℚ} {d : ℕ}
    {tE tL tU : Tensor ℚ} (hw : WF w g.values d tE tL tU) (c : Cert) :
    CostM.billed (check Interp.counting g (maxTask g.positions g.values)) ⟨w, c⟩ =
      some (numCorrect g w (maxTask g.positions g.values),
        g.values ^ g.positions * (g.positions * d + d * d + d * g.values + (g.values - 1))) := by
  rw [check_billed (singleCost_family hg hw) c]
  congr 2
  · unfold numCorrect
    refine List.countP_congr fun x hx => ?_
    obtain ⟨hlen, hxV⟩ := (mem_allInputs_replicate (k := g.positions) (V := g.values)).mp hx
    simp [singleOk_iff hg hw hlen hxV]
  · simp [maxTask, length_allInputs, List.prod_replicate]

end BruteForce
