import Protected.N_attn_min2_tiny_v8d4_s1_c38_hf9acc86549f1e885
import GrossSub.Check

/-!
# Instance: entry 9 on the network `attn_min2_tiny-v8d4-s1`

`tests/attn_min2_tiny` of the pipeline, network `attn_min2_tiny-v8d4-s1` (a development network):
`n = 2` positions, `V = 8` tokens, width `d = 4`, head size `h = 4`. Gross et al.'s configuration
`EUPU-max-diff-exact--attn-mean-query+diff--attn-err-max-diff-subproduct` (method codes `err = 4`,
`eu = 1`), with their plan of gaps and the certificate of the protected module (92 numbers).

The kernel evaluates the checker on the protected weights and certificate (`D_instance`): 38 of the
64 inputs certified, for a bill of 7,407 (`GrossSub.subBill 4 1 gap 8 2 4 4`). The evaluation nests
deeper than Lean's default recursion limit allows the `decide` tactic, hence the option.
-/

namespace GrossSubInstances.AttnMin2TinySub

open CompactCheck GrossSub Protected.N_attn_min2_tiny_v8d4_s1_c38_hf9acc86549f1e885

/-- Their plan of gaps, by the ranks of the query, of the largest token, and the number of positions
    holding a token other than the largest. -/
def gaps : List (List (List ℕ)) :=
  [
    [[1, 1], [1, 1], [1, 1], [1, 1], [1, 4], [1, 5], [1, 6], [1, 7]],
    [[1, 1], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1], [1, 3]],
    [[1, 1], [1, 1], [1, 1], [1, 1], [1, 2], [1, 2], [1, 3], [1, 3]],
    [[1, 1], [1, 1], [1, 1], [1, 1], [1, 1], [1, 2], [1, 3], [1, 3]],
    [[1, 1], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1], [1, 3]],
    [[1, 1], [1, 1], [1, 1], [1, 1], [1, 1], [1, 2], [1, 1], [1, 1]],
    [[1, 1], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1], [1, 3], [1, 1]],
    [[1, 1], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1], [1, 1], [1, 4]]]

/-- The gap of a class (one where the plan has none). -/
def gap (rq lam c : ℕ) : ℕ := ((gaps.getD rq []).getD lam []).getD c 1

/-- The checker on this network: the label is the smallest token. -/
def D : Checker := fun I => check I false 4 1 gap graph task

theorem graph_isAttn : AttnClasses.IsAttn graph := ⟨rfl, rfl, by decide, by decide⟩

theorem D_sound : ∀ (w : Weights ℚ) (c : Cert) (n : Nat) (cost : Cost),
    CostM.exec (D Interp.counting) ⟨w, c⟩ = some (n, cost) → n ≤ numCorrect graph w task :=
  fun w c n cost h => check_sound graph_isAttn false 4 1 gap w c n cost h

set_option maxRecDepth 100000 in
theorem D_instance :
    CostM.billed (D Interp.counting) ⟨weights, cert⟩ = some (38, 7407) := by
  decide +kernel

theorem performance : Target := by
  change claimedCount ≤ numCorrect graph weights task
  obtain ⟨cost, h⟩ := CostM.exec_of_billed D_instance
  exact D_sound weights cert 38 cost h

end GrossSubInstances.AttnMin2TinySub
