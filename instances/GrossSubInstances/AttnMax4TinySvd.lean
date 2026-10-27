import Protected.N_attn_max4_tiny_v4d4_s0_c134_hce1cd1a24b2e255c
import GrossSub.Check

/-!
# Instance: entry 9 on the network `attn_max4_tiny-v4d4-s0`

`tests/attn_max4_tiny` of the pipeline, network `attn_max4_tiny-v4d4-s0` (a development network):
`n = 4` positions, `V = 4` tokens, width `d = 4`, head size `h = 4`. Gross et al.'s configuration
`EUPU-max-diff-exact--attn-drop-average-query-per-output-logit-reasoning--attn-err-svd` (method
codes `err = 0`, `eu = 1`), with their plan of gaps and the certificate of the protected module (97
numbers).

The kernel evaluates the checker on the protected weights and certificate (`D_instance`): 134 of the
256 inputs certified, for a bill of 4,246 (`GrossSub.subBill 0 1 gap 4 4 4 4`). The evaluation nests
deeper than Lean's default recursion limit allows the `decide` tactic, hence the option.
-/

namespace GrossSubInstances.AttnMax4TinySvd

open CompactCheck GrossSub Protected.N_attn_max4_tiny_v4d4_s0_c134_hce1cd1a24b2e255c

/-- Their plan of gaps, by the ranks of the query, of the largest token, and the number of positions
    holding a token other than the largest. -/
def gaps : List (List (List ℕ)) :=
  [
    [[1, 1, 1, 1], [1, 1, 1, 1], [1, 2, 1, 1], [1, 2, 2, 2]],
    [[1, 1, 1, 1], [1, 1, 1, 1], [1, 1, 1, 1], [1, 2, 2, 2]],
    [[1, 1, 1, 1], [1, 1, 1, 1], [1, 1, 1, 1], [1, 1, 1, 1]],
    [[1, 1, 1, 1], [1, 1, 1, 1], [1, 1, 1, 1], [1, 1, 2, 2]]]

/-- The gap of a class (one where the plan has none). -/
def gap (rq lam c : ℕ) : ℕ := ((gaps.getD rq []).getD lam []).getD c 1

/-- The checker on this network: the label is the largest token. -/
def D : Checker := fun I => check I true 0 1 gap graph task

theorem graph_isAttn : AttnClasses.IsAttn graph := ⟨rfl, rfl, by decide, by decide⟩

theorem D_sound : ∀ (w : Weights ℚ) (c : Cert) (n : Nat) (cost : Cost),
    CostM.exec (D Interp.counting) ⟨w, c⟩ = some (n, cost) → n ≤ numCorrect graph w task :=
  fun w c n cost h => check_sound graph_isAttn true 0 1 gap w c n cost h

set_option maxRecDepth 100000 in
theorem D_instance :
    CostM.billed (D Interp.counting) ⟨weights, cert⟩ = some (134, 4246) := by
  decide +kernel

theorem performance : Target := by
  change claimedCount ≤ numCorrect graph weights task
  obtain ⟨cost, h⟩ := CostM.exec_of_billed D_instance
  exact D_sound weights cert 134 cost h

end GrossSubInstances.AttnMax4TinySvd
