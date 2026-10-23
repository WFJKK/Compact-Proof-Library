import Protected.N_attn_min4_tiny_v4d4_s0_c256
import AttnClasses.Sound

/-!
# Instance: entry 6 on the tiny attention min-of-4 network

`tests/attn_min4_tiny` of the pipeline, network `attn_min4_tiny-v4d4-s0` (a development network): `n = 4` positions,
`V = 4` tokens, width `d = 4`, head size `h = 4`. The protected module is the one the acceptance
service generates for a claim of 256.

The kernel evaluates the checker on the protected weights (`D_instance`): all 256 inputs certified,
for a bill of 2,151 (`AttnClasses.bill 4 4 4 4`). The evaluation nests deeper than Lean's
default recursion limit allows the `decide` tactic, hence the option.
-/

namespace AttnClassesInstances.AttnMin4Tiny

open CompactCheck AttnClasses Protected.N_attn_min4_tiny_v4d4_s0_c256

/-- The checker on this network: the label is the smallest token. -/
def D : Checker := fun I => check I false graph task

theorem graph_isAttn : IsAttn graph := ⟨rfl, rfl, by decide, by decide⟩

theorem D_sound : ∀ (w : Weights ℚ) (c : Cert) (n : Nat) (cost : Cost),
    CostM.exec (D Interp.counting) ⟨w, c⟩ = some (n, cost) → n ≤ numCorrect graph w task :=
  fun w c n cost h => check_sound graph_isAttn false w c n cost h

set_option maxRecDepth 100000 in
theorem D_instance : CostM.billed (D Interp.counting) ⟨weights, cert⟩ = some (256, 2151) := by
  decide +kernel

theorem performance : Target := by
  change claimedCount ≤ numCorrect graph weights task
  obtain ⟨cost, h⟩ := CostM.exec_of_billed D_instance
  exact D_sound weights cert 256 cost h

end AttnClassesInstances.AttnMin4Tiny
