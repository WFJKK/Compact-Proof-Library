import Protected.N_attn_min2_tiny_v8d4_s1_c64
import AttnClasses.Sound

/-!
# Instance: entry 6 on the tiny attention min-of-2 network

`tests/attn_min2_tiny` of the pipeline, network `attn_min2_tiny-v8d4-s1` (a development network): `n = 2` positions,
`V = 8` tokens, width `d = 4`, head size `h = 4`. The protected module is the one the acceptance
service generates for a claim of 64.

The kernel evaluates the checker on the protected weights (`D_instance`): all 64 inputs certified,
for a bill of 3,381 (`AttnClasses.bill 8 2 4 4`). The evaluation nests deeper than Lean's
default recursion limit allows the `decide` tactic, hence the option.
-/

namespace AttnClassesInstances.AttnMin2Tiny

open CompactCheck AttnClasses Protected.N_attn_min2_tiny_v8d4_s1_c64

/-- The checker on this network: the label is the smallest token. -/
def D : Checker := fun I => check I false graph task

theorem graph_isAttn : IsAttn graph := ⟨rfl, rfl, by decide, by decide⟩

theorem D_sound : ∀ (w : Weights ℚ) (c : Cert) (n : Nat) (cost : Cost),
    CostM.exec (D Interp.counting) ⟨w, c⟩ = some (n, cost) → n ≤ numCorrect graph w task :=
  fun w c n cost h => check_sound graph_isAttn false w c n cost h

set_option maxRecDepth 100000 in
theorem D_instance : CostM.billed (D Interp.counting) ⟨weights, cert⟩ = some (64, 3381) := by
  decide +kernel

theorem performance : Target := by
  change claimedCount ≤ numCorrect graph weights task
  obtain ⟨cost, h⟩ := CostM.exec_of_billed D_instance
  exact D_sound weights cert 64 cost h

end AttnClassesInstances.AttnMin2Tiny
