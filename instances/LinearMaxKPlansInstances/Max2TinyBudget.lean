import Protected.N_max2_tiny_v8_s0_c20
import LinearMaxKPlans.Sound

/-!
# Instance: a plan on the tiny max-of-2 network

`tests/max2_tiny` of the pipeline, network `max2_tiny-v8-s0`: `k = 2` positions, `V = 8` tokens,
width `d = 4`. The protected module is the one the acceptance service generates for a claim of 20.

The plan is the one the pipeline's baseline 04 chooses at knob 0.75 (a third of the full proof's
leaf work): the whole group of 7, and the inputs of the group of 6 whose tokens are all at least 4.
The kernel evaluates the checker on the protected weights (`D_instance`): 15 + 5 = 20 inputs
certified, for a bill of 568 (`LinearMaxKPlans.billPlan`).
-/

namespace LinearMaxKPlansInstances.Max2TinyBudget

open CompactCheck LinearMaxKPlans Protected.N_max2_tiny_v8_s0_c20

/-- The plan: two tails. -/
def plan : List Piece := [⟨7, 0, 7⟩, ⟨6, 4, 6⟩]

/-- The checker of the plan on this network. -/
def D : Checker := fun I => check I plan graph task

theorem D_sound : ∀ (w : Weights ℚ) (c : Cert) (n : Nat) (cost : Cost),
    CostM.exec (D Interp.counting) ⟨w, c⟩ = some (n, cost) → n ≤ numCorrect graph w task :=
  fun w c n cost h => check_sound (g := graph) (by decide) plan w c n cost h

theorem D_instance : CostM.billed (D Interp.counting) ⟨weights, cert⟩ = some (20, 568) := by
  decide +kernel

theorem performance : Target := by
  change claimedCount ≤ numCorrect graph weights task
  obtain ⟨cost, h⟩ := CostM.exec_of_billed D_instance
  exact D_sound weights cert 20 cost h

end LinearMaxKPlansInstances.Max2TinyBudget
