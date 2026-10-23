import Protected.N_max2_tiny_v8_s0_c64
import LinearMaxK.Sound

/-!
# Instance: the tiny max-of-2 network

`tests/max2_tiny` of the pipeline, network `max2_tiny-v8-s0`: `k = 2` positions, `V = 8` tokens,
width `d = 4`. The protected module is the one the acceptance service generates for a claim of 64.

The general layer's checker, on this graph and task, with its soundness theorem specialised; the
kernel evaluates the checker on the protected weights (`D_instance`): all 64 inputs certified, for a
bill of 1072, which is `bill 2 8 4` (`LinearMaxK.bill_eq`).
-/

namespace LinearMaxKInstances.Max2Tiny

open CompactCheck LinearMaxK Protected.N_max2_tiny_v8_s0_c64

/-- The checker on this network. -/
def D : Checker := fun I => check I graph task

theorem D_sound : ∀ (w : Weights ℚ) (c : Cert) (n : Nat) (cost : Cost),
    CostM.exec (D Interp.counting) ⟨w, c⟩ = some (n, cost) → n ≤ numCorrect graph w task :=
  fun w c n cost h => check_sound (g := graph) (by decide) w c n cost h

theorem D_instance : CostM.billed (D Interp.counting) ⟨weights, cert⟩ = some (64, 1072) := by
  decide +kernel

theorem performance : Target := by
  change claimedCount ≤ numCorrect graph weights task
  obtain ⟨cost, h⟩ := CostM.exec_of_billed D_instance
  exact D_sound weights cert 64 cost h

end LinearMaxKInstances.Max2Tiny
