import Protected.N_attn_min4_tiny_v4d4_s0_c256
import BruteForce.General

/-!
# Instance: brute force on the attention network `attn_min4_tiny-v4d4-s0`

Written by `scripts/make_brute_general_instance.py`. `n = 4` positions, `V = 4` tokens, width
`d = 4`, head size `h = 4`: 256 inputs, each a forward pass of the general single rule charged
287. One fact per input, each decided by the kernel on its own; `D_instance` puts them together
(`BruteForce.countGSingles_run`): all 256 inputs certified, for a bill of 256 * 287 = 73,472.
-/

namespace BruteForceInstances.AttnMin4Tiny

open CompactCheck BruteForce Protected.N_attn_min4_tiny_v4d4_s0_c256

/-- Brute force with the general single rule on this network. -/
def D : Checker := fun I => checkGeneral I graph task

theorem D_sound : ∀ (w : Weights ℚ) (c : Cert) (n : Nat) (cost : Cost),
    CostM.exec (D Interp.counting) ⟨w, c⟩ = some (n, cost) → n ≤ numCorrect graph w task :=
  fun w c n cost h => checkGeneral_sound w c n cost h

/-- The general single rule's verdict and charge on input `x` of the protected weights. -/
abbrev run1 (x : Input) : Option (Bool × Nat) := gsingleOn weights graph task x

theorem in_0_0_0_0 : run1 [0, 0, 0, 0] = some (true, 287) := by
  decide +kernel

theorem in_0_0_0_1 : run1 [0, 0, 0, 1] = some (true, 287) := by
  decide +kernel

theorem in_0_0_0_2 : run1 [0, 0, 0, 2] = some (true, 287) := by
  decide +kernel

theorem in_0_0_0_3 : run1 [0, 0, 0, 3] = some (true, 287) := by
  decide +kernel

theorem in_0_0_1_0 : run1 [0, 0, 1, 0] = some (true, 287) := by
  decide +kernel

theorem in_0_0_1_1 : run1 [0, 0, 1, 1] = some (true, 287) := by
  decide +kernel

theorem in_0_0_1_2 : run1 [0, 0, 1, 2] = some (true, 287) := by
  decide +kernel

theorem in_0_0_1_3 : run1 [0, 0, 1, 3] = some (true, 287) := by
  decide +kernel

theorem in_0_0_2_0 : run1 [0, 0, 2, 0] = some (true, 287) := by
  decide +kernel

theorem in_0_0_2_1 : run1 [0, 0, 2, 1] = some (true, 287) := by
  decide +kernel

theorem in_0_0_2_2 : run1 [0, 0, 2, 2] = some (true, 287) := by
  decide +kernel

theorem in_0_0_2_3 : run1 [0, 0, 2, 3] = some (true, 287) := by
  decide +kernel

theorem in_0_0_3_0 : run1 [0, 0, 3, 0] = some (true, 287) := by
  decide +kernel

theorem in_0_0_3_1 : run1 [0, 0, 3, 1] = some (true, 287) := by
  decide +kernel

theorem in_0_0_3_2 : run1 [0, 0, 3, 2] = some (true, 287) := by
  decide +kernel

theorem in_0_0_3_3 : run1 [0, 0, 3, 3] = some (true, 287) := by
  decide +kernel

theorem in_0_1_0_0 : run1 [0, 1, 0, 0] = some (true, 287) := by
  decide +kernel

theorem in_0_1_0_1 : run1 [0, 1, 0, 1] = some (true, 287) := by
  decide +kernel

theorem in_0_1_0_2 : run1 [0, 1, 0, 2] = some (true, 287) := by
  decide +kernel

theorem in_0_1_0_3 : run1 [0, 1, 0, 3] = some (true, 287) := by
  decide +kernel

theorem in_0_1_1_0 : run1 [0, 1, 1, 0] = some (true, 287) := by
  decide +kernel

theorem in_0_1_1_1 : run1 [0, 1, 1, 1] = some (true, 287) := by
  decide +kernel

theorem in_0_1_1_2 : run1 [0, 1, 1, 2] = some (true, 287) := by
  decide +kernel

theorem in_0_1_1_3 : run1 [0, 1, 1, 3] = some (true, 287) := by
  decide +kernel

theorem in_0_1_2_0 : run1 [0, 1, 2, 0] = some (true, 287) := by
  decide +kernel

theorem in_0_1_2_1 : run1 [0, 1, 2, 1] = some (true, 287) := by
  decide +kernel

theorem in_0_1_2_2 : run1 [0, 1, 2, 2] = some (true, 287) := by
  decide +kernel

theorem in_0_1_2_3 : run1 [0, 1, 2, 3] = some (true, 287) := by
  decide +kernel

theorem in_0_1_3_0 : run1 [0, 1, 3, 0] = some (true, 287) := by
  decide +kernel

theorem in_0_1_3_1 : run1 [0, 1, 3, 1] = some (true, 287) := by
  decide +kernel

theorem in_0_1_3_2 : run1 [0, 1, 3, 2] = some (true, 287) := by
  decide +kernel

theorem in_0_1_3_3 : run1 [0, 1, 3, 3] = some (true, 287) := by
  decide +kernel

theorem in_0_2_0_0 : run1 [0, 2, 0, 0] = some (true, 287) := by
  decide +kernel

theorem in_0_2_0_1 : run1 [0, 2, 0, 1] = some (true, 287) := by
  decide +kernel

theorem in_0_2_0_2 : run1 [0, 2, 0, 2] = some (true, 287) := by
  decide +kernel

theorem in_0_2_0_3 : run1 [0, 2, 0, 3] = some (true, 287) := by
  decide +kernel

theorem in_0_2_1_0 : run1 [0, 2, 1, 0] = some (true, 287) := by
  decide +kernel

theorem in_0_2_1_1 : run1 [0, 2, 1, 1] = some (true, 287) := by
  decide +kernel

theorem in_0_2_1_2 : run1 [0, 2, 1, 2] = some (true, 287) := by
  decide +kernel

theorem in_0_2_1_3 : run1 [0, 2, 1, 3] = some (true, 287) := by
  decide +kernel

theorem in_0_2_2_0 : run1 [0, 2, 2, 0] = some (true, 287) := by
  decide +kernel

theorem in_0_2_2_1 : run1 [0, 2, 2, 1] = some (true, 287) := by
  decide +kernel

theorem in_0_2_2_2 : run1 [0, 2, 2, 2] = some (true, 287) := by
  decide +kernel

theorem in_0_2_2_3 : run1 [0, 2, 2, 3] = some (true, 287) := by
  decide +kernel

theorem in_0_2_3_0 : run1 [0, 2, 3, 0] = some (true, 287) := by
  decide +kernel

theorem in_0_2_3_1 : run1 [0, 2, 3, 1] = some (true, 287) := by
  decide +kernel

theorem in_0_2_3_2 : run1 [0, 2, 3, 2] = some (true, 287) := by
  decide +kernel

theorem in_0_2_3_3 : run1 [0, 2, 3, 3] = some (true, 287) := by
  decide +kernel

theorem in_0_3_0_0 : run1 [0, 3, 0, 0] = some (true, 287) := by
  decide +kernel

theorem in_0_3_0_1 : run1 [0, 3, 0, 1] = some (true, 287) := by
  decide +kernel

theorem in_0_3_0_2 : run1 [0, 3, 0, 2] = some (true, 287) := by
  decide +kernel

theorem in_0_3_0_3 : run1 [0, 3, 0, 3] = some (true, 287) := by
  decide +kernel

theorem in_0_3_1_0 : run1 [0, 3, 1, 0] = some (true, 287) := by
  decide +kernel

theorem in_0_3_1_1 : run1 [0, 3, 1, 1] = some (true, 287) := by
  decide +kernel

theorem in_0_3_1_2 : run1 [0, 3, 1, 2] = some (true, 287) := by
  decide +kernel

theorem in_0_3_1_3 : run1 [0, 3, 1, 3] = some (true, 287) := by
  decide +kernel

theorem in_0_3_2_0 : run1 [0, 3, 2, 0] = some (true, 287) := by
  decide +kernel

theorem in_0_3_2_1 : run1 [0, 3, 2, 1] = some (true, 287) := by
  decide +kernel

theorem in_0_3_2_2 : run1 [0, 3, 2, 2] = some (true, 287) := by
  decide +kernel

theorem in_0_3_2_3 : run1 [0, 3, 2, 3] = some (true, 287) := by
  decide +kernel

theorem in_0_3_3_0 : run1 [0, 3, 3, 0] = some (true, 287) := by
  decide +kernel

theorem in_0_3_3_1 : run1 [0, 3, 3, 1] = some (true, 287) := by
  decide +kernel

theorem in_0_3_3_2 : run1 [0, 3, 3, 2] = some (true, 287) := by
  decide +kernel

theorem in_0_3_3_3 : run1 [0, 3, 3, 3] = some (true, 287) := by
  decide +kernel

theorem in_1_0_0_0 : run1 [1, 0, 0, 0] = some (true, 287) := by
  decide +kernel

theorem in_1_0_0_1 : run1 [1, 0, 0, 1] = some (true, 287) := by
  decide +kernel

theorem in_1_0_0_2 : run1 [1, 0, 0, 2] = some (true, 287) := by
  decide +kernel

theorem in_1_0_0_3 : run1 [1, 0, 0, 3] = some (true, 287) := by
  decide +kernel

theorem in_1_0_1_0 : run1 [1, 0, 1, 0] = some (true, 287) := by
  decide +kernel

theorem in_1_0_1_1 : run1 [1, 0, 1, 1] = some (true, 287) := by
  decide +kernel

theorem in_1_0_1_2 : run1 [1, 0, 1, 2] = some (true, 287) := by
  decide +kernel

theorem in_1_0_1_3 : run1 [1, 0, 1, 3] = some (true, 287) := by
  decide +kernel

theorem in_1_0_2_0 : run1 [1, 0, 2, 0] = some (true, 287) := by
  decide +kernel

theorem in_1_0_2_1 : run1 [1, 0, 2, 1] = some (true, 287) := by
  decide +kernel

theorem in_1_0_2_2 : run1 [1, 0, 2, 2] = some (true, 287) := by
  decide +kernel

theorem in_1_0_2_3 : run1 [1, 0, 2, 3] = some (true, 287) := by
  decide +kernel

theorem in_1_0_3_0 : run1 [1, 0, 3, 0] = some (true, 287) := by
  decide +kernel

theorem in_1_0_3_1 : run1 [1, 0, 3, 1] = some (true, 287) := by
  decide +kernel

theorem in_1_0_3_2 : run1 [1, 0, 3, 2] = some (true, 287) := by
  decide +kernel

theorem in_1_0_3_3 : run1 [1, 0, 3, 3] = some (true, 287) := by
  decide +kernel

theorem in_1_1_0_0 : run1 [1, 1, 0, 0] = some (true, 287) := by
  decide +kernel

theorem in_1_1_0_1 : run1 [1, 1, 0, 1] = some (true, 287) := by
  decide +kernel

theorem in_1_1_0_2 : run1 [1, 1, 0, 2] = some (true, 287) := by
  decide +kernel

theorem in_1_1_0_3 : run1 [1, 1, 0, 3] = some (true, 287) := by
  decide +kernel

theorem in_1_1_1_0 : run1 [1, 1, 1, 0] = some (true, 287) := by
  decide +kernel

theorem in_1_1_1_1 : run1 [1, 1, 1, 1] = some (true, 287) := by
  decide +kernel

theorem in_1_1_1_2 : run1 [1, 1, 1, 2] = some (true, 287) := by
  decide +kernel

theorem in_1_1_1_3 : run1 [1, 1, 1, 3] = some (true, 287) := by
  decide +kernel

theorem in_1_1_2_0 : run1 [1, 1, 2, 0] = some (true, 287) := by
  decide +kernel

theorem in_1_1_2_1 : run1 [1, 1, 2, 1] = some (true, 287) := by
  decide +kernel

theorem in_1_1_2_2 : run1 [1, 1, 2, 2] = some (true, 287) := by
  decide +kernel

theorem in_1_1_2_3 : run1 [1, 1, 2, 3] = some (true, 287) := by
  decide +kernel

theorem in_1_1_3_0 : run1 [1, 1, 3, 0] = some (true, 287) := by
  decide +kernel

theorem in_1_1_3_1 : run1 [1, 1, 3, 1] = some (true, 287) := by
  decide +kernel

theorem in_1_1_3_2 : run1 [1, 1, 3, 2] = some (true, 287) := by
  decide +kernel

theorem in_1_1_3_3 : run1 [1, 1, 3, 3] = some (true, 287) := by
  decide +kernel

theorem in_1_2_0_0 : run1 [1, 2, 0, 0] = some (true, 287) := by
  decide +kernel

theorem in_1_2_0_1 : run1 [1, 2, 0, 1] = some (true, 287) := by
  decide +kernel

theorem in_1_2_0_2 : run1 [1, 2, 0, 2] = some (true, 287) := by
  decide +kernel

theorem in_1_2_0_3 : run1 [1, 2, 0, 3] = some (true, 287) := by
  decide +kernel

theorem in_1_2_1_0 : run1 [1, 2, 1, 0] = some (true, 287) := by
  decide +kernel

theorem in_1_2_1_1 : run1 [1, 2, 1, 1] = some (true, 287) := by
  decide +kernel

theorem in_1_2_1_2 : run1 [1, 2, 1, 2] = some (true, 287) := by
  decide +kernel

theorem in_1_2_1_3 : run1 [1, 2, 1, 3] = some (true, 287) := by
  decide +kernel

theorem in_1_2_2_0 : run1 [1, 2, 2, 0] = some (true, 287) := by
  decide +kernel

theorem in_1_2_2_1 : run1 [1, 2, 2, 1] = some (true, 287) := by
  decide +kernel

theorem in_1_2_2_2 : run1 [1, 2, 2, 2] = some (true, 287) := by
  decide +kernel

theorem in_1_2_2_3 : run1 [1, 2, 2, 3] = some (true, 287) := by
  decide +kernel

theorem in_1_2_3_0 : run1 [1, 2, 3, 0] = some (true, 287) := by
  decide +kernel

theorem in_1_2_3_1 : run1 [1, 2, 3, 1] = some (true, 287) := by
  decide +kernel

theorem in_1_2_3_2 : run1 [1, 2, 3, 2] = some (true, 287) := by
  decide +kernel

theorem in_1_2_3_3 : run1 [1, 2, 3, 3] = some (true, 287) := by
  decide +kernel

theorem in_1_3_0_0 : run1 [1, 3, 0, 0] = some (true, 287) := by
  decide +kernel

theorem in_1_3_0_1 : run1 [1, 3, 0, 1] = some (true, 287) := by
  decide +kernel

theorem in_1_3_0_2 : run1 [1, 3, 0, 2] = some (true, 287) := by
  decide +kernel

theorem in_1_3_0_3 : run1 [1, 3, 0, 3] = some (true, 287) := by
  decide +kernel

theorem in_1_3_1_0 : run1 [1, 3, 1, 0] = some (true, 287) := by
  decide +kernel

theorem in_1_3_1_1 : run1 [1, 3, 1, 1] = some (true, 287) := by
  decide +kernel

theorem in_1_3_1_2 : run1 [1, 3, 1, 2] = some (true, 287) := by
  decide +kernel

theorem in_1_3_1_3 : run1 [1, 3, 1, 3] = some (true, 287) := by
  decide +kernel

theorem in_1_3_2_0 : run1 [1, 3, 2, 0] = some (true, 287) := by
  decide +kernel

theorem in_1_3_2_1 : run1 [1, 3, 2, 1] = some (true, 287) := by
  decide +kernel

theorem in_1_3_2_2 : run1 [1, 3, 2, 2] = some (true, 287) := by
  decide +kernel

theorem in_1_3_2_3 : run1 [1, 3, 2, 3] = some (true, 287) := by
  decide +kernel

theorem in_1_3_3_0 : run1 [1, 3, 3, 0] = some (true, 287) := by
  decide +kernel

theorem in_1_3_3_1 : run1 [1, 3, 3, 1] = some (true, 287) := by
  decide +kernel

theorem in_1_3_3_2 : run1 [1, 3, 3, 2] = some (true, 287) := by
  decide +kernel

theorem in_1_3_3_3 : run1 [1, 3, 3, 3] = some (true, 287) := by
  decide +kernel

theorem in_2_0_0_0 : run1 [2, 0, 0, 0] = some (true, 287) := by
  decide +kernel

theorem in_2_0_0_1 : run1 [2, 0, 0, 1] = some (true, 287) := by
  decide +kernel

theorem in_2_0_0_2 : run1 [2, 0, 0, 2] = some (true, 287) := by
  decide +kernel

theorem in_2_0_0_3 : run1 [2, 0, 0, 3] = some (true, 287) := by
  decide +kernel

theorem in_2_0_1_0 : run1 [2, 0, 1, 0] = some (true, 287) := by
  decide +kernel

theorem in_2_0_1_1 : run1 [2, 0, 1, 1] = some (true, 287) := by
  decide +kernel

theorem in_2_0_1_2 : run1 [2, 0, 1, 2] = some (true, 287) := by
  decide +kernel

theorem in_2_0_1_3 : run1 [2, 0, 1, 3] = some (true, 287) := by
  decide +kernel

theorem in_2_0_2_0 : run1 [2, 0, 2, 0] = some (true, 287) := by
  decide +kernel

theorem in_2_0_2_1 : run1 [2, 0, 2, 1] = some (true, 287) := by
  decide +kernel

theorem in_2_0_2_2 : run1 [2, 0, 2, 2] = some (true, 287) := by
  decide +kernel

theorem in_2_0_2_3 : run1 [2, 0, 2, 3] = some (true, 287) := by
  decide +kernel

theorem in_2_0_3_0 : run1 [2, 0, 3, 0] = some (true, 287) := by
  decide +kernel

theorem in_2_0_3_1 : run1 [2, 0, 3, 1] = some (true, 287) := by
  decide +kernel

theorem in_2_0_3_2 : run1 [2, 0, 3, 2] = some (true, 287) := by
  decide +kernel

theorem in_2_0_3_3 : run1 [2, 0, 3, 3] = some (true, 287) := by
  decide +kernel

theorem in_2_1_0_0 : run1 [2, 1, 0, 0] = some (true, 287) := by
  decide +kernel

theorem in_2_1_0_1 : run1 [2, 1, 0, 1] = some (true, 287) := by
  decide +kernel

theorem in_2_1_0_2 : run1 [2, 1, 0, 2] = some (true, 287) := by
  decide +kernel

theorem in_2_1_0_3 : run1 [2, 1, 0, 3] = some (true, 287) := by
  decide +kernel

theorem in_2_1_1_0 : run1 [2, 1, 1, 0] = some (true, 287) := by
  decide +kernel

theorem in_2_1_1_1 : run1 [2, 1, 1, 1] = some (true, 287) := by
  decide +kernel

theorem in_2_1_1_2 : run1 [2, 1, 1, 2] = some (true, 287) := by
  decide +kernel

theorem in_2_1_1_3 : run1 [2, 1, 1, 3] = some (true, 287) := by
  decide +kernel

theorem in_2_1_2_0 : run1 [2, 1, 2, 0] = some (true, 287) := by
  decide +kernel

theorem in_2_1_2_1 : run1 [2, 1, 2, 1] = some (true, 287) := by
  decide +kernel

theorem in_2_1_2_2 : run1 [2, 1, 2, 2] = some (true, 287) := by
  decide +kernel

theorem in_2_1_2_3 : run1 [2, 1, 2, 3] = some (true, 287) := by
  decide +kernel

theorem in_2_1_3_0 : run1 [2, 1, 3, 0] = some (true, 287) := by
  decide +kernel

theorem in_2_1_3_1 : run1 [2, 1, 3, 1] = some (true, 287) := by
  decide +kernel

theorem in_2_1_3_2 : run1 [2, 1, 3, 2] = some (true, 287) := by
  decide +kernel

theorem in_2_1_3_3 : run1 [2, 1, 3, 3] = some (true, 287) := by
  decide +kernel

theorem in_2_2_0_0 : run1 [2, 2, 0, 0] = some (true, 287) := by
  decide +kernel

theorem in_2_2_0_1 : run1 [2, 2, 0, 1] = some (true, 287) := by
  decide +kernel

theorem in_2_2_0_2 : run1 [2, 2, 0, 2] = some (true, 287) := by
  decide +kernel

theorem in_2_2_0_3 : run1 [2, 2, 0, 3] = some (true, 287) := by
  decide +kernel

theorem in_2_2_1_0 : run1 [2, 2, 1, 0] = some (true, 287) := by
  decide +kernel

theorem in_2_2_1_1 : run1 [2, 2, 1, 1] = some (true, 287) := by
  decide +kernel

theorem in_2_2_1_2 : run1 [2, 2, 1, 2] = some (true, 287) := by
  decide +kernel

theorem in_2_2_1_3 : run1 [2, 2, 1, 3] = some (true, 287) := by
  decide +kernel

theorem in_2_2_2_0 : run1 [2, 2, 2, 0] = some (true, 287) := by
  decide +kernel

theorem in_2_2_2_1 : run1 [2, 2, 2, 1] = some (true, 287) := by
  decide +kernel

theorem in_2_2_2_2 : run1 [2, 2, 2, 2] = some (true, 287) := by
  decide +kernel

theorem in_2_2_2_3 : run1 [2, 2, 2, 3] = some (true, 287) := by
  decide +kernel

theorem in_2_2_3_0 : run1 [2, 2, 3, 0] = some (true, 287) := by
  decide +kernel

theorem in_2_2_3_1 : run1 [2, 2, 3, 1] = some (true, 287) := by
  decide +kernel

theorem in_2_2_3_2 : run1 [2, 2, 3, 2] = some (true, 287) := by
  decide +kernel

theorem in_2_2_3_3 : run1 [2, 2, 3, 3] = some (true, 287) := by
  decide +kernel

theorem in_2_3_0_0 : run1 [2, 3, 0, 0] = some (true, 287) := by
  decide +kernel

theorem in_2_3_0_1 : run1 [2, 3, 0, 1] = some (true, 287) := by
  decide +kernel

theorem in_2_3_0_2 : run1 [2, 3, 0, 2] = some (true, 287) := by
  decide +kernel

theorem in_2_3_0_3 : run1 [2, 3, 0, 3] = some (true, 287) := by
  decide +kernel

theorem in_2_3_1_0 : run1 [2, 3, 1, 0] = some (true, 287) := by
  decide +kernel

theorem in_2_3_1_1 : run1 [2, 3, 1, 1] = some (true, 287) := by
  decide +kernel

theorem in_2_3_1_2 : run1 [2, 3, 1, 2] = some (true, 287) := by
  decide +kernel

theorem in_2_3_1_3 : run1 [2, 3, 1, 3] = some (true, 287) := by
  decide +kernel

theorem in_2_3_2_0 : run1 [2, 3, 2, 0] = some (true, 287) := by
  decide +kernel

theorem in_2_3_2_1 : run1 [2, 3, 2, 1] = some (true, 287) := by
  decide +kernel

theorem in_2_3_2_2 : run1 [2, 3, 2, 2] = some (true, 287) := by
  decide +kernel

theorem in_2_3_2_3 : run1 [2, 3, 2, 3] = some (true, 287) := by
  decide +kernel

theorem in_2_3_3_0 : run1 [2, 3, 3, 0] = some (true, 287) := by
  decide +kernel

theorem in_2_3_3_1 : run1 [2, 3, 3, 1] = some (true, 287) := by
  decide +kernel

theorem in_2_3_3_2 : run1 [2, 3, 3, 2] = some (true, 287) := by
  decide +kernel

theorem in_2_3_3_3 : run1 [2, 3, 3, 3] = some (true, 287) := by
  decide +kernel

theorem in_3_0_0_0 : run1 [3, 0, 0, 0] = some (true, 287) := by
  decide +kernel

theorem in_3_0_0_1 : run1 [3, 0, 0, 1] = some (true, 287) := by
  decide +kernel

theorem in_3_0_0_2 : run1 [3, 0, 0, 2] = some (true, 287) := by
  decide +kernel

theorem in_3_0_0_3 : run1 [3, 0, 0, 3] = some (true, 287) := by
  decide +kernel

theorem in_3_0_1_0 : run1 [3, 0, 1, 0] = some (true, 287) := by
  decide +kernel

theorem in_3_0_1_1 : run1 [3, 0, 1, 1] = some (true, 287) := by
  decide +kernel

theorem in_3_0_1_2 : run1 [3, 0, 1, 2] = some (true, 287) := by
  decide +kernel

theorem in_3_0_1_3 : run1 [3, 0, 1, 3] = some (true, 287) := by
  decide +kernel

theorem in_3_0_2_0 : run1 [3, 0, 2, 0] = some (true, 287) := by
  decide +kernel

theorem in_3_0_2_1 : run1 [3, 0, 2, 1] = some (true, 287) := by
  decide +kernel

theorem in_3_0_2_2 : run1 [3, 0, 2, 2] = some (true, 287) := by
  decide +kernel

theorem in_3_0_2_3 : run1 [3, 0, 2, 3] = some (true, 287) := by
  decide +kernel

theorem in_3_0_3_0 : run1 [3, 0, 3, 0] = some (true, 287) := by
  decide +kernel

theorem in_3_0_3_1 : run1 [3, 0, 3, 1] = some (true, 287) := by
  decide +kernel

theorem in_3_0_3_2 : run1 [3, 0, 3, 2] = some (true, 287) := by
  decide +kernel

theorem in_3_0_3_3 : run1 [3, 0, 3, 3] = some (true, 287) := by
  decide +kernel

theorem in_3_1_0_0 : run1 [3, 1, 0, 0] = some (true, 287) := by
  decide +kernel

theorem in_3_1_0_1 : run1 [3, 1, 0, 1] = some (true, 287) := by
  decide +kernel

theorem in_3_1_0_2 : run1 [3, 1, 0, 2] = some (true, 287) := by
  decide +kernel

theorem in_3_1_0_3 : run1 [3, 1, 0, 3] = some (true, 287) := by
  decide +kernel

theorem in_3_1_1_0 : run1 [3, 1, 1, 0] = some (true, 287) := by
  decide +kernel

theorem in_3_1_1_1 : run1 [3, 1, 1, 1] = some (true, 287) := by
  decide +kernel

theorem in_3_1_1_2 : run1 [3, 1, 1, 2] = some (true, 287) := by
  decide +kernel

theorem in_3_1_1_3 : run1 [3, 1, 1, 3] = some (true, 287) := by
  decide +kernel

theorem in_3_1_2_0 : run1 [3, 1, 2, 0] = some (true, 287) := by
  decide +kernel

theorem in_3_1_2_1 : run1 [3, 1, 2, 1] = some (true, 287) := by
  decide +kernel

theorem in_3_1_2_2 : run1 [3, 1, 2, 2] = some (true, 287) := by
  decide +kernel

theorem in_3_1_2_3 : run1 [3, 1, 2, 3] = some (true, 287) := by
  decide +kernel

theorem in_3_1_3_0 : run1 [3, 1, 3, 0] = some (true, 287) := by
  decide +kernel

theorem in_3_1_3_1 : run1 [3, 1, 3, 1] = some (true, 287) := by
  decide +kernel

theorem in_3_1_3_2 : run1 [3, 1, 3, 2] = some (true, 287) := by
  decide +kernel

theorem in_3_1_3_3 : run1 [3, 1, 3, 3] = some (true, 287) := by
  decide +kernel

theorem in_3_2_0_0 : run1 [3, 2, 0, 0] = some (true, 287) := by
  decide +kernel

theorem in_3_2_0_1 : run1 [3, 2, 0, 1] = some (true, 287) := by
  decide +kernel

theorem in_3_2_0_2 : run1 [3, 2, 0, 2] = some (true, 287) := by
  decide +kernel

theorem in_3_2_0_3 : run1 [3, 2, 0, 3] = some (true, 287) := by
  decide +kernel

theorem in_3_2_1_0 : run1 [3, 2, 1, 0] = some (true, 287) := by
  decide +kernel

theorem in_3_2_1_1 : run1 [3, 2, 1, 1] = some (true, 287) := by
  decide +kernel

theorem in_3_2_1_2 : run1 [3, 2, 1, 2] = some (true, 287) := by
  decide +kernel

theorem in_3_2_1_3 : run1 [3, 2, 1, 3] = some (true, 287) := by
  decide +kernel

theorem in_3_2_2_0 : run1 [3, 2, 2, 0] = some (true, 287) := by
  decide +kernel

theorem in_3_2_2_1 : run1 [3, 2, 2, 1] = some (true, 287) := by
  decide +kernel

theorem in_3_2_2_2 : run1 [3, 2, 2, 2] = some (true, 287) := by
  decide +kernel

theorem in_3_2_2_3 : run1 [3, 2, 2, 3] = some (true, 287) := by
  decide +kernel

theorem in_3_2_3_0 : run1 [3, 2, 3, 0] = some (true, 287) := by
  decide +kernel

theorem in_3_2_3_1 : run1 [3, 2, 3, 1] = some (true, 287) := by
  decide +kernel

theorem in_3_2_3_2 : run1 [3, 2, 3, 2] = some (true, 287) := by
  decide +kernel

theorem in_3_2_3_3 : run1 [3, 2, 3, 3] = some (true, 287) := by
  decide +kernel

theorem in_3_3_0_0 : run1 [3, 3, 0, 0] = some (true, 287) := by
  decide +kernel

theorem in_3_3_0_1 : run1 [3, 3, 0, 1] = some (true, 287) := by
  decide +kernel

theorem in_3_3_0_2 : run1 [3, 3, 0, 2] = some (true, 287) := by
  decide +kernel

theorem in_3_3_0_3 : run1 [3, 3, 0, 3] = some (true, 287) := by
  decide +kernel

theorem in_3_3_1_0 : run1 [3, 3, 1, 0] = some (true, 287) := by
  decide +kernel

theorem in_3_3_1_1 : run1 [3, 3, 1, 1] = some (true, 287) := by
  decide +kernel

theorem in_3_3_1_2 : run1 [3, 3, 1, 2] = some (true, 287) := by
  decide +kernel

theorem in_3_3_1_3 : run1 [3, 3, 1, 3] = some (true, 287) := by
  decide +kernel

theorem in_3_3_2_0 : run1 [3, 3, 2, 0] = some (true, 287) := by
  decide +kernel

theorem in_3_3_2_1 : run1 [3, 3, 2, 1] = some (true, 287) := by
  decide +kernel

theorem in_3_3_2_2 : run1 [3, 3, 2, 2] = some (true, 287) := by
  decide +kernel

theorem in_3_3_2_3 : run1 [3, 3, 2, 3] = some (true, 287) := by
  decide +kernel

theorem in_3_3_3_0 : run1 [3, 3, 3, 0] = some (true, 287) := by
  decide +kernel

theorem in_3_3_3_1 : run1 [3, 3, 3, 1] = some (true, 287) := by
  decide +kernel

theorem in_3_3_3_2 : run1 [3, 3, 3, 2] = some (true, 287) := by
  decide +kernel

theorem in_3_3_3_3 : run1 [3, 3, 3, 3] = some (true, 287) := by
  decide +kernel

-- A long list of inputs, and a long conjunction of facts, go deeper than the default limit.
set_option maxRecDepth 100000 in
theorem inputs_eq : allInputs task.space = [[0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 2], [0, 0, 0, 3], [0, 0, 1, 0], [0, 0, 1, 1], [0, 0, 1, 2], [0, 0, 1, 3], [0, 0, 2, 0], [0, 0, 2, 1], [0, 0, 2, 2], [0, 0, 2, 3], [0, 0, 3, 0], [0, 0, 3, 1], [0, 0, 3, 2], [0, 0, 3, 3], [0, 1, 0, 0], [0, 1, 0, 1], [0, 1, 0, 2], [0, 1, 0, 3], [0, 1, 1, 0], [0, 1, 1, 1], [0, 1, 1, 2], [0, 1, 1, 3], [0, 1, 2, 0], [0, 1, 2, 1], [0, 1, 2, 2], [0, 1, 2, 3], [0, 1, 3, 0], [0, 1, 3, 1], [0, 1, 3, 2], [0, 1, 3, 3], [0, 2, 0, 0], [0, 2, 0, 1], [0, 2, 0, 2], [0, 2, 0, 3], [0, 2, 1, 0], [0, 2, 1, 1], [0, 2, 1, 2], [0, 2, 1, 3], [0, 2, 2, 0], [0, 2, 2, 1], [0, 2, 2, 2], [0, 2, 2, 3], [0, 2, 3, 0], [0, 2, 3, 1], [0, 2, 3, 2], [0, 2, 3, 3], [0, 3, 0, 0], [0, 3, 0, 1], [0, 3, 0, 2], [0, 3, 0, 3], [0, 3, 1, 0], [0, 3, 1, 1], [0, 3, 1, 2], [0, 3, 1, 3], [0, 3, 2, 0], [0, 3, 2, 1], [0, 3, 2, 2], [0, 3, 2, 3], [0, 3, 3, 0], [0, 3, 3, 1], [0, 3, 3, 2], [0, 3, 3, 3], [1, 0, 0, 0], [1, 0, 0, 1], [1, 0, 0, 2], [1, 0, 0, 3], [1, 0, 1, 0], [1, 0, 1, 1], [1, 0, 1, 2], [1, 0, 1, 3], [1, 0, 2, 0], [1, 0, 2, 1], [1, 0, 2, 2], [1, 0, 2, 3], [1, 0, 3, 0], [1, 0, 3, 1], [1, 0, 3, 2], [1, 0, 3, 3], [1, 1, 0, 0], [1, 1, 0, 1], [1, 1, 0, 2], [1, 1, 0, 3], [1, 1, 1, 0], [1, 1, 1, 1], [1, 1, 1, 2], [1, 1, 1, 3], [1, 1, 2, 0], [1, 1, 2, 1], [1, 1, 2, 2], [1, 1, 2, 3], [1, 1, 3, 0], [1, 1, 3, 1], [1, 1, 3, 2], [1, 1, 3, 3], [1, 2, 0, 0], [1, 2, 0, 1], [1, 2, 0, 2], [1, 2, 0, 3], [1, 2, 1, 0], [1, 2, 1, 1], [1, 2, 1, 2], [1, 2, 1, 3], [1, 2, 2, 0], [1, 2, 2, 1], [1, 2, 2, 2], [1, 2, 2, 3], [1, 2, 3, 0], [1, 2, 3, 1], [1, 2, 3, 2], [1, 2, 3, 3], [1, 3, 0, 0], [1, 3, 0, 1], [1, 3, 0, 2], [1, 3, 0, 3], [1, 3, 1, 0], [1, 3, 1, 1], [1, 3, 1, 2], [1, 3, 1, 3], [1, 3, 2, 0], [1, 3, 2, 1], [1, 3, 2, 2], [1, 3, 2, 3], [1, 3, 3, 0], [1, 3, 3, 1], [1, 3, 3, 2], [1, 3, 3, 3], [2, 0, 0, 0], [2, 0, 0, 1], [2, 0, 0, 2], [2, 0, 0, 3], [2, 0, 1, 0], [2, 0, 1, 1], [2, 0, 1, 2], [2, 0, 1, 3], [2, 0, 2, 0], [2, 0, 2, 1], [2, 0, 2, 2], [2, 0, 2, 3], [2, 0, 3, 0], [2, 0, 3, 1], [2, 0, 3, 2], [2, 0, 3, 3], [2, 1, 0, 0], [2, 1, 0, 1], [2, 1, 0, 2], [2, 1, 0, 3], [2, 1, 1, 0], [2, 1, 1, 1], [2, 1, 1, 2], [2, 1, 1, 3], [2, 1, 2, 0], [2, 1, 2, 1], [2, 1, 2, 2], [2, 1, 2, 3], [2, 1, 3, 0], [2, 1, 3, 1], [2, 1, 3, 2], [2, 1, 3, 3], [2, 2, 0, 0], [2, 2, 0, 1], [2, 2, 0, 2], [2, 2, 0, 3], [2, 2, 1, 0], [2, 2, 1, 1], [2, 2, 1, 2], [2, 2, 1, 3], [2, 2, 2, 0], [2, 2, 2, 1], [2, 2, 2, 2], [2, 2, 2, 3], [2, 2, 3, 0], [2, 2, 3, 1], [2, 2, 3, 2], [2, 2, 3, 3], [2, 3, 0, 0], [2, 3, 0, 1], [2, 3, 0, 2], [2, 3, 0, 3], [2, 3, 1, 0], [2, 3, 1, 1], [2, 3, 1, 2], [2, 3, 1, 3], [2, 3, 2, 0], [2, 3, 2, 1], [2, 3, 2, 2], [2, 3, 2, 3], [2, 3, 3, 0], [2, 3, 3, 1], [2, 3, 3, 2], [2, 3, 3, 3], [3, 0, 0, 0], [3, 0, 0, 1], [3, 0, 0, 2], [3, 0, 0, 3], [3, 0, 1, 0], [3, 0, 1, 1], [3, 0, 1, 2], [3, 0, 1, 3], [3, 0, 2, 0], [3, 0, 2, 1], [3, 0, 2, 2], [3, 0, 2, 3], [3, 0, 3, 0], [3, 0, 3, 1], [3, 0, 3, 2], [3, 0, 3, 3], [3, 1, 0, 0], [3, 1, 0, 1], [3, 1, 0, 2], [3, 1, 0, 3], [3, 1, 1, 0], [3, 1, 1, 1], [3, 1, 1, 2], [3, 1, 1, 3], [3, 1, 2, 0], [3, 1, 2, 1], [3, 1, 2, 2], [3, 1, 2, 3], [3, 1, 3, 0], [3, 1, 3, 1], [3, 1, 3, 2], [3, 1, 3, 3], [3, 2, 0, 0], [3, 2, 0, 1], [3, 2, 0, 2], [3, 2, 0, 3], [3, 2, 1, 0], [3, 2, 1, 1], [3, 2, 1, 2], [3, 2, 1, 3], [3, 2, 2, 0], [3, 2, 2, 1], [3, 2, 2, 2], [3, 2, 2, 3], [3, 2, 3, 0], [3, 2, 3, 1], [3, 2, 3, 2], [3, 2, 3, 3], [3, 3, 0, 0], [3, 3, 0, 1], [3, 3, 0, 2], [3, 3, 0, 3], [3, 3, 1, 0], [3, 3, 1, 1], [3, 3, 1, 2], [3, 3, 1, 3], [3, 3, 2, 0], [3, 3, 2, 1], [3, 3, 2, 2], [3, 3, 2, 3], [3, 3, 3, 0], [3, 3, 3, 1], [3, 3, 3, 2], [3, 3, 3, 3]] := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem all_inputs : Each (fun x => run1 x = some (true, 287)) (allInputs task.space) := by
  rw [inputs_eq]
  exact ⟨in_0_0_0_0, in_0_0_0_1, in_0_0_0_2, in_0_0_0_3, in_0_0_1_0, in_0_0_1_1, in_0_0_1_2, in_0_0_1_3, in_0_0_2_0, in_0_0_2_1, in_0_0_2_2, in_0_0_2_3, in_0_0_3_0, in_0_0_3_1, in_0_0_3_2, in_0_0_3_3, in_0_1_0_0, in_0_1_0_1, in_0_1_0_2, in_0_1_0_3, in_0_1_1_0, in_0_1_1_1, in_0_1_1_2, in_0_1_1_3, in_0_1_2_0, in_0_1_2_1, in_0_1_2_2, in_0_1_2_3, in_0_1_3_0, in_0_1_3_1, in_0_1_3_2, in_0_1_3_3, in_0_2_0_0, in_0_2_0_1, in_0_2_0_2, in_0_2_0_3, in_0_2_1_0, in_0_2_1_1, in_0_2_1_2, in_0_2_1_3, in_0_2_2_0, in_0_2_2_1, in_0_2_2_2, in_0_2_2_3, in_0_2_3_0, in_0_2_3_1, in_0_2_3_2, in_0_2_3_3, in_0_3_0_0, in_0_3_0_1, in_0_3_0_2, in_0_3_0_3, in_0_3_1_0, in_0_3_1_1, in_0_3_1_2, in_0_3_1_3, in_0_3_2_0, in_0_3_2_1, in_0_3_2_2, in_0_3_2_3, in_0_3_3_0, in_0_3_3_1, in_0_3_3_2, in_0_3_3_3, in_1_0_0_0, in_1_0_0_1, in_1_0_0_2, in_1_0_0_3, in_1_0_1_0, in_1_0_1_1, in_1_0_1_2, in_1_0_1_3, in_1_0_2_0, in_1_0_2_1, in_1_0_2_2, in_1_0_2_3, in_1_0_3_0, in_1_0_3_1, in_1_0_3_2, in_1_0_3_3, in_1_1_0_0, in_1_1_0_1, in_1_1_0_2, in_1_1_0_3, in_1_1_1_0, in_1_1_1_1, in_1_1_1_2, in_1_1_1_3, in_1_1_2_0, in_1_1_2_1, in_1_1_2_2, in_1_1_2_3, in_1_1_3_0, in_1_1_3_1, in_1_1_3_2, in_1_1_3_3, in_1_2_0_0, in_1_2_0_1, in_1_2_0_2, in_1_2_0_3, in_1_2_1_0, in_1_2_1_1, in_1_2_1_2, in_1_2_1_3, in_1_2_2_0, in_1_2_2_1, in_1_2_2_2, in_1_2_2_3, in_1_2_3_0, in_1_2_3_1, in_1_2_3_2, in_1_2_3_3, in_1_3_0_0, in_1_3_0_1, in_1_3_0_2, in_1_3_0_3, in_1_3_1_0, in_1_3_1_1, in_1_3_1_2, in_1_3_1_3, in_1_3_2_0, in_1_3_2_1, in_1_3_2_2, in_1_3_2_3, in_1_3_3_0, in_1_3_3_1, in_1_3_3_2, in_1_3_3_3, in_2_0_0_0, in_2_0_0_1, in_2_0_0_2, in_2_0_0_3, in_2_0_1_0, in_2_0_1_1, in_2_0_1_2, in_2_0_1_3, in_2_0_2_0, in_2_0_2_1, in_2_0_2_2, in_2_0_2_3, in_2_0_3_0, in_2_0_3_1, in_2_0_3_2, in_2_0_3_3, in_2_1_0_0, in_2_1_0_1, in_2_1_0_2, in_2_1_0_3, in_2_1_1_0, in_2_1_1_1, in_2_1_1_2, in_2_1_1_3, in_2_1_2_0, in_2_1_2_1, in_2_1_2_2, in_2_1_2_3, in_2_1_3_0, in_2_1_3_1, in_2_1_3_2, in_2_1_3_3, in_2_2_0_0, in_2_2_0_1, in_2_2_0_2, in_2_2_0_3, in_2_2_1_0, in_2_2_1_1, in_2_2_1_2, in_2_2_1_3, in_2_2_2_0, in_2_2_2_1, in_2_2_2_2, in_2_2_2_3, in_2_2_3_0, in_2_2_3_1, in_2_2_3_2, in_2_2_3_3, in_2_3_0_0, in_2_3_0_1, in_2_3_0_2, in_2_3_0_3, in_2_3_1_0, in_2_3_1_1, in_2_3_1_2, in_2_3_1_3, in_2_3_2_0, in_2_3_2_1, in_2_3_2_2, in_2_3_2_3, in_2_3_3_0, in_2_3_3_1, in_2_3_3_2, in_2_3_3_3, in_3_0_0_0, in_3_0_0_1, in_3_0_0_2, in_3_0_0_3, in_3_0_1_0, in_3_0_1_1, in_3_0_1_2, in_3_0_1_3, in_3_0_2_0, in_3_0_2_1, in_3_0_2_2, in_3_0_2_3, in_3_0_3_0, in_3_0_3_1, in_3_0_3_2, in_3_0_3_3, in_3_1_0_0, in_3_1_0_1, in_3_1_0_2, in_3_1_0_3, in_3_1_1_0, in_3_1_1_1, in_3_1_1_2, in_3_1_1_3, in_3_1_2_0, in_3_1_2_1, in_3_1_2_2, in_3_1_2_3, in_3_1_3_0, in_3_1_3_1, in_3_1_3_2, in_3_1_3_3, in_3_2_0_0, in_3_2_0_1, in_3_2_0_2, in_3_2_0_3, in_3_2_1_0, in_3_2_1_1, in_3_2_1_2, in_3_2_1_3, in_3_2_2_0, in_3_2_2_1, in_3_2_2_2, in_3_2_2_3, in_3_2_3_0, in_3_2_3_1, in_3_2_3_2, in_3_2_3_3, in_3_3_0_0, in_3_3_0_1, in_3_3_0_2, in_3_3_0_3, in_3_3_1_0, in_3_3_1_1, in_3_3_1_2, in_3_3_1_3, in_3_3_2_0, in_3_3_2_1, in_3_3_2_2, in_3_3_2_3, in_3_3_3_0, in_3_3_3_1, in_3_3_3_2, in_3_3_3_3, trivial⟩

set_option maxRecDepth 100000 in
/-- The kernel never runs the whole checker at once: the instance follows from the facts. Every
    step rewrites with an equation, so the terms the kernel compares are identical. -/
theorem D_instance : CostM.billed (D Interp.counting) ⟨weights, cert⟩ = some (256, 73472) := by
  obtain ⟨c', hrun, htot⟩ := countGSingles_run (g := graph) (task := task) ⟨weights, cert⟩ 287
    (fun _ => true) (allInputs task.space) [] all_inputs
  have hlen : (allInputs task.space).length = 256 := by rw [inputs_eq]; rfl
  have hcount : (allInputs task.space).countP (fun _ => true) = 256 := by
    rw [List.countP_true, hlen]
  have htot' : c'.total = 73472 := by
    rw [htot, hlen]
    simp [Cost.total]
  have hD : D Interp.counting = countGSingles Interp.counting graph task (allInputs task.space) := rfl
  rw [CostM.billed, CostM.exec, hD, hrun, hcount]
  simp only [Option.map_some, htot']

theorem performance : Target := by
  change claimedCount ≤ numCorrect graph weights task
  obtain ⟨cost, h⟩ := CostM.exec_of_billed D_instance
  exact D_sound weights cert 256 cost h

end BruteForceInstances.AttnMin4Tiny
