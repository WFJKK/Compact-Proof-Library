import Protected.N_max2_tiny_v8_s0_c64
import LinearMaxKColumnMax.Sound

/-!
# Instance: column maxima on the tiny max-of-2 network, under `Full64`'s plan

`tests/max2_tiny` of the pipeline, network `max2_tiny-v8-s0`: `k = 2` positions, `V = 8` tokens,
width `d = 4`. The protected module is the one the acceptance service generates for a claim of 64.

The plan is the one of the agent's `Full64` (open lane, pilot 2, round 4), term for term:
`pair a m` is `box m a a`, `rpair a m` is `refined [a, m]`, `exact a m` is `exact [a, m]`.
`Full64` certified the inputs `[6, 7]` and `[7, 6]` with the forward pass it ran to bound the
weights' lengths; under policy v4 the lengths are read for free, so `exact [6, 7]` certifies them.

The kernel evaluates the checker on the protected weights (`D_instance`): all 64 inputs certified,
for a bill of 581 (`LinearMaxKColumnMax.billPlan`): the columns 384, their summaries 64, and the
tests 133 (two diagonal tests at 1, sixteen boxes at 2, nine refined tests at 6, three exact tests
at 15).
-/

namespace LinearMaxKColumnMaxInstances.Max2TinyFull64

open CompactCheck LinearMaxKColumnMax Protected.N_max2_tiny_v8_s0_c64

/-- `Full64`'s plan. -/
def plan : List Term :=
  [.diag 0, .diag 3,
    .box 1 0 0 true, .box 2 1 1 true, .box 4 0 0 true, .box 5 0 0 true, .box 6 0 0 true,
    .box 7 0 0 true,
    .box 4 1 1 false, .box 6 1 1 false, .box 7 1 1 false, .box 4 2 2 false, .box 5 2 2 false,
    .box 7 2 2 false, .box 4 3 3 false, .box 6 3 3 false, .box 6 4 4 false, .box 7 4 4 false,
    .refined [0, 2], .refined [0, 3], .refined [1, 3], .refined [1, 5], .refined [2, 3],
    .refined [3, 5], .refined [3, 7], .refined [5, 6], .refined [5, 7],
    .exact [2, 6], .exact [4, 5], .exact [6, 7]]

/-- The checker of the plan on this network. -/
def D : Checker := fun I => check I plan graph task

theorem D_sound : ∀ (w : Weights ℚ) (c : Cert) (n : Nat) (cost : Cost),
    CostM.exec (D Interp.counting) ⟨w, c⟩ = some (n, cost) → n ≤ numCorrect graph w task :=
  fun w c n cost h => check_sound (g := graph) (by decide) plan w c n cost h

theorem D_instance : CostM.billed (D Interp.counting) ⟨weights, cert⟩ = some (64, 581) := by
  decide +kernel

theorem performance : Target := by
  change claimedCount ≤ numCorrect graph weights task
  obtain ⟨cost, h⟩ := CostM.exec_of_billed D_instance
  exact D_sound weights cert 64 cost h

end LinearMaxKColumnMaxInstances.Max2TinyFull64
