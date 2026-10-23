import Protected.N_attn_min2_tiny_v8d4_s1_c64
import BruteForce.General

/-!
# Instance: brute force on the attention network `attn_min2_tiny-v8d4-s1`

Written by `scripts/make_brute_general_instance.py`. `n = 2` positions, `V = 8` tokens, width
`d = 4`, head size `h = 4`: 64 inputs, each a forward pass of the general single rule charged
191. One fact per input, each decided by the kernel on its own; `D_instance` puts them together
(`BruteForce.countGSingles_run`): all 64 inputs certified, for a bill of 64 * 191 = 12,224.
-/

namespace BruteForceInstances.AttnMin2Tiny

open CompactCheck BruteForce Protected.N_attn_min2_tiny_v8d4_s1_c64

/-- Brute force with the general single rule on this network. -/
def D : Checker := fun I => checkGeneral I graph task

theorem D_sound : ∀ (w : Weights ℚ) (c : Cert) (n : Nat) (cost : Cost),
    CostM.exec (D Interp.counting) ⟨w, c⟩ = some (n, cost) → n ≤ numCorrect graph w task :=
  fun w c n cost h => checkGeneral_sound w c n cost h

/-- The general single rule's verdict and charge on input `x` of the protected weights. -/
abbrev run1 (x : Input) : Option (Bool × Nat) := gsingleOn weights graph task x

theorem in_0_0 : run1 [0, 0] = some (true, 191) := by
  decide +kernel

theorem in_0_1 : run1 [0, 1] = some (true, 191) := by
  decide +kernel

theorem in_0_2 : run1 [0, 2] = some (true, 191) := by
  decide +kernel

theorem in_0_3 : run1 [0, 3] = some (true, 191) := by
  decide +kernel

theorem in_0_4 : run1 [0, 4] = some (true, 191) := by
  decide +kernel

theorem in_0_5 : run1 [0, 5] = some (true, 191) := by
  decide +kernel

theorem in_0_6 : run1 [0, 6] = some (true, 191) := by
  decide +kernel

theorem in_0_7 : run1 [0, 7] = some (true, 191) := by
  decide +kernel

theorem in_1_0 : run1 [1, 0] = some (true, 191) := by
  decide +kernel

theorem in_1_1 : run1 [1, 1] = some (true, 191) := by
  decide +kernel

theorem in_1_2 : run1 [1, 2] = some (true, 191) := by
  decide +kernel

theorem in_1_3 : run1 [1, 3] = some (true, 191) := by
  decide +kernel

theorem in_1_4 : run1 [1, 4] = some (true, 191) := by
  decide +kernel

theorem in_1_5 : run1 [1, 5] = some (true, 191) := by
  decide +kernel

theorem in_1_6 : run1 [1, 6] = some (true, 191) := by
  decide +kernel

theorem in_1_7 : run1 [1, 7] = some (true, 191) := by
  decide +kernel

theorem in_2_0 : run1 [2, 0] = some (true, 191) := by
  decide +kernel

theorem in_2_1 : run1 [2, 1] = some (true, 191) := by
  decide +kernel

theorem in_2_2 : run1 [2, 2] = some (true, 191) := by
  decide +kernel

theorem in_2_3 : run1 [2, 3] = some (true, 191) := by
  decide +kernel

theorem in_2_4 : run1 [2, 4] = some (true, 191) := by
  decide +kernel

theorem in_2_5 : run1 [2, 5] = some (true, 191) := by
  decide +kernel

theorem in_2_6 : run1 [2, 6] = some (true, 191) := by
  decide +kernel

theorem in_2_7 : run1 [2, 7] = some (true, 191) := by
  decide +kernel

theorem in_3_0 : run1 [3, 0] = some (true, 191) := by
  decide +kernel

theorem in_3_1 : run1 [3, 1] = some (true, 191) := by
  decide +kernel

theorem in_3_2 : run1 [3, 2] = some (true, 191) := by
  decide +kernel

theorem in_3_3 : run1 [3, 3] = some (true, 191) := by
  decide +kernel

theorem in_3_4 : run1 [3, 4] = some (true, 191) := by
  decide +kernel

theorem in_3_5 : run1 [3, 5] = some (true, 191) := by
  decide +kernel

theorem in_3_6 : run1 [3, 6] = some (true, 191) := by
  decide +kernel

theorem in_3_7 : run1 [3, 7] = some (true, 191) := by
  decide +kernel

theorem in_4_0 : run1 [4, 0] = some (true, 191) := by
  decide +kernel

theorem in_4_1 : run1 [4, 1] = some (true, 191) := by
  decide +kernel

theorem in_4_2 : run1 [4, 2] = some (true, 191) := by
  decide +kernel

theorem in_4_3 : run1 [4, 3] = some (true, 191) := by
  decide +kernel

theorem in_4_4 : run1 [4, 4] = some (true, 191) := by
  decide +kernel

theorem in_4_5 : run1 [4, 5] = some (true, 191) := by
  decide +kernel

theorem in_4_6 : run1 [4, 6] = some (true, 191) := by
  decide +kernel

theorem in_4_7 : run1 [4, 7] = some (true, 191) := by
  decide +kernel

theorem in_5_0 : run1 [5, 0] = some (true, 191) := by
  decide +kernel

theorem in_5_1 : run1 [5, 1] = some (true, 191) := by
  decide +kernel

theorem in_5_2 : run1 [5, 2] = some (true, 191) := by
  decide +kernel

theorem in_5_3 : run1 [5, 3] = some (true, 191) := by
  decide +kernel

theorem in_5_4 : run1 [5, 4] = some (true, 191) := by
  decide +kernel

theorem in_5_5 : run1 [5, 5] = some (true, 191) := by
  decide +kernel

theorem in_5_6 : run1 [5, 6] = some (true, 191) := by
  decide +kernel

theorem in_5_7 : run1 [5, 7] = some (true, 191) := by
  decide +kernel

theorem in_6_0 : run1 [6, 0] = some (true, 191) := by
  decide +kernel

theorem in_6_1 : run1 [6, 1] = some (true, 191) := by
  decide +kernel

theorem in_6_2 : run1 [6, 2] = some (true, 191) := by
  decide +kernel

theorem in_6_3 : run1 [6, 3] = some (true, 191) := by
  decide +kernel

theorem in_6_4 : run1 [6, 4] = some (true, 191) := by
  decide +kernel

theorem in_6_5 : run1 [6, 5] = some (true, 191) := by
  decide +kernel

theorem in_6_6 : run1 [6, 6] = some (true, 191) := by
  decide +kernel

theorem in_6_7 : run1 [6, 7] = some (true, 191) := by
  decide +kernel

theorem in_7_0 : run1 [7, 0] = some (true, 191) := by
  decide +kernel

theorem in_7_1 : run1 [7, 1] = some (true, 191) := by
  decide +kernel

theorem in_7_2 : run1 [7, 2] = some (true, 191) := by
  decide +kernel

theorem in_7_3 : run1 [7, 3] = some (true, 191) := by
  decide +kernel

theorem in_7_4 : run1 [7, 4] = some (true, 191) := by
  decide +kernel

theorem in_7_5 : run1 [7, 5] = some (true, 191) := by
  decide +kernel

theorem in_7_6 : run1 [7, 6] = some (true, 191) := by
  decide +kernel

theorem in_7_7 : run1 [7, 7] = some (true, 191) := by
  decide +kernel

-- A long list of inputs, and a long conjunction of facts, go deeper than the default limit.
set_option maxRecDepth 100000 in
theorem inputs_eq : allInputs task.space = [[0, 0], [0, 1], [0, 2], [0, 3], [0, 4], [0, 5], [0, 6], [0, 7], [1, 0], [1, 1], [1, 2], [1, 3], [1, 4], [1, 5], [1, 6], [1, 7], [2, 0], [2, 1], [2, 2], [2, 3], [2, 4], [2, 5], [2, 6], [2, 7], [3, 0], [3, 1], [3, 2], [3, 3], [3, 4], [3, 5], [3, 6], [3, 7], [4, 0], [4, 1], [4, 2], [4, 3], [4, 4], [4, 5], [4, 6], [4, 7], [5, 0], [5, 1], [5, 2], [5, 3], [5, 4], [5, 5], [5, 6], [5, 7], [6, 0], [6, 1], [6, 2], [6, 3], [6, 4], [6, 5], [6, 6], [6, 7], [7, 0], [7, 1], [7, 2], [7, 3], [7, 4], [7, 5], [7, 6], [7, 7]] := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem all_inputs : Each (fun x => run1 x = some (true, 191)) (allInputs task.space) := by
  rw [inputs_eq]
  exact ⟨in_0_0, in_0_1, in_0_2, in_0_3, in_0_4, in_0_5, in_0_6, in_0_7, in_1_0, in_1_1, in_1_2, in_1_3, in_1_4, in_1_5, in_1_6, in_1_7, in_2_0, in_2_1, in_2_2, in_2_3, in_2_4, in_2_5, in_2_6, in_2_7, in_3_0, in_3_1, in_3_2, in_3_3, in_3_4, in_3_5, in_3_6, in_3_7, in_4_0, in_4_1, in_4_2, in_4_3, in_4_4, in_4_5, in_4_6, in_4_7, in_5_0, in_5_1, in_5_2, in_5_3, in_5_4, in_5_5, in_5_6, in_5_7, in_6_0, in_6_1, in_6_2, in_6_3, in_6_4, in_6_5, in_6_6, in_6_7, in_7_0, in_7_1, in_7_2, in_7_3, in_7_4, in_7_5, in_7_6, in_7_7, trivial⟩

set_option maxRecDepth 100000 in
/-- The kernel never runs the whole checker at once: the instance follows from the facts. Every
    step rewrites with an equation, so the terms the kernel compares are identical. -/
theorem D_instance : CostM.billed (D Interp.counting) ⟨weights, cert⟩ = some (64, 12224) := by
  obtain ⟨c', hrun, htot⟩ := countGSingles_run (g := graph) (task := task) ⟨weights, cert⟩ 191
    (fun _ => true) (allInputs task.space) [] all_inputs
  have hlen : (allInputs task.space).length = 64 := by rw [inputs_eq]; rfl
  have hcount : (allInputs task.space).countP (fun _ => true) = 64 := by
    rw [List.countP_true, hlen]
  have htot' : c'.total = 12224 := by
    rw [htot, hlen]
    simp [Cost.total]
  have hD : D Interp.counting = countGSingles Interp.counting graph task (allInputs task.space) := rfl
  rw [CostM.billed, CostM.exec, hD, hrun, hcount]
  simp only [Option.map_some, htot']

theorem performance : Target := by
  change claimedCount ≤ numCorrect graph weights task
  obtain ⟨cost, h⟩ := CostM.exec_of_billed D_instance
  exact D_sound weights cert 64 cost h

end BruteForceInstances.AttnMin2Tiny
