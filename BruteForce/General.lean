import BruteForce.Checker
import CompactCheck.CountedGeneralSound

/-!
# Brute force on general networks (attention)

The linear single-input rule (`I.single`) has no price for softmax, so on an attention network it
fails. CompactCheck's general single rule `I.gsingle` runs the general checker's exact forward pass
on one input, `exp` and softmax enclosed in rational bounds, and charges what `cost-v3` charges a
`single` leaf of such a network (`CountedGeneral.lean`). Brute force is the same program with it:
every input of the task's space, counting the passes.

* `checkGeneral_sound`: the count is at most `numCorrect`, for every graph, task, weights and
  certificate (`CostM.gsingle_correct`).
* `countGSingles_run`: given each call's verdict and charge as a separate fact, the run of the
  checker. An instance proves one fact per input (`decide +kernel` each) and puts them together
  with this lemma: one `decide` over all forward passes of an attention network does not fit in
  the kernel's memory (CompactCheck's `docs/COUNTED.md`, "Split instances").

On the one-head attention networks of the pipeline the charge of a forward pass is the same for
every input: with `n` positions, `V` tokens, width `d` and head size `h`,

    2 n d h + 2 d h + 4 n h + 2 n d + 2 n + d + V d + V - 1

(`gopCost` on the graph's 26 operations, plus the final comparison); 191 on the tiny max-of-2
network (`n = 2`, `V = 8`, `d = h = 4`) and 287 on the tiny max-of-4 one (`n = V = d = h = 4`).
The instances state the charge the kernel computes; the formula is checked there, not proved.
-/

namespace BruteForce

open CompactCheck Common

section Checker

variable (I : Interp)

/-- The general single-input rule on each input of `xs`, counting the inputs that pass. -/
def countGSingles (g : Graph) (task : Task) : List Input → I.M I.N
  | [] => pure I.nzero
  | x :: xs => do
    let ok ← I.gsingle g task x
    let n ← countGSingles g task xs
    pure (I.nadd (I.countB ok) n)

/-- Brute force on a general network: the general single-input rule on every input. -/
def checkGeneral (g : Graph) (task : Task) : I.M I.N :=
  countGSingles I g task (allInputs task.space)

end Checker

variable {env : Env} {g : Graph} {task : Task}

open Classical in
/-- The count never exceeds the number of inputs the network answers correctly. -/
theorem countGSingles_le (xs : List Input) (c : Cost) (n : ℕ) (c' : Cost)
    (h : (countGSingles Interp.counting g task xs).run env c = some (n, c')) :
    n ≤ xs.countP fun x => decide (Correct g env.weights task x) := by
  induction xs generalizing c n c' with
  | nil =>
    simp only [countGSingles, CostM.run_pure, Option.some.injEq, Prod.mk.injEq] at h
    omega
  | cons x xs ih =>
    obtain ⟨ok, c1, h1, h2⟩ := Runs.bind_some h
    obtain ⟨m, c2, h3, h4⟩ := Runs.bind_some h2
    simp only [CostM.run_pure, Option.some.injEq, Prod.mk.injEq] at h4
    have hm := ih c1 m c2 h3
    rw [List.countP_cons]
    cases ok with
    | false => simp only [Bool.cond_false, Nat.add_eq] at h4; omega
    | true =>
      have hc : Correct g env.weights task x := CostM.gsingle_correct h1
      simp only [Bool.cond_true, Nat.add_eq] at h4
      simp only [hc, decide_true, ite_true]
      omega

/-- **Soundness.** For every graph, task, weights and certificate, brute force with the general
    single rule certifies at most the inputs the network answers correctly. -/
theorem checkGeneral_sound (w : Weights ℚ) (c : Cert) (n : ℕ) (cost : Cost)
    (h : CostM.exec (checkGeneral Interp.counting g task) ⟨w, c⟩ = some (n, cost)) :
    n ≤ numCorrect g w task := by
  unfold numCorrect
  exact countGSingles_le (env := ⟨w, c⟩) _ [] n cost h

/-- The general single rule's verdict and charge on input `x`, for the weights `w`. -/
abbrev gsingleOn (w : Weights ℚ) (g : Graph) (task : Task) (x : Input) : Option (Bool × ℕ) :=
  (dweights w).bind fun dw => gsingleRun g dw task x

/-- `P` holds of every element, as a nested conjunction: a proof is one anonymous constructor of
    separately proved facts. -/
def Each {α : Type} (P : α → Prop) : List α → Prop
  | [] => True
  | x :: xs => P x ∧ Each P xs

/-- **The run, from one fact per call.** If the general single rule answers `b x` on each input
    `x` of `xs` at the charge `K`, the checker counts the inputs with `b x` and is charged `K` per
    input. -/
theorem countGSingles_run (env : Env) (K : ℕ) (b : Input → Bool) :
    ∀ (xs : List Input) (c : Cost),
      Each (fun x => gsingleOn env.weights g task x = some (b x, K)) xs →
      ∃ c', (countGSingles Interp.counting g task xs).run env c = some (xs.countP b, c') ∧
        c'.total = c.total + K * xs.length
  | [], c, _ => ⟨c, by simp [countGSingles, CostM.run_pure], by simp⟩
  | x :: xs, c, h => by
    obtain ⟨hx, hxs⟩ := h
    obtain ⟨c', hrun, htot⟩ := countGSingles_run env K b xs (c.add "single" K) hxs
    refine ⟨c', ?_, ?_⟩
    · simp only [countGSingles, Interp.counting_bind, Interp.counting_pure, CostM.run_bind,
        CostM.gsingle_run_of hx, hrun, CostM.run_pure, List.countP_cons]
      cases b x <;> simp <;> omega
    · rw [htot, CompactCheck.Cost.total_add, List.length_cons, Nat.mul_add, Nat.mul_one]
      omega

end BruteForce
