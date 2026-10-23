import Common.Basic

/-!
# Brute force

The proof every other is measured against: the single-input rule, one exact forward pass charged as
`cost-v3` charges it, on every input of the task's space, counting the inputs it answers
correctly. It uses nothing about the network, so it is written once, for every graph and every task.

* `check_sound`: the count is at most `numCorrect`, for every graph, task, weights and certificate.
* `check_billed`: when a forward pass can be billed (`singleCost g w = some s`), the count is the
  number of inputs the single-input rule passes, and the bill is `s` per input.
-/

namespace BruteForce

open CompactCheck Common

section Checker

variable (I : Interp)

/-- The single-input rule on each input of `xs`, counting the inputs that pass. -/
def countSingles (g : Graph) (task : Task) : List Input → I.M I.N
  | [] => pure I.nzero
  | x :: xs => do
    let ok ← I.single g task x
    let n ← countSingles g task xs
    pure (I.nadd (I.countB ok) n)

/-- Brute force: the single-input rule on every input of the task's space. -/
def check (g : Graph) (task : Task) : I.M I.N :=
  countSingles I g task (allInputs task.space)

end Checker

variable {env : Env} {g : Graph} {task : Task}

/-- With a forward pass billed at `s`, the single-input rule on the inputs `xs` counts those that
    pass and costs `s` for each. -/
theorem runs_countSingles {s : ℕ} (hs : singleCost g env.weights = some s) :
    ∀ xs : List Input, Runs (countSingles Interp.counting g task xs) env
      (xs.countP (singleOk g env.weights task)) (xs.length * s)
  | [] => by simpa [countSingles] using Runs.pure (env := env) (0 : ℕ)
  | x :: xs => by
    refine Runs.bind' (runs_single hs)
      (Runs.bind' (runs_countSingles hs xs) (Runs.pure _) rfl rfl) ?_ ?_
    · simp only [Interp.counting, List.countP_cons]
      cases singleOk g env.weights task x <;> simp
      omega
    · simp only [List.length_cons]; ring

open Classical in
/-- The count never exceeds the number of inputs the network answers correctly. -/
theorem countSingles_le (xs : List Input) (c : Cost) (n : ℕ) (c' : Cost)
    (h : (countSingles Interp.counting g task xs).run env c = some (n, c')) :
    n ≤ xs.countP fun x => decide (Correct g env.weights task x) := by
  induction xs generalizing c n c' with
  | nil =>
    simp only [countSingles, CostM.run_pure, Option.some.injEq, Prod.mk.injEq] at h
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
      have hc : Correct g env.weights task x :=
        singleOk_correct g env.weights task x (CostM.single_spec h1)
      simp only [Bool.cond_true, Nat.add_eq] at h4
      simp only [hc, decide_true, ite_true]
      omega

/-- **Soundness.** For every graph, task, weights and certificate, brute force certifies at most
    the inputs the network answers correctly. -/
theorem check_sound (w : Weights ℚ) (c : Cert) (n : ℕ) (cost : Cost)
    (h : CostM.exec (check Interp.counting g task) ⟨w, c⟩ = some (n, cost)) :
    n ≤ numCorrect g w task := by
  unfold numCorrect
  exact countSingles_le (env := ⟨w, c⟩) _ [] n cost h

/-- **Count and cost.** When a forward pass can be billed, at `s`, brute force counts the inputs
    the single-input rule passes, and its bill is `s` times the number of inputs. -/
theorem check_billed {w : Weights ℚ} {s : ℕ} (hs : singleCost g w = some s) (c : Cert) :
    CostM.billed (check Interp.counting g task) ⟨w, c⟩ =
      some ((allInputs task.space).countP (singleOk g w task), (allInputs task.space).length * s) :=
  (runs_countSingles (env := ⟨w, c⟩) hs _).billed

end BruteForce
