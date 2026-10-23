import Symmetry.Sorted
import LinearMaxK.Groups

/-!
# Symmetry: one forward pass per class of reorderings

For a network whose input is summed over its positions before anything else (`symmetricNet`), and
a task whose label does not depend on the order of the tokens (`labelSymmetric`), an input and its
reorderings are answered alike (`singleOk_perm`). So the checker runs the single-input rule on the
sorted inputs only, and counts each that passes with the number of its reorderings, `mult V k x`.

* `check_sound`: for every such network and task, all weights and certificates, the count is at
  most `numCorrect`.
* `check_billed`: when a forward pass can be billed, at `s` operations, the count is the number of
  inputs the single-input rule passes, as for brute force, and the bill is `s` per sorted input:
  `(V + k - 1).choose k` forward passes instead of `V^k`.
-/

namespace Symmetry

open CompactCheck Common

section Checker

variable (I : Interp)

/-- The single-input rule on each sorted input of `xs`, counting each that passes with the number of
    its reorderings. -/
def countSorted (g : Graph) (task : Task) (V k : ℕ) : List Input → I.M I.N
  | [] => pure I.nzero
  | x :: xs => do
    let ok ← I.single g task x
    let n ← countSorted g task V k xs
    pure (I.nadd (I.nscale (mult V k x) ok) n)

/-- Symmetry: the single-input rule on every sorted input of the task's space, `k` positions of
    `V` tokens. -/
def check (g : Graph) (task : Task) : I.M I.N :=
  countSorted I g task (task.space.headD 0) task.space.length
    (sortedFrom (task.space.headD 0) task.space.length 0)

end Checker

variable {env : Env} {g : Graph} {task : Task}

/-- What a run computes, whenever it succeeds: the count of the sorted inputs that pass, each with
    its number of reorderings. -/
theorem countSorted_value {V k : ℕ} : ∀ (xs : List Input) {c c' : Cost} {n : ℕ},
    (countSorted Interp.counting g task V k xs).run env c = some (n, c') →
      n = (xs.map fun x => cond (singleOk g env.weights task x) (mult V k x) 0).sum
  | [], c, c', n, h => by
    simp only [countSorted, CostM.run_pure, Option.some.injEq, Prod.mk.injEq] at h
    simp [← h.1]
  | x :: xs, c, c', n, h => by
    obtain ⟨ok, c1, h1, h2⟩ := Runs.bind_some h
    obtain ⟨m, c2, h3, h4⟩ := Runs.bind_some h2
    simp only [CostM.run_pure, Option.some.injEq, Prod.mk.injEq] at h4
    obtain ⟨sc, hsc⟩ := single_some h1
    have hok := ((runs_single (task := task) (x := x) hsc).det h1).1
    rw [← h4.1, countSorted_value xs h3, hok]
    simp

/-- With a forward pass billed at `s`, the checker costs `s` per sorted input. -/
theorem runs_countSorted {s : ℕ} (hs : singleCost g env.weights = some s) (V k : ℕ) :
    ∀ xs : List Input, Runs (countSorted Interp.counting g task V k xs) env
      ((xs.map fun x => cond (singleOk g env.weights task x) (mult V k x) 0).sum) (xs.length * s)
  | [] => by simpa [countSorted] using Runs.pure (env := env) (0 : ℕ)
  | x :: xs => by
    refine Runs.bind' (runs_single hs)
      (Runs.bind' (runs_countSorted hs V k xs) (Runs.pure _) rfl rfl) ?_ ?_
    · simp only [Interp.counting, List.map_cons, List.sum_cons]
      cases singleOk g env.weights task x <;> simp
    · simp only [List.length_cons]; ring

/-! ## Classes of reorderings -/

/-- Two sorted inputs that are reorderings of one input are equal. -/
theorem sorted_classes (V k : ℕ) :
    (sortedFrom V k 0).Pairwise fun a b => ∀ y : Input, y.isPerm a = true → y.isPerm b = false := by
  refine (nodup_sortedFrom V k 0).imp_of_mem fun {a b} ha hb hab y hya => ?_
  rw [Bool.eq_false_iff]
  intro hyb
  rw [List.isPerm_iff] at hya hyb
  exact hab (List.Perm.eq_of_pairwise (fun a b _ _ h1 h2 => Nat.le_antisymm h1 h2)
    (mem_sortedFrom.mp ha).2.1 (mem_sortedFrom.mp hb).2.1 (hya.symm.trans hyb))

/-- Every input of `k` tokens in `[0, V)` is a reordering of a sorted one. -/
theorem exists_sorted {V k : ℕ} {y : Input} (hy : y ∈ allInputs (List.replicate k V)) :
    ∃ x ∈ sortedFrom V k 0, y.isPerm x = true := by
  obtain ⟨hlen, hyV⟩ := (LinearMaxK.mem_allInputs_replicate (k := k) (V := V)).mp hy
  refine ⟨y.mergeSort (fun a b => decide (a ≤ b)), mem_sortedFrom.mpr ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [List.length_mergeSort, hlen]
  · simpa using List.pairwise_mergeSort (le := fun a b => decide (a ≤ b))
      (fun a b c hab hbc => by simp at *; omega) (fun a b => by simp; omega) y
  · intro t ht
    exact ⟨Nat.zero_le t, hyV t ((List.mergeSort_perm y _).mem_iff.mp ht)⟩
  · rw [List.isPerm_iff]; exact (List.mergeSort_perm y _).symm

/-- Over classes that share no element and cover the inputs where `P` holds, the counts of `P` add
    up to the count of `P`. -/
theorem sum_countP_eq_of_pairwise {α β : Type} (L : List α) (Q : β → α → Bool) :
    ∀ (S : List β) (P : α → Bool), S.Pairwise (fun a b => ∀ y ∈ L, Q a y = true → Q b y = false) →
      (∀ y ∈ L, P y = true → ∃ s ∈ S, Q s y = true) →
      (S.map fun s => L.countP fun y => Q s y && P y).sum = L.countP P
  | [], P, _, hcov => by
    simp only [List.map_nil, List.sum_nil]
    refine (List.countP_eq_zero.mpr fun y hy hP => ?_).symm
    obtain ⟨s, hs, -⟩ := hcov y hy hP
    exact absurd hs List.not_mem_nil
  | s :: S, P, h, hcov => by
    obtain ⟨hs, hS⟩ := List.pairwise_cons.mp h
    have ih := sum_countP_eq_of_pairwise L Q S (fun y => P y && !Q s y) hS (by
      intro y hy hP
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hP
      obtain ⟨s', hs', hq⟩ := hcov y hy hP.1
      rcases List.mem_cons.mp hs' with rfl | hs'
      · rw [hP.2] at hq; cases hq
      · exact ⟨s', hs', hq⟩)
    have hcongr : (S.map fun s' => L.countP fun y => Q s' y && P y) =
        (S.map fun s' => L.countP fun y => Q s' y && (P y && !Q s y)) := by
      refine List.map_congr_left fun s' hs' => List.countP_congr fun y hy => ?_
      cases hq : Q s' y
      · simp
      · have : Q s y = false := by
          cases hqs : Q s y
          · rfl
          · rw [hs s' hs' y hy hqs] at hq; cases hq
        simp [this]
    have hsplit := countP_split L P (Q s)
    have hcomm : L.countP (fun y => Q s y && P y) = L.countP (fun y => P y && Q s y) :=
      List.countP_congr fun y _ => by simp [Bool.and_comm]
    rw [List.map_cons, List.sum_cons, hcongr, ih]
    omega

section Space

variable {k V : ℕ} (hspace : task.space = List.replicate k V) (hk : 0 < k)
include hspace hk

theorem check_eq :
    check Interp.counting g task = countSorted Interp.counting g task V k (sortedFrom V k 0) := by
  have h1 : task.space.length = k := by rw [hspace, List.length_replicate]
  have h2 : task.space.headD 0 = V := by
    rw [hspace]; obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩; rfl
  simp only [check, h1, h2]

omit hspace hk in
/-- The reorderings of a sorted input that passes the single-input rule, counted with a property
    they all have. -/
theorem countP_class (w : Weights ℚ) {x : Input} (hx : x ∈ sortedFrom V k 0) (P : Input → Bool)
    (hP : ∀ y, y.isPerm x = true → singleOk g w task x = true → P y = true) :
    cond (singleOk g w task x) (mult V k x) 0 =
      (allInputs (List.replicate k V)).countP fun y =>
        y.isPerm x && (singleOk g w task x && P y) := by
  obtain ⟨hlen, -, hxV⟩ := mem_sortedFrom.mp hx
  cases hs : singleOk g w task x
  · simp
  · simp only [Bool.cond_true, Bool.true_and]
    rw [← countP_perm k x hlen fun t ht => (hxV t ht).2]
    refine List.countP_congr fun y _ => ?_
    constructor
    · intro hy; simp [hy, hP y hy hs]
    · intro hy; simp only [Bool.and_eq_true] at hy; exact hy.1

open Classical in
/-- **Soundness.** For a network whose input is summed over its positions and a task whose label
    does not depend on the order, whatever the weights, the count is at most the number of inputs
    the network answers correctly. -/
theorem check_sound (hsym : symmetricNet g = true) (hlab : task.labelSymmetric = true)
    (w : Weights ℚ) (c : Cert) (n : ℕ) (cost : Cost)
    (h : CostM.exec (check Interp.counting g task) ⟨w, c⟩ = some (n, cost)) :
    n ≤ numCorrect g w task := by
  rw [check_eq hspace hk] at h
  rw [countSorted_value (env := ⟨w, c⟩) _ h, numCorrect, hspace]
  have hle : ∀ x ∈ sortedFrom V k 0, cond (singleOk g w task x) (mult V k x) 0 ≤
      (allInputs (List.replicate k V)).countP fun y =>
        y.isPerm x && decide (Correct g w task y) := by
    intro x hx
    rw [countP_class w hx (fun y => decide (Correct g w task y))
      (fun y hy hs => decide_eq_true (singleOk_correct g w task y
        (singleOk_perm hsym hlab (List.isPerm_iff.mp hy).symm hs)))]
    refine List.countP_mono_left fun y _ hy => ?_
    simp only [Bool.and_eq_true] at hy ⊢
    exact ⟨hy.1, hy.2.2⟩
  refine le_trans (List.sum_le_sum hle) ?_
  exact sum_countP_le_of_pairwise _ (fun (x y : Input) => y.isPerm x) _ _
    ((sorted_classes V k).imp fun h y _ => h y)

/-- **Count and cost.** When a forward pass can be billed, at `s` operations, the count is the
    number of inputs the single-input rule passes, as for brute force, and the bill is `s` per
    sorted input, of which there are `(V + k - 1).choose k`. -/
theorem check_billed (hsym : symmetricNet g = true) (hlab : task.labelSymmetric = true)
    {w : Weights ℚ} {s : ℕ} (hs : singleCost g w = some s) (c : Cert) :
    CostM.billed (check Interp.counting g task) ⟨w, c⟩ =
      some ((allInputs task.space).countP (singleOk g w task), (V + k - 1).choose k * s) := by
  rw [check_eq hspace hk, (runs_countSorted (env := ⟨w, c⟩) (task := task) hs V k _).billed,
    length_sortedFrom, Nat.sub_zero, hspace]
  congr 2
  have hcl : ∀ x ∈ sortedFrom V k 0, cond (singleOk g w task x) (mult V k x) 0 =
      (allInputs (List.replicate k V)).countP fun y => y.isPerm x && singleOk g w task y := by
    intro x hx
    rw [countP_class w hx (fun _ => true) (fun _ _ _ => rfl)]
    refine List.countP_congr fun y _ => ?_
    constructor
    · intro hy
      simp only [Bool.and_eq_true] at hy
      exact by simp [hy.1, singleOk_perm hsym hlab (List.isPerm_iff.mp hy.1).symm hy.2.1]
    · intro hy
      simp only [Bool.and_eq_true] at hy
      exact by simp [hy.1, singleOk_perm hsym hlab (List.isPerm_iff.mp hy.1) hy.2]
  rw [List.map_congr_left hcl]
  exact sum_countP_eq_of_pairwise _ (fun (x y : Input) => y.isPerm x) _ _
    ((sorted_classes V k).imp fun h y _ => h y) fun y hy _ => exists_sorted hy

end Space

end Symmetry
