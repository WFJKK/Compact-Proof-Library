import PathBrute.Checker
import GrossCubic.Check

/-!
# What the checker of entry 8 computes, and what it costs

`runs_test`: one input's test, its value and its cost, `5 n` operations per other output.
`runs_check`: when `exp` accepts every score, the checker's run, with its count and its bill
`bill V n d h`, the tables and `5 n (V - 1)` operations per input. `sat_check`: what any run that
succeeds returns.
-/

namespace PathBrute

open CompactCheck Common AttnClasses GrossCubic Finset

variable {env : Env}

/-! ## One input -/

/-- The value of `test`. -/
def testV (V n : ℕ) (Dd : List (List (List Q))) (Od : List (List (List (List Q))))
    (X : List (List (List (Q × Q)))) (ℓ : ℕ) (x : Input) : Bool :=
  decide ((maxLV ((others V ℓ).map fun j => sumLV ((List.range n).map fun p =>
    kupV (((X.getD (x.getD (n - 1) 0) []).getD (x.getD p 0) []).getD p (⟨0⟩, ⟨0⟩))
      ⟨(((Dd.getD (x.getD (n - 1) 0) []).getD ℓ []).getD j ⟨0⟩).val +
        ((((Od.getD (x.getD p 0) []).getD p []).getD ℓ []).getD j ⟨0⟩).val⟩))).val < 0)

theorem runs_test (V n : ℕ) (Dd : List (List (List Q))) (Od : List (List (List (List Q))))
    (X : List (List (List (Q × Q)))) (ℓ : ℕ) (x : Input) :
    Runs (test Interp.counting V n Dd Od X ℓ x) env (testV V n Dd Od X ℓ x)
      ((others V ℓ).length * (n * 4 + (n - 1)) + ((others V ℓ).length - 1) + 1) := by
  unfold test
  simp only [Interp.counting_bind]
  refine Runs.bind' (runs_mapM (c := fun _ => n * 4 + (n - 1)) _ fun j _ =>
      Runs.bind' (runs_mapM (c := fun _ => 4) _ fun p _ =>
        Runs.bind' (runs_add cat _ _) (runs_kup _ _) rfl rfl) (runs_sumL _) rfl (by simp))
    (Runs.bind' (runs_maxL _) (runs_lt cat _ _) rfl rfl) rfl ?_
  simp
  omega

/-! ## Differences within rows -/

/-- The value of `diffs`. -/
def diffsV (r : List Q) : List (List Q) :=
  (List.range r.length).map fun l => r.map fun v => ⟨v.val - (r.getD l ⟨0⟩).val⟩

theorem runs_diffs (r : List Q) :
    Runs (diffs Interp.counting r) env (diffsV r) (r.length * r.length) := by
  unfold diffs diffsV
  refine (runs_mapM (c := fun _ => r.length) _ fun l _ => ?_).congr rfl (by simp)
  exact (runs_mapM (c := fun _ => 1) _ fun v _ => runs_sub cat _ _).congr rfl (by simp)

theorem diffsV_vec (k : ℕ) (f : ℕ → ℚ) : diffsV (vec k f) = mat k k fun l j => f j - f l := by
  rw [diffsV, length_vec]
  refine List.map_congr_left fun l hl => ?_
  rw [getD_vec (List.mem_range.mp hl)]
  simp [vec]

/-! ## The tables -/

/-- The differences of the direct path, `D[q, j] - D[q, l]` at `[q][l][j]`. -/
def DdTab (N : Net) : List (List (List Q)) :=
  (List.range N.V).map fun q => mat N.V N.V fun l j => N.D q j - N.D q l

/-- The differences of the paths through the head, `O[t, p, j] - O[t, p, l]` at `[t][p][l][j]`. -/
def OdTab (N : Net) : List (List (List (List Q))) :=
  (List.range N.V).map fun t => (List.range N.n).map fun p =>
    mat N.V N.V fun l j => (evT N t j + pvT N p j) - (evT N t l + pvT N p l)

/-- The count, from the bounds `X` on `exp` of the scores. -/
def countV (N : Net) (task : Task) (X : List (List (List (Q × Q)))) : ℕ :=
  ((allInputs task.space).map fun x =>
    testV N.V N.n (DdTab N) (OdTab N) X (task.label x) x).foldl
    (fun a b => Interp.counting.nadd a (Interp.counting.countB b)) Interp.counting.nzero

/-- The operations of the tables: queries and keys, scores, paths, their differences, and the
    bounds on `exp`. -/
def tableCost (V n d h : ℕ) : ℕ :=
  h * d + V * d + V * h * d + V * h * d + V * V * h + n * h * d + V * n * h + d * d * h +
    d * V * d + V * V * d + n * V * d + V * V * d + V * (n * V) + V * (n * (V * V)) +
    V * (V * V) + V * (V * (n * 4))

/-- The bill: the tables, and `5 n` operations per input and other output (`V ≥ 2`). -/
def bill (V n d h : ℕ) : ℕ :=
  tableCost V n d h + V ^ n * ((V - 1) * (n * 4 + (n - 1)) + (V - 1 - 1) + 1)

theorem length_allInputs : ∀ s : List ℕ, (allInputs s).length = s.prod
  | [] => rfl
  | v :: vs => by
    simp [allInputs, List.length_flatMap, length_allInputs vs]

theorem runs_Ot (N : Net) :
    Runs ((mat N.V N.V (evT N)).mapM fun r =>
        (mat N.n N.V (pvT N)).mapM (vadd Interp.counting r)) env
      ((List.range N.V).map fun t => (List.range N.n).map fun p =>
        vec N.V fun j => evT N t j + pvT N p j) (N.V * (N.n * N.V)) := by
  refine (runs_mapM (g := fun r => (mat N.n N.V (pvT N)).map fun s =>
      (List.zip r s).map fun pr => (⟨pr.1.val + pr.2.val⟩ : Q))
    (c := fun _ => N.n * N.V) _ fun r hr => ?_).congr ?_ (by simp [mat, Function.comp_def])
  · refine (runs_mapM (c := fun _ => N.V) _ fun s hs => ?_).congr rfl
      (by simp [mat, Function.comp_def])
    obtain ⟨t, -, rfl⟩ := List.mem_map.mp hr
    obtain ⟨p, -, rfl⟩ := List.mem_map.mp hs
    exact (runs_vadd N.V _ _).congr (by simp [vec, zip_map_map]) rfl
  · simp only [mat, List.map_map]
    refine List.map_congr_left fun t _ => ?_
    simp only [Function.comp_apply]
    refine List.map_congr_left fun p _ => ?_
    simp [vec, zip_map_map]

theorem runs_Od (N : Net) :
    Runs (((List.range N.V).map fun t => (List.range N.n).map fun p =>
        vec N.V fun j => evT N t j + pvT N p j).mapM fun rs =>
        rs.mapM (diffs Interp.counting)) env (OdTab N) (N.V * (N.n * (N.V * N.V))) := by
  refine (runs_mapM (g := fun rs => rs.map diffsV) (c := fun _ => N.n * (N.V * N.V)) _
    fun rs hrs => ?_).congr ?_ (by simp [Function.comp_def])
  · obtain ⟨t, -, rfl⟩ := List.mem_map.mp hrs
    refine (runs_mapM (c := fun _ => N.V * N.V) _ fun o ho => ?_).congr rfl
      (by simp [Function.comp_def])
    obtain ⟨p, -, rfl⟩ := List.mem_map.mp ho
    exact (runs_diffs _).congr rfl (by rw [length_vec])
  · simp only [OdTab, List.map_map]
    refine List.map_congr_left fun t _ => ?_
    simp only [Function.comp_apply, List.map_map]
    refine List.map_congr_left fun p _ => ?_
    simp only [Function.comp_apply]
    rw [diffsV_vec]

theorem runs_Dd (N : Net) :
    Runs ((mat N.V N.V N.D).mapM (diffs Interp.counting)) env (DdTab N) (N.V * (N.V * N.V)) := by
  refine (runs_mapM (g := diffsV) (c := fun _ => N.V * N.V) _ fun r hr => ?_).congr ?_
    (by simp [mat, Function.comp_def])
  · obtain ⟨q, -, rfl⟩ := List.mem_map.mp hr
    exact (runs_diffs _).congr rfl (by simp)
  · simp only [DdTab, mat, List.map_map]
    refine List.map_congr_left fun q _ => ?_
    simp only [Function.comp_apply]
    exact diffsV_vec N.V (N.D q)

/-! ## The whole run -/

/-- **The run.** On well-formed weights, when `exp` accepts every score and every label is an
    output, the checker returns `countV` and is billed `bill V n d h`. -/
theorem runs_check {N : Net} {g : Graph} (task : Task) {env : Env}
    (hw : N.WF env.weights) (hV : N.V = g.values) (hn : N.n = g.positions) (hn0 : 0 < N.n)
    (hsp : task.space = List.replicate N.n N.V)
    (hl : ∀ x ∈ allInputs task.space, task.label x < N.V)
    (hexp : ∀ q < N.V, ∀ t < N.V, ∀ p < N.n, (expInterval (N.SEf q t + N.SPf q p)).isSome) :
    Runs (check Interp.counting g task) env
      (countV N task (expTab N.V N.n fun q t p => N.SEf q t + N.SPf q p))
      (bill N.V N.n N.d N.h) := by
  have hQ : N.n - 1 < N.n := by omega
  refine Runs.of_eq (n :=
      N.h * N.d + (N.V * N.d + (N.V * N.h * N.d + (N.V * N.h * N.d + (N.V * N.V * N.h + (N.n *
        N.h * N.d + (N.V * N.n * N.h + (N.d * N.d * N.h + (N.d * N.V * N.d + (N.V * N.V * N.d +
        (N.n * N.V * N.d + (N.V * N.V * N.d + (N.V * (N.n * N.V) + (N.V * (N.n * (N.V * N.V)) +
        (N.V * (N.V * N.V) + (N.V * (N.V * (N.n * 4)) + (((allInputs task.space).map fun _ =>
        (N.V - 1) * (N.n * 4 + (N.n - 1)) + (N.V - 1 - 1) + 1).sum + (0)))))))))))))))))) ?run ?eq
  case run =>
    unfold check
    refine Runs.bind0 (runs_weightShape hw.hE) ?_
    refine Runs.bind0 (runs_weightShape hw.hP) ?_
    refine Runs.bind0 (runs_weightShape hw.hQ) ?_
    refine Runs.bind0 (runs_weightShape hw.hK) ?_
    refine Runs.bind0 (runs_weightShape hw.hV) ?_
    refine Runs.bind0 (runs_weightShape hw.hO) ?_
    refine Runs.bind0 (runs_weightShape hw.hU) ?_
    refine Runs.bind0 (runs_weightShape hw.hC) ?_
    refine Runs.bind0 (runs_weightSize hw.hE) ?_
    refine Runs.bind0 (runs_weightSize hw.hP) ?_
    refine Runs.bind0 (runs_weightSize hw.hQ) ?_
    refine Runs.bind0 (runs_weightSize hw.hK) ?_
    refine Runs.bind0 (runs_weightSize hw.hV) ?_
    refine Runs.bind0 (runs_weightSize hw.hO) ?_
    refine Runs.bind0 (runs_weightSize hw.hU) ?_
    refine Runs.bind0 (runs_weightSize hw.hC) ?_
    dsimp only
    rw [← hV, ← hn, hw.hEs, hw.hQs]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    rw [← hw.hEs, ← hw.hQs, ite_eq_left (wellFormed_of_WF hw)]
    refine Runs.bind0 (runs_rows hw.hE hw.hEn) ?_
    refine Runs.bind0 (runs_rows hw.hP hw.hPn) ?_
    refine Runs.bind0 (runs_weight hw.hC (by rw [hw.hCn]; omega)) ?_
    refine Runs.bind (runs_Qc hw) ?_
    refine Runs.bind0 (runs_cols hw.hK hw.hKn) ?_
    refine Runs.bind0 (runs_rows hw.hV hw.hVn) ?_
    refine Runs.bind0 (runs_cols hw.hO hw.hOn) ?_
    refine Runs.bind0 (runs_cols hw.hU hw.hUn) ?_
    simp only [getD_mat hQ]
    refine Runs.bind (runs_rq N) ?_
    refine Runs.bind (runs_mm _ _ _ _ _) ?_
    refine Runs.bind (runs_mm _ _ _ _ _) ?_
    refine Runs.bind (runs_mm _ _ _ _ _) ?_
    refine Runs.bind (runs_mm _ _ _ _ _) ?_
    refine Runs.bind (runs_mm _ _ _ _ _) ?_
    refine Runs.bind (runs_mm _ _ _ _ _) ?_
    refine Runs.bind (runs_mm _ _ _ _ _) ?_
    rw [transpose_mat]
    refine Runs.bind (runs_mm _ _ _ _ _) ?_
    refine Runs.bind (runs_mm _ _ _ _ _) ?_
    refine Runs.bind (runs_mm _ _ _ _ _) ?_
    refine Runs.bind (runs_Ot N) ?_
    refine Runs.bind (runs_Od N) ?_
    refine Runs.bind (runs_Dd N) ?_
    refine Runs.bind (runs_X N.V N.n N.SEf N.SPf hexp) ?_
    refine Runs.bind (runs_mapM (c := fun _ => (N.V - 1) * (N.n * 4 + (N.n - 1)) +
      (N.V - 1 - 1) + 1) _ fun x hx => (runs_test _ _ _ _ _ _ _).congr rfl ?_) ?_
    · rw [length_others (hl x hx)]
    · exact Runs.pure _
  case eq =>
    rw [sum_map_const', hsp, length_allInputs, List.prod_replicate]
    unfold bill tableCost
    ring

/-- One deterministic step of a run that succeeds. -/
macro "gstep " t:term : tactic =>
  `(tactic| (refine Sat.bind (Sat.of_runs $t) fun _ h => ?_; subst h))

/-- **What a run returns.** On well-formed weights, every run of the checker that succeeds returns
    `countV` of bounds on `exp` of the scores, `exp` having accepted every score. -/
theorem sat_check {N : Net} {g : Graph} (task : Task) {env : Env}
    (hw : N.WF env.weights) (hV : N.V = g.values) (hn : N.n = g.positions) (hn0 : 0 < N.n) :
    Sat (check Interp.counting g task) env fun count => ∃ X : List (List (List (Q × Q))),
      (∀ q < N.V, ∀ t < N.V, ∀ p < N.n,
        expInterval (N.SEf q t + N.SPf q p) =
          some ((((X.getD q []).getD t []).getD p (⟨0⟩, ⟨0⟩)).1.val,
            (((X.getD q []).getD t []).getD p (⟨0⟩, ⟨0⟩)).2.val)) ∧
      count = countV N task X := by
  have hQ : N.n - 1 < N.n := by omega
  unfold check
  gstep (runs_weightShape hw.hE)
  gstep (runs_weightShape hw.hP)
  gstep (runs_weightShape hw.hQ)
  gstep (runs_weightShape hw.hK)
  gstep (runs_weightShape hw.hV)
  gstep (runs_weightShape hw.hO)
  gstep (runs_weightShape hw.hU)
  gstep (runs_weightShape hw.hC)
  gstep (runs_weightSize hw.hE)
  gstep (runs_weightSize hw.hP)
  gstep (runs_weightSize hw.hQ)
  gstep (runs_weightSize hw.hK)
  gstep (runs_weightSize hw.hV)
  gstep (runs_weightSize hw.hO)
  gstep (runs_weightSize hw.hU)
  gstep (runs_weightSize hw.hC)
  dsimp only
  rw [← hV, ← hn, hw.hEs, hw.hQs]
  simp only [List.getD_cons_succ, List.getD_cons_zero]
  rw [← hw.hEs, ← hw.hQs, ite_eq_left (wellFormed_of_WF hw)]
  gstep (runs_rows hw.hE hw.hEn)
  gstep (runs_rows hw.hP hw.hPn)
  gstep (runs_weight hw.hC (by rw [hw.hCn]; omega))
  gstep (runs_Qc hw)
  gstep (runs_cols hw.hK hw.hKn)
  gstep (runs_rows hw.hV hw.hVn)
  gstep (runs_cols hw.hO hw.hOn)
  gstep (runs_cols hw.hU hw.hUn)
  simp only [getD_mat hQ]
  gstep (runs_rq N)
  gstep (runs_mm _ _ _ _ _)
  gstep (runs_mm _ _ _ _ _)
  gstep (runs_mm _ _ _ _ _)
  gstep (runs_mm _ _ _ _ _)
  gstep (runs_mm _ _ _ _ _)
  gstep (runs_mm _ _ _ _ _)
  gstep (runs_mm _ _ _ _ _)
  rw [transpose_mat]
  gstep (runs_mm _ _ _ _ _)
  gstep (runs_mm _ _ _ _ _)
  gstep (runs_mm _ _ _ _ _)
  gstep (runs_Ot N)
  gstep (runs_Od N)
  gstep (runs_Dd N)
  refine Sat.bind (sat_X N.V N.n N.SEf N.SPf) fun X hX => ?_
  gstep (runs_mapM (c := fun x => (others N.V (task.label x)).length * (N.n * 4 + (N.n - 1)) +
    ((others N.V (task.label x)).length - 1) + 1) _ fun x _ => runs_test _ _ _ _ _ _ _)
  exact Sat.pure ⟨X, hX, rfl⟩

end PathBrute
