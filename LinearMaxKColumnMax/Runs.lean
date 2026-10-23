import LinearMaxKColumnMax.Checker
import LinearMaxK.Runs

/-!
# What the checker of entry 5 computes, and what it costs

As in entries 1 and 3: each function of the checker, run by the counting interpreter, as a `Runs`,
with its value and its exact number of operations. The tests read only entries of the columns and
the summaries, so their runs hold for any columns and summaries; `runs_check` puts in the columns
of `M = U L E` and their summaries, for well-formed weights and a valid plan.
-/

namespace LinearMaxKColumnMax

open CompactCheck Common LinearMaxK

/-- The largest of `vs`, or zero if there are none, as `maxOf` folds it. -/
def maxOfV : List ℚ → ℚ
  | [] => 0
  | v :: vs => vs.foldl max v

section Values

variable (cols : List (List Q)) (ss : List (Summary K))

/-- Entry `(j, t)` of the columns, as a number. -/
def ent (j t : ℕ) : ℚ := (entry K cols j t).val

/-- The summaries of column `t`, computed from the columns. -/
def summQ (V t : ℕ) : Summary K :=
  ⟨⟨maxOfV ((others V t).map fun j => ent cols j t)⟩,
    ⟨max (maxOfV ((others V t).map fun j => ent cols j t)) (ent cols t t)⟩,
    ⟨ent cols t t - maxOfV ((others V t).map fun j => ent cols j t)⟩⟩

/-- The loss `ℓ(t) = top_t - M[m, t]`. -/
def loss (m t : ℕ) : ℚ := (sm K ss t).top.val - ent cols m t

/-- The largest loss over `[lo, hi]`, as the checker folds it. -/
def lossMax (m lo hi : ℕ) : ℚ :=
  ((List.range' (lo + 1) (hi - lo)).map (loss cols ss m)).foldl max (loss cols ss m lo)

/-- The test of a box. -/
def boxOk (k m lo hi : ℕ) : Bool :=
  decide (((k - 1 : ℕ) : ℚ) * lossMax cols ss m lo hi < (sm K ss m).dm.val)

/-- The exact margin test against `j`, of an input whose tokens other than `m` are `os` and which
    holds `m` `c` times. -/
def jOk (m c : ℕ) (os : List ℕ) (j : ℕ) : Bool :=
  decide ((os.map fun t => ent cols j t - ent cols m t).sum <
    (c : ℚ) * (ent cols m m - ent cols j m))

/-- The tokens of `x` other than its largest. -/
def othersOf (x : Input) : List ℕ := x.filter fun t => t != x.foldl max 0

/-- How many times `x` holds its largest token. -/
def copies (x : Input) : ℕ := (x.filter fun t => t == x.foldl max 0).length

/-- The distinct tokens of `x` other than its largest. -/
def distinctOf (x : Input) : List ℕ := (List.range (x.foldl max 0)).filter fun j => x.contains j

/-- The refined test of `x`. -/
def refinedOk (x : Input) : Bool :=
  decide (((othersOf x).map fun t => (sm K ss t).mx.val - ent cols (x.foldl max 0) t).sum <
      (copies x : ℚ) * (sm K ss (x.foldl max 0)).dm.val) &&
    (distinctOf x).all (jOk cols (x.foldl max 0) (copies x) (othersOf x))

/-- Logit `j` of `x`, from the columns, as `logit` adds it up. -/
def logitV (x : Input) (j : ℕ) : ℚ := ent cols j (x.headD 0) + (x.tail.map (ent cols j)).sum

/-- The exact test of `x`. -/
def exactOk (V : ℕ) (x : Input) : Bool :=
  decide (maxOfV ((others V (x.foldl max 0)).map (logitV cols x)) <
    logitV cols x (x.foldl max 0))

/-- The test of a term. -/
def termOk (V k : ℕ) : Term → Bool
  | .diag m => decide (0 < (sm K ss m).dm.val)
  | .box m lo hi _ => boxOk cols ss k m lo hi
  | .refined x => refinedOk cols ss x
  | .exact x => exactOk cols V x

end Values

/-! ## Costs -/

/-- The operations of the refined test of `x`: with `n` other tokens, `c` copies of the largest
    and `u` distinct other tokens, `(2n - 1) + (c - 1) + 1` for the test against the outputs that
    are not tokens of `x`, and `(2n - 1) + (c - 1) + 3` for each exact margin, with its gate. -/
def refinedCost (x : Input) : ℕ :=
  (2 * (othersOf x).length - 1) + (copies x - 1) + 1 +
    (distinctOf x).length * ((2 * (othersOf x).length - 1) + (copies x - 1) + 3)

/-- The operations of the test of a term. -/
def termCost (V k : ℕ) : Term → ℕ
  | .diag _ => 1
  | .box _ lo hi _ => 2 * (hi - lo) + (k - 2) + 2
  | .refined x => refinedCost x
  | .exact _ => (k - 1) * V + (V - 2) + 1

/-- The bill of a plan: the columns `V (d^2 + V d)`, their summaries `V ((V - 2) + 2)`, and the
    tests of the terms. -/
def billPlan (V k d : ℕ) (plan : List Term) : ℕ :=
  V * (d * d + V * d) + V * ((V - 2) + 2) + (plan.map (termCost V k)).sum

/-! ## Runs -/

theorem length_others {V t : ℕ} (ht : t < V) : (others V t).length = V - 1 := by
  have h := countP_ne t V
  simp only [ht, ↓reduceIte] at h
  rw [others, ← List.countP_eq_length_filter, ← h]
  exact List.countP_congr fun j _ => by simp [bne_iff_ne]

/-! ## Folds, by their values -/

theorem Q_eq {a b : Q} (h : a.val = b.val) : a = b := by
  cases a; cases b; simp only at h; rw [h]

theorem val_foldl_max {α : Type} (F : α → ℚ) : ∀ (l : List α) (v : Q),
    (l.foldl (fun a w => (⟨max a.val (F w)⟩ : Q)) v).val = (l.map F).foldl max v.val
  | [], _ => rfl
  | _ :: l, _ => val_foldl_max F l _

theorem val_foldl_add {α : Type} (F : α → ℚ) : ∀ (l : List α) (v : Q),
    (l.foldl (fun a w => (⟨a.val + F w⟩ : Q)) v).val = v.val + (l.map F).sum
  | [], _ => by simp
  | w :: l, v => by
    rw [List.foldl_cons, val_foldl_add F l, List.map_cons, List.sum_cons]
    simp only
    ring

theorem foldl_and {α : Type} (p : α → Bool) : ∀ (l : List α) (b : Bool),
    l.foldl (fun b a => b && p a) b = (b && l.all p)
  | [], b => by simp
  | a :: l, b => by rw [List.foldl_cons, foldl_and p l, List.all_cons, Bool.and_assoc]

theorem foldl_nadd {α : Type} (F : α → ℕ) : ∀ (l : List α) (n : ℕ),
    l.foldl (fun n a => Nat.add n (F a)) n = n + (l.map F).sum
  | [], n => by simp
  | a :: l, n => by
    rw [List.foldl_cons, foldl_nadd F l, List.map_cons, List.sum_cons]
    simp only [Nat.add_eq]
    ring

theorem sum_map_const {α : Type} (l : List α) (c : ℕ) : (l.map fun _ => c).sum = l.length * c := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih, List.length_cons]; ring

/-! ## The parts of the checker -/

section

variable {env : Env}

theorem runs_maxOf : ∀ vs : List Q, Runs (maxOf K vs) env ⟨maxOfV (vs.map Q.val)⟩ (vs.length - 1)
  | [] => (Runs.pure _).congr rfl rfl
  | v :: vs => by
    simp only [maxOf]
    exact (runs_foldlM (c := fun _ => 1) vs v fun a w _ => runs_max cat a w).congr
      (Q_eq (by rw [val_foldl_max Q.val]; simp [maxOfV])) (by simp)

theorem runs_rep (v : Q) (c : ℕ) : Runs (rep K v c) env ⟨(c : ℚ) * v.val⟩ (c - 1) := by
  unfold rep
  split
  · rename_i hc
    subst hc
    exact (Runs.pure _).congr (by simp) rfl
  · rename_i hc
    refine (runs_foldlM (c := fun _ => 1) (List.range (c - 1)) v
      fun s _ _ => runs_add cat s v).congr (Q_eq ?_) (by simp)
    rw [val_foldl_add (fun _ => v.val)]
    simp only [List.map_const', List.sum_replicate, List.length_range, nsmul_eq_mul]
    obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    push_cast
    ring

/-- `Σ_{t ∈ ts} (f t - g t)`, as a number. -/
theorem runs_sumDiff (f g : ℕ → Q) : ∀ ts : List ℕ,
    Runs (sumDiff K f g ts) env ⟨(ts.map fun t => (f t).val - (g t).val).sum⟩ (2 * ts.length - 1)
  | [] => (Runs.pure _).congr (by simp) rfl
  | t :: ts => by
    simp only [sumDiff, Interp.counting_bind]
    refine Runs.bind' (runs_sub cat (f t) (g t))
      (runs_foldlM (g := fun acc u => (⟨acc.val + ((f u).val - (g u).val)⟩ : Q))
        (c := fun _ => 2) ts _ fun acc u _ =>
          Runs.bind' (runs_sub cat (f u) (g u)) (runs_add cat acc _) rfl rfl) ?_ ?_
    · refine Q_eq ?_
      rw [val_foldl_add (fun u => (f u).val - (g u).val), List.map_cons, List.sum_cons]
    · simp only [sum_map_const, List.length_cons]; omega

variable (cols : List (List Q)) (ss : List (Summary K))

theorem runs_boxTest (k m lo hi : ℕ) :
    Runs (boxTest K cols ss k m lo hi) env (boxOk cols ss k m lo hi)
      (2 * (hi - lo) + (k - 2) + 2) := by
  simp only [boxTest, Interp.counting_bind]
  refine Runs.bind' (runs_sub cat _ _)
    (Runs.bind' (runs_foldlM (g := fun a t => (⟨max a.val (loss cols ss m t)⟩ : Q))
        (c := fun _ => 2) _ _ fun a t _ =>
          Runs.bind' (runs_sub cat _ _) (runs_max cat a _) rfl rfl)
      (Runs.bind' (runs_rep _ (k - 1)) (runs_lt cat _ _) rfl rfl) rfl rfl) ?_ ?_
  · simp only [boxOk, lossMax]
    rw [val_foldl_max (loss cols ss m)]
    rfl
  · simp only [sum_map_const, List.length_range']; omega

theorem runs_refinedTest (x : Input) :
    Runs (refinedTest K cols ss x) env (refinedOk cols ss x) (refinedCost x) := by
  simp only [refinedTest, Interp.counting_bind]
  refine Runs.bind' (runs_sumDiff _ _ _)
    (Runs.bind' (runs_rep _ _)
      (Runs.bind' (runs_lt cat _ _)
        (runs_foldlM (g := fun b j => b && jOk cols (x.foldl max 0) (copies x) (othersOf x) j)
          (c := fun _ => (2 * (othersOf x).length - 1) + (copies x - 1) + 3) _ _ fun b j _ =>
            Runs.bind' (runs_sumDiff _ _ _)
              (Runs.bind' (runs_sub cat _ _)
                (Runs.bind' (runs_rep _ _)
                  (Runs.bind' (runs_lt cat _ _) (runs_band cat _ _) rfl rfl) rfl rfl) rfl rfl)
              (by simp only [jOk, ent, othersOf, copies]; rfl)
              (by simp only [othersOf, copies]; omega)) rfl rfl) rfl rfl) ?_ ?_
  · rw [foldl_and]
    simp only [refinedOk, distinctOf, othersOf, copies, ent]
    rfl
  · simp only [refinedCost, sum_map_const, distinctOf, othersOf, copies]; ring

theorem runs_logit (x : Input) (j : ℕ) :
    Runs (logit K cols x j) env ⟨logitV cols x j⟩ x.tail.length := by
  unfold logit
  refine (runs_foldlM (g := fun a t => (⟨a.val + ent cols j t⟩ : Q)) (c := fun _ => 1) _ _
    fun a t _ => runs_add cat a _).congr (Q_eq ?_) (by simp)
  rw [val_foldl_add (ent cols j)]
  rfl

theorem runs_maxOver {f : ℕ → K.M Q} {F : ℕ → ℚ} {C : ℕ} (h : ∀ j, Runs (f j) env ⟨F j⟩ C) :
    ∀ js : List ℕ,
      Runs (maxOver K f js) env ⟨maxOfV (js.map F)⟩ (js.length * C + (js.length - 1))
  | [] => (Runs.pure _).congr rfl (by simp)
  | j :: js => by
    simp only [maxOver, Interp.counting_bind]
    refine Runs.bind' (h j)
      (runs_foldlM (g := fun a j' => (⟨max a.val (F j')⟩ : Q)) (c := fun _ => C + 1) js _
        fun a j' _ => Runs.bind' (h j') (runs_max cat a _) rfl rfl) ?_ ?_
    · refine Q_eq ?_
      rw [val_foldl_max F]
      rfl
    · simp only [sum_map_const, List.length_cons, Nat.add_sub_cancel]
      ring

theorem runs_exactTest {V : ℕ} (hV : 0 < V) {x : Input} (hxV : ∀ t ∈ x, t < V) :
    Runs (exactTest K cols V x) env (exactOk cols V x)
      (V * x.tail.length + (V - 2) + 1) := by
  have hm : x.foldl max 0 < V := label_lt hV hxV
  have hlen := length_others hm
  simp only [exactTest, Interp.counting_bind]
  refine Runs.bind' (runs_maxOver (fun j => runs_logit cols x j) _)
    (Runs.bind' (runs_logit cols x _) (runs_lt cat _ _) rfl rfl) rfl ?_
  rw [hlen]
  obtain ⟨V', rfl⟩ : ∃ V', V = V' + 1 := ⟨V - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [show V' + 1 - 2 = V' - 1 by omega]
  ring

theorem runs_summary {V t : ℕ} (ht : t < V) :
    Runs (summary K cols V t) env (summQ cols V t) ((V - 2) + 2) := by
  simp only [summary, Interp.counting_bind, Interp.counting_pure]
  refine Runs.bind' (runs_maxOf _)
    (Runs.bind' (runs_max cat _ _) (Runs.bind' (runs_sub cat _ _) (Runs.pure _) rfl rfl) rfl rfl)
    ?_ ?_
  · simp [summQ, ent, List.map_map, Function.comp_def]
  · simp only [List.length_map, length_others ht]; omega

theorem runs_summaries {V : ℕ} (ts : List ℕ) (h : ∀ t ∈ ts, t < V) :
    Runs (summaries K cols V ts) env (ts.map (summQ cols V)) (ts.length * ((V - 2) + 2)) :=
  (runs_mapM (c := fun _ => (V - 2) + 2) ts fun t ht => runs_summary cols (h t ht)).congr rfl
    (sum_map_const _ _)

theorem sortedB_iff : ∀ x : List ℕ, sortedB x = true ↔ x.Pairwise (· ≤ ·)
  | [] => by simp [sortedB]
  | a :: l => by
    simp only [sortedB, Bool.and_eq_true, List.all_eq_true, Nat.ble_eq, sortedB_iff l,
      List.pairwise_cons]

theorem validInput_spec {V k : ℕ} {x : Input} :
    validInput V k x = true ↔ x.Pairwise (· ≤ ·) ∧ x.length = k ∧ ∀ t ∈ x, t < V := by
  simp only [validInput, Bool.and_eq_true, sortedB_iff, Nat.beq_eq, List.all_eq_true, Nat.blt_eq,
    and_assoc]

theorem runs_termTest {V k : ℕ} (hV : 0 < V) {t : Term}
    (ht : ∀ x ∈ t.inputs k, validInput V k x = true) :
    Runs (termTest K cols ss V k t) env (termOk cols ss V k t) (termCost V k t) := by
  rcases t with m | ⟨m, lo, hi, dg⟩ | x | x
  · exact (runs_lt cat _ _).congr (by simp [termOk]) rfl
  · exact runs_boxTest cols ss k m lo hi
  · exact runs_refinedTest cols ss x
  · obtain ⟨-, hlen, hxV⟩ := validInput_spec.mp (ht x (by simp [Term.inputs]))
    exact (runs_exactTest cols hV hxV).congr rfl (by simp [termCost, hlen]; ring)

theorem runs_countTerms {V k : ℕ} (hV : 0 < V) (plan : List Term)
    (h : ∀ t ∈ plan, ∀ x ∈ t.inputs k, validInput V k x = true) :
    Runs (countTerms K cols ss V k plan) env
      ((plan.map fun t => cond (termOk cols ss V k t) (t.size V k) 0).sum)
      ((plan.map (termCost V k)).sum) := by
  unfold countTerms
  refine (runs_foldlM (g := fun n t => Nat.add n (cond (termOk cols ss V k t) (t.size V k) 0))
    (c := termCost V k) plan _ fun n t ht =>
      Runs.bind' (runs_termTest cols ss hV (h t ht)) (Runs.pure _) rfl
        (Nat.add_zero _)).congr ?_ rfl
  rw [foldl_nadd]
  simp

end

/-! ## The whole checker -/

/-- The summaries of the columns of `M`. -/
def summsQ (tE tL tU : Tensor ℚ) (V d : ℕ) : List (Summary K) :=
  (List.range V).map (summQ (colsQ tE tL tU V d) V)

theorem planOk_spec {V k : ℕ} {plan : List Term} (h : planOk V k plan = true) :
    (∀ t ∈ plan, t.valid V = true) ∧ (∀ t ∈ plan, ∀ x ∈ t.inputs k, validInput V k x = true) ∧
      nodupB (plan.flatMap (Term.inputs k)) = true := by
  simp only [planOk, Bool.and_eq_true, List.all_eq_true, List.mem_flatMap] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  exact ⟨h1, fun t ht x hx => h2 x ⟨t, ht, hx⟩, h3⟩

/-- What the checker of a valid plan does on a network of the family with well-formed weights: its
    count, from the terms' tests, and its bill. -/
theorem runs_check {env : Env} {g : Graph} {d : ℕ} {tE tL tU : Tensor ℚ}
    (hw : WF env.weights g.values d tE tL tU) (hV : 0 < g.values) {plan : List Term}
    (hplan : planOk g.values g.positions plan = true) (task : Task) :
    Runs (check K plan g task) env
      ((plan.map fun t => cond (termOk (colsQ tE tL tU g.values d) (summsQ tE tL tU g.values d)
          g.values g.positions t) (t.size g.values g.positions) 0).sum)
      (billPlan g.values g.positions d plan) := by
  simp only [check, Interp.counting_bind]
  refine Runs.bind0 (runs_weightShape hw.hE) ?_
  refine Runs.bind0 (runs_weightShape hw.hL) ?_
  refine Runs.bind0 (runs_weightShape hw.hU) ?_
  refine Runs.bind0 (runs_weightSize hw.hE) ?_
  refine Runs.bind0 (runs_weightSize hw.hL) ?_
  refine Runs.bind0 (runs_weightSize hw.hU) ?_
  have hd : tE.shape.headD 0 = d := by rw [hw.hEs]; rfl
  simp only [hd, wellFormed_of_WF hw, hplan, Bool.and_self, ↓reduceIte]
  exact Runs.bind' (runs_columns hw fun t ht => List.mem_range.mp ht)
    (Runs.bind' (runs_summaries (colsQ tE tL tU g.values d) (List.range g.values)
        fun t ht => List.mem_range.mp ht)
      (runs_countTerms (colsQ tE tL tU g.values d) _ hV plan (planOk_spec hplan).2.1) rfl rfl)
    rfl (by simp only [billPlan, List.length_range]; ring)

end LinearMaxKColumnMax
