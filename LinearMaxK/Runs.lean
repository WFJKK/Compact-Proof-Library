import LinearMaxK.Checker
import LinearMaxK.Groups

/-!
# What the checker computes, and what it costs

Each function of the checker, run by the counting interpreter on well-formed weights, as a `Runs`:
its value in terms of `M = U L E`, and the exact number of operations it is charged. Together these
give the checker's count and its bill (`runs_check`).
-/

namespace LinearMaxK

open CompactCheck Common

/-- The counting interpreter, which the acceptance service runs. -/
abbrev K := Interp.counting

section

variable {env : Env}

theorem runs_readW {name : String} {t : Tensor ℚ} (h : List.lookup name env.weights = some t) :
    ∀ {is : List ℕ}, (∀ i ∈ is, i < t.data.size) →
      Runs (readW K name is) env (is.map fun i => (⟨t.get i⟩ : Q)) 0
  | [], _ => Runs.pure _
  | i :: is, hi => by
    simp only [readW, Interp.counting_bind, Interp.counting_pure]
    exact Runs.bind' (runs_weight h (hi i List.mem_cons_self))
      (Runs.bind' (runs_readW h fun j hj => hi j (List.mem_cons_of_mem _ hj)) (Runs.pure _) rfl rfl)
      (by simp) (by simp)

theorem runs_dot (f g : ℕ → ℚ) : ∀ (l : List ℕ) (acc : Q),
    Runs (dot K (l.map fun i => (⟨f i⟩ : Q)) (l.map fun i => (⟨g i⟩ : Q)) acc) env
      ⟨acc.val + (l.map fun i => f i * g i).sum⟩ l.length
  | [], acc => by
    simp only [List.map_nil, dot]
    exact (Runs.pure acc).congr (by cases acc; simp) rfl
  | i :: l, acc => by
    simp only [List.map_cons, dot, Interp.counting_bind]
    exact Runs.bind' (runs_muladd cat acc ⟨f i⟩ ⟨g i⟩) (runs_dot f g l _) (by simp [add_assoc])
      (by simp [Nat.add_comm])

theorem runs_matVec {name : String} {W : Tensor ℚ} (hW : List.lookup name env.weights = some W)
    {n : ℕ} (g : ℕ → ℚ) :
    ∀ {rs : List ℕ}, (∀ r ∈ rs, ∀ i < n, r * n + i < W.data.size) →
      Runs (matVec K name n ((List.range n).map fun i => (⟨g i⟩ : Q)) rs) env
        (rs.map fun r => (⟨((List.range n).map fun i => W.get (r * n + i) * g i).sum⟩ : Q))
        (rs.length * n)
  | [], _ => (Runs.pure _).congr rfl (by simp)
  | r :: rs, hr => by
    simp only [matVec, Interp.counting_bind, Interp.counting_pure]
    have hrow := runs_readW (env := env) hW (is := (List.range n).map fun i => r * n + i)
      (by simpa using hr r List.mem_cons_self)
    rw [List.map_map] at hrow
    exact Runs.bind' hrow
      (Runs.bind' (runs_dot (fun i => W.get (r * n + i)) g (List.range n) _)
        (Runs.bind' (runs_matVec hW g fun r' hr' => hr r' (List.mem_cons_of_mem _ hr'))
          (Runs.pure _) rfl rfl) rfl rfl)
      (by simp) (by simp [Nat.add_mul, Nat.add_comm])

/-! ## The columns of `M` -/

/-- Column `t` of `M`, as the checker holds it: a list over the outputs. -/
def colQ (tE tL tU : Tensor ℚ) (V d t : ℕ) : List Q :=
  (List.range V).map fun j => ⟨Mval tE tL tU V d j t⟩

variable {V d : ℕ} {tE tL tU : Tensor ℚ}

theorem runs_column (hw : WF env.weights V d tE tL tU) {t : ℕ} (ht : t < V) :
    Runs (column K V d t) env (colQ tE tL tU V d t) (d * d + V * d) := by
  simp only [column, Interp.counting_bind]
  have he := runs_readW (env := env) hw.hE (is := (List.range d).map fun b => b * V + t)
    (by intro i hi; simp only [List.mem_map, List.mem_range] at hi
        obtain ⟨b, hb, rfl⟩ := hi; rw [hw.hEn]; exact pos_lt hb ht)
  rw [List.map_map] at he
  refine Runs.bind0 he ?_
  exact Runs.bind' (runs_matVec hw.hL (fun b => tE.get (b * V + t)) (rs := List.range d)
      (by intro r hr i hi; rw [hw.hLn]; exact pos_lt (List.mem_range.mp hr) hi))
    (runs_matVec hw.hU _ (rs := List.range V)
      (by intro r hr i hi; rw [hw.hUn]; exact pos_lt (List.mem_range.mp hr) hi))
    (by simp [colQ, Mval, sum_range_eq]) (by simp)

theorem runs_columns (hw : WF env.weights V d tE tL tU) :
    ∀ {ts : List ℕ}, (∀ t ∈ ts, t < V) →
      Runs (columns K V d ts) env (ts.map (colQ tE tL tU V d)) (ts.length * (d * d + V * d))
  | [], _ => (Runs.pure _).congr rfl (by simp)
  | t :: ts, ht => by
    simp only [columns, Interp.counting_bind, Interp.counting_pure]
    exact Runs.bind' (runs_column hw (ht t List.mem_cons_self))
      (Runs.bind' (runs_columns hw fun u hu => ht u (List.mem_cons_of_mem _ hu)) (Runs.pure _)
        rfl rfl) (by simp) (by simp [Nat.add_mul, Nat.add_comm])

/-- The columns of `M`, all of them. -/
def colsQ (tE tL tU : Tensor ℚ) (V d : ℕ) : List (List Q) := (List.range V).map (colQ tE tL tU V d)

theorem entry_colsQ {j t : ℕ} (hj : j < V) (ht : t < V) :
    entry K (colsQ tE tL tU V d) j t = ⟨Mval tE tL tU V d j t⟩ := by
  simp [entry, colsQ, colQ, List.getD_eq_getElem?_getD, hj, ht]

/-! ## The tests -/

/-- `D(t) = M[m, t] - M[j, t]`: how much more token `t` gives the output `m` than the output `j`. -/
def Dif (tE tL tU : Tensor ℚ) (V d m j t : ℕ) : ℚ := Mval tE tL tU V d m t - Mval tE tL tU V d j t

/-- `min_{t ≤ m} D(t)`, as the checker folds it. -/
def mu (tE tL tU : Tensor ℚ) (V d m j : ℕ) : ℚ :=
  (List.range m).foldl (fun a t => min a (Dif tE tL tU V d m j t)) (Dif tE tL tU V d m j m)

/-- The test of the group `m` against the output `j`. -/
def pairOk (tE tL tU : Tensor ℚ) (V d k m j : ℕ) : Bool :=
  decide (0 < Dif tE tL tU V d m j m + ((k - 1 : ℕ) : ℚ) * mu tE tL tU V d m j)

/-- The tests of the group `m` against every other output. -/
def groupOk (tE tL tU : Tensor ℚ) (V d k m : ℕ) : Bool :=
  (List.range V).all fun j => decide (j = m) || pairOk tE tL tU V d k m j

theorem runs_minDiff {m j : ℕ} (hm : m < V) (hj : j < V) :
    ∀ (ts : List ℕ) (acc : Q), (∀ t ∈ ts, t < V) →
      Runs (minDiff K (colsQ tE tL tU V d) m j ts acc) env
        ⟨ts.foldl (fun a t => min a (Dif tE tL tU V d m j t)) acc.val⟩ (2 * ts.length)
  | [], acc, _ => by
    simp only [minDiff, List.foldl_nil]
    exact (Runs.pure acc).congr (by cases acc; rfl) rfl
  | t :: ts, acc, ht => by
    have ht0 := ht t List.mem_cons_self
    simp only [minDiff, Interp.counting_bind, entry_colsQ hm ht0, entry_colsQ hj ht0]
    exact Runs.bind' (runs_sub cat _ _)
      (Runs.bind' (runs_min cat _ _)
        (runs_minDiff hm hj ts _ fun u hu => ht u (List.mem_cons_of_mem _ hu)) rfl rfl)
      (by simp [Dif]) (by simp; omega)

theorem runs_pairTest {k m j : ℕ} (hm : m < V) (hj : j < V) :
    Runs (pairTest K (colsQ tE tL tU V d) ⟨((k - 1 : ℕ) : ℚ)⟩ m j) env
      (pairOk tE tL tU V d k m j) (2 * m + 3) := by
  simp only [pairTest, Interp.counting_bind, entry_colsQ hm hm, entry_colsQ hj hm]
  exact Runs.bind' (runs_sub cat _ _)
    (Runs.bind' (runs_minDiff hm hj (List.range m) _
        fun t ht => lt_trans (List.mem_range.mp ht) hm)
      (Runs.bind' (runs_muladd cat _ _ _) (runs_lt cat _ _) rfl rfl) rfl rfl)
    (by simp only [pairOk, mu, Dif]; exact decide_eq_decide.mpr Iff.rfl) (by simp; omega)

theorem runs_groupTest {k m : ℕ} (hm : m < V) :
    ∀ (js : List ℕ), (∀ j ∈ js, j < V) →
      Runs (groupTest K (colsQ tE tL tU V d) ⟨((k - 1 : ℕ) : ℚ)⟩ m js) env
        (js.all fun j => decide (j = m) || pairOk tE tL tU V d k m j)
        (js.countP (fun j => !decide (j = m)) * (2 * m + 4))
  | [], _ => (Runs.pure _).congr rfl (by simp)
  | j :: js, hj => by
    have ih := runs_groupTest (k := k) hm js fun u hu => hj u (List.mem_cons_of_mem _ hu)
    by_cases hjm : j = m
    · simp only [groupTest, hjm, ↓reduceIte]
      exact ih.congr (by simp) (by simp)
    · simp only [groupTest, hjm, ↓reduceIte, Interp.counting_bind]
      exact Runs.bind' (runs_pairTest hm (hj j List.mem_cons_self))
        (Runs.bind' ih (runs_band cat _ _) rfl rfl) (by simp [hjm])
        (by simp [hjm]; ring)

theorem countP_ne (m : ℕ) : ∀ V : ℕ,
    (List.range V).countP (fun j => !decide (j = m)) = V - (if m < V then 1 else 0)
  | 0 => by simp
  | V + 1 => by
    rw [List.range_succ, List.countP_append, countP_ne m V]
    simp only [List.countP_cons, List.countP_nil, Bool.not_eq_true', decide_eq_false_iff_not]
    by_cases h1 : m < V
    · have : V ≠ m := by omega
      simp [h1, this, show m < V + 1 by omega]; omega
    · by_cases h2 : V = m
      · subst h2; simp
      · simp [h1, h2, show ¬ m < V + 1 by omega]

theorem runs_countGroups {k : ℕ} (ok0 : Bool) :
    ∀ (ms : List ℕ), (∀ m ∈ ms, m < V) →
      Runs (countGroups K (colsQ tE tL tU V d) ⟨((k - 1 : ℕ) : ℚ)⟩ ok0 k V ms) env
        ((ms.map fun m => cond (ok0 && groupOk tE tL tU V d k m)
          (Nat.pow (m + 1) k - Nat.pow m k) 0).sum)
        ((ms.map fun m => (V - 1) * (2 * m + 4) + 1).sum)
  | [], _ => (Runs.pure _).congr rfl rfl
  | m :: ms, hm => by
    have hm0 := hm m List.mem_cons_self
    simp only [countGroups, Interp.counting_bind, Interp.counting_pure]
    exact Runs.bind' (runs_groupTest (k := k) hm0 (List.range V) fun j hj => List.mem_range.mp hj)
      (Runs.bind' (runs_band cat _ _)
        (Runs.bind' (runs_countGroups ok0 ms fun u hu => hm u (List.mem_cons_of_mem _ hu))
          (Runs.pure _) rfl rfl) rfl rfl)
      (by simp [groupOk]) (by simp [countP_ne, hm0]; ring)

/-- The forward pass of the guard, on a network of the family: `k d` for the embedding of the
    tokens, `d^2` and `V d` for the two other maps, `V - 1` comparisons. -/
theorem singleCost_family {g : Graph} (hg : IsLinearMaxK g = true) {w : Weights ℚ}
    (hw : WF w g.values d tE tL tU) :
    singleCost g w = some (g.positions * d + d * d + d * g.values + (g.values - 1)) := by
  obtain ⟨hn, ho, -, -⟩ := isLinearMaxK_spec hg
  simp [singleCost, reachable, reachable.go, hn, ho, Op.args, hw.hE, hw.hEs, hw.hL, hw.hLs, hw.hU,
    hw.hUs, normDim, shapeSize]

/-- The guard's input: every token `V - 1`. -/
def guardInput (g : Graph) : Input := List.replicate g.positions (g.values - 1)

/-- The bill: the guard's forward pass, the columns, the literal `k - 1`, and the tests of each
    group (`2m + 4` for each of the `V - 1` other outputs, and a gate). -/
def bill (k V d : ℕ) : ℕ :=
  (k * d + d * d + d * V + (V - 1)) + V * (d * d + V * d) + 1 +
    ((List.range V).map fun m => (V - 1) * (2 * m + 4) + 1).sum

/-- What the checker does on a network of the family with well-formed weights: its count, from the
    guard and the groups' tests, and its bill. -/
theorem runs_check {g : Graph} (hg : IsLinearMaxK g = true)
    (hw : WF env.weights g.values d tE tL tU) :
    Runs (check K g (maxTask g.positions g.values)) env
      (((List.range g.values).map fun m =>
        cond (singleOk g env.weights (maxTask g.positions g.values) (guardInput g) &&
          groupOk tE tL tU g.values d g.positions m)
          (Nat.pow (m + 1) g.positions - Nat.pow m g.positions) 0).sum)
      (bill g.positions g.values d) := by
  simp only [check, Interp.counting_bind]
  refine Runs.bind0 (runs_weightShape hw.hE) ?_
  refine Runs.bind0 (runs_weightShape hw.hL) ?_
  refine Runs.bind0 (runs_weightShape hw.hU) ?_
  simp only [hw.hEs, hw.hLs, hw.hUs, List.headD_cons, beq_self_eq_true, Bool.and_self,
    ↓reduceIte]
  exact Runs.bind' (runs_single (singleCost_family hg hw))
    (Runs.bind' (runs_columns hw fun t ht => List.mem_range.mp ht)
      (Runs.bind' (runs_lit cat _)
        (runs_countGroups _ (List.range g.values) fun m hm => List.mem_range.mp hm) rfl rfl)
      rfl rfl)
    rfl (by simp [bill]; ring)

end

end LinearMaxK
