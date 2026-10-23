import LinearMaxK.Exact

/-!
# The checker's count from a table of integers

At `V = 64` the kernel cannot evaluate the checker in one `decide`: it runs out of memory. This
file splits the evaluation into small statements, each of which the kernel checks on its own.

* The weights of an exported network are integers times a power of two, with one exponent per
  tensor (`dyadic`). So `M = 2^e · MZ`, where `MZ = U L E` is the product of the integer
  mantissas (`Mval_eq`), and every test has the same outcome on `MZ` as on `M` (`groupOk_eq`).
* `rowZ j` computes row `j` of `MZ` from the mantissas. An instance compares each row with a table
  of integers, one `decide` per row.
* `groupOkZ` makes the tests of one group on the table, one `decide` per group.

`check_billed_of_table` puts them together: on such weights, the checker's count is `countZ` of the
table and its bill is `bill V d`.
-/

namespace LinearMaxK

open CompactCheck Common

/-! ## Integer matrices, as lists -/

/-- The dot product of two lists of integers. -/
def dotZ (xs ys : List ℤ) : ℤ := (List.zipWith (· * ·) xs ys).sum

/-- The first `r` rows of `n` entries of a list. -/
def chunks (n : ℕ) : ℕ → List ℤ → List (List ℤ)
  | 0, _ => []
  | r + 1, l => l.take n :: chunks n r (l.drop n)

/-- Entry `(j, t)` of `U L E` for the integer matrices `E` (`d × V`), `L` (`d × d`) and
    `U` (`V × d`), given row-major. -/
def MZ (mE mL mU : List ℤ) (V d j t : ℕ) : ℤ :=
  ∑ a ∈ Finset.range d, mU.getD (j * d + a) 0 *
    ∑ b ∈ Finset.range d, mL.getD (a * d + b) 0 * mE.getD (b * V + t) 0

/-- Row `j` of `U L E`, computed as the kernel evaluates it quickly: entry `t` is `U_j · (L E_t)`
    for the row `U_j` of `U` and the column `E_t` of `E`. -/
def rowZ (mE mL mU : List ℤ) (V d j : ℕ) : List ℤ :=
  let er := chunks V d mE
  let lr := chunks d d mL
  let uj := (chunks d V mU).getD j []
  (List.range V).map fun t => dotZ uj (lr.map fun l => dotZ l (er.map fun r => r.getD t 0))

theorem getD_chunks (n : ℕ) : ∀ (r : ℕ) (l : List ℤ) (a b : ℕ), a < r → b < n →
    ((chunks n r l).getD a []).getD b 0 = l.getD (a * n + b) 0
  | 0, _, _, _, ha, _ => absurd ha (Nat.not_lt_zero _)
  | r + 1, l, 0, b, _, hb => by
    simp [chunks, List.getD_eq_getElem?_getD, hb]
  | r + 1, l, a + 1, b, ha, hb => by
    simp only [chunks, List.getD_cons_succ]
    rw [getD_chunks n r (l.drop n) a b (by omega) hb]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]
    congr 2
    ring

theorem length_chunks (n : ℕ) : ∀ (r : ℕ) (l : List ℤ), (chunks n r l).length = r
  | 0, _ => rfl
  | r + 1, l => by simp [chunks, length_chunks n r]

theorem length_getD_chunks_le (n : ℕ) : ∀ (r : ℕ) (l : List ℤ) (a : ℕ),
    ((chunks n r l).getD a []).length ≤ n
  | 0, _, _ => by simp [chunks]
  | r + 1, l, 0 => by simp [chunks]
  | r + 1, l, a + 1 => by
    simp only [chunks, List.getD_cons_succ]
    exact length_getD_chunks_le n r _ a

/-- A dot product is the sum of the products of the entries, over any range covering one list. -/
theorem dotZ_eq : ∀ (xs ys : List ℤ) (n : ℕ), xs.length ≤ n →
    dotZ xs ys = ∑ i ∈ Finset.range n, xs.getD i 0 * ys.getD i 0
  | [], ys, n, _ => by simp [dotZ]
  | _ :: _, [], n, _ => by simp [dotZ]
  | x :: xs, y :: ys, n, h => by
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by simp at h; omega⟩
    rw [Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    rw [← dotZ_eq xs ys n (by simp at h; omega)]
    simp [dotZ, add_comm]

theorem getD_map_range {α : Type} (F : ℕ → α) (x : α) {V t : ℕ} (ht : t < V) :
    ((List.range V).map F).getD t x = F t := by
  simp [List.getD_eq_getElem?_getD, ht]

theorem getD_map_dotZ (col : List ℤ) : ∀ (l : List (List ℤ)) (a : ℕ),
    (l.map fun r => dotZ r col).getD a 0 = dotZ (l.getD a []) col
  | [], _ => by simp [dotZ]
  | _ :: _, 0 => rfl
  | _ :: l, a + 1 => by simp only [List.map_cons, List.getD_cons_succ]; exact getD_map_dotZ col l a

theorem getD_map_getD (t : ℕ) : ∀ (l : List (List ℤ)) (b : ℕ),
    (l.map fun r => r.getD t 0).getD b 0 = (l.getD b []).getD t 0
  | [], _ => by simp
  | _ :: _, 0 => rfl
  | _ :: l, b + 1 => by simp only [List.map_cons, List.getD_cons_succ]; exact getD_map_getD t l b

/-- `rowZ` computes the rows of `MZ`. -/
theorem getD_rowZ {mE mL mU : List ℤ} {V d j t : ℕ} (hj : j < V) (ht : t < V) :
    (rowZ mE mL mU V d j).getD t 0 = MZ mE mL mU V d j t := by
  simp only [rowZ]
  rw [getD_map_range _ _ ht, dotZ_eq _ _ d (length_getD_chunks_le d V mU j)]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [Finset.mem_range] at ha
  rw [getD_chunks d V mU j a hj ha, getD_map_dotZ, dotZ_eq _ _ d (length_getD_chunks_le d d mL a)]
  congr 1
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [Finset.mem_range] at hb
  rw [getD_chunks d d mL a b ha hb, getD_map_getD, getD_chunks V d mE b t hb ht]

/-! ## The tests on a table of rows -/

/-- `D(t) = M[m, t] - M[j, t]`, on a table of rows. -/
def DZ (rows : List (List ℤ)) (m j t : ℕ) : ℤ :=
  (rows.getD m []).getD t 0 - (rows.getD j []).getD t 0

/-- The test of the group `m` against the output `j`, on a table of rows: as `pairOk`, with the
    minimum folded along the two rows. -/
def pairOkZ (rows : List (List ℤ)) (k m j : ℕ) : Bool :=
  let rm := rows.getD m []
  let rj := rows.getD j []
  let dm := rm.getD m 0 - rj.getD m 0
  decide (0 < dm + ((k - 1 : ℕ) : ℤ) * (List.zipWith (· - ·) (rm.take m) (rj.take m)).foldl min dm)

/-- The tests of the group `m`, on a table of rows. -/
def groupOkZ (rows : List (List ℤ)) (k V m : ℕ) : Bool :=
  (List.range V).all fun j => decide (j = m) || pairOkZ rows k m j

/-- The checker's count, from the groups' tests on a table of rows. -/
def countZ (rows : List (List ℤ)) (k V : ℕ) : ℕ :=
  ((List.range V).map fun m => cond (groupOkZ rows k V m) (Nat.pow (m + 1) k - Nat.pow m k) 0).sum

theorem zipWith_take {f : ℤ → ℤ → ℤ} {l₁ l₂ : List ℤ} {m : ℕ} (h₁ : m ≤ l₁.length)
    (h₂ : m ≤ l₂.length) :
    List.zipWith f (l₁.take m) (l₂.take m) =
      (List.range m).map fun t => f (l₁.getD t 0) (l₂.getD t 0) := by
  refine List.ext_getElem (by simp; omega) fun i hi _ => ?_
  simp only [List.length_zipWith, List.length_take] at hi
  simp [List.getElem_zipWith, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem
    (show i < l₁.length by omega), List.getElem?_eq_getElem (show i < l₂.length by omega)]

theorem pairOkZ_eq (rows : List (List ℤ)) {k m j : ℕ} (hm : m ≤ (rows.getD m []).length)
    (hj : m ≤ (rows.getD j []).length) :
    pairOkZ rows k m j = decide (0 < DZ rows m j m + ((k - 1 : ℕ) : ℤ) *
      (List.range m).foldl (fun a t => min a (DZ rows m j t)) (DZ rows m j m)) := by
  simp only [pairOkZ, zipWith_take hm hj, List.foldl_map, DZ]
  exact decide_eq_decide.mpr Iff.rfl

/-! ## From the rational weights to the integer mantissas -/

theorem dyadic_eq (m e : ℤ) : dyadic m e = (m : ℚ) * (2 : ℚ) ^ e := by
  unfold dyadic
  split
  · rename_i h
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h
    simp [zpow_natCast]
  · rename_i h
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, e = -(n : ℤ) := ⟨(-e).toNat, by omega⟩
    simp [zpow_neg, zpow_natCast, div_eq_mul_inv]

/-- A tensor of dyadic rationals with one exponent. -/
def dyadicTensor (shape : List ℕ) (ms : List ℤ) (e : ℤ) : Tensor ℚ :=
  ⟨shape, (ms.map (dyadic · e)).toArray⟩

theorem get_dyadicTensor (shape : List ℕ) (ms : List ℤ) (e : ℤ) (i : ℕ) :
    (dyadicTensor shape ms e).get i = (ms.getD i 0 : ℚ) * 2 ^ e := by
  by_cases hi : i < ms.length
  · simp [dyadicTensor, Tensor.get, Array.getD, hi, List.getD_eq_getElem?_getD, dyadic_eq]
  · simp [dyadicTensor, Tensor.get, Array.getD, hi, List.getD_eq_getElem?_getD]

/-- `M = 2^(eE + eL + eU) · MZ`. -/
theorem Mval_eq (mE mL mU : List ℤ) (eE eL eU : ℤ) (sE sL sU : List ℕ) (V d j t : ℕ) :
    Mval (dyadicTensor sE mE eE) (dyadicTensor sL mL eL) (dyadicTensor sU mU eU) V d j t =
      (2 : ℚ) ^ (eE + eL + eU) * (MZ mE mL mU V d j t : ℚ) := by
  simp only [Mval, get_dyadicTensor, MZ]
  push_cast
  rw [zpow_add₀ two_ne_zero, zpow_add₀ two_ne_zero]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem foldl_min_scale {c : ℚ} (hc : 0 ≤ c) (f : ℕ → ℚ) (g : ℕ → ℤ) (hfg : ∀ t, f t = c * g t) :
    ∀ (l : List ℕ) (a : ℤ),
      l.foldl (fun x t => min x (f t)) (c * a) = c * (l.foldl (fun x t => min x (g t)) a : ℤ)
  | [], a => by simp
  | t :: l, a => by
    simp only [List.foldl_cons]
    rw [hfg t, ← mul_min_of_nonneg _ _ hc, ← Int.cast_min]
    exact foldl_min_scale hc f g hfg l _

section Bridge

variable {mE mL mU : List ℤ} {eE eL eU : ℤ} {sE sL sU : List ℕ} {V d : ℕ} {rows : List (List ℤ)}

/-- On a table of the rows of `MZ`, a test has the same outcome as on `M`. -/
theorem pairOk_eq (hrows : ∀ j < V, rows.getD j [] = rowZ mE mL mU V d j) {k m j : ℕ}
    (hm : m < V) (hj : j < V) :
    pairOk (dyadicTensor sE mE eE) (dyadicTensor sL mL eL) (dyadicTensor sU mU eU) V d k m j =
      pairOkZ rows k m j := by
  have hc : (0 : ℚ) < 2 ^ (eE + eL + eU) := zpow_pos two_pos _
  have hlen : ∀ i < V, (rows.getD i []).length = V := fun i hi => by
    rw [hrows i hi]; simp [rowZ]
  have hD : ∀ t < V, Dif (dyadicTensor sE mE eE) (dyadicTensor sL mL eL) (dyadicTensor sU mU eU)
      V d m j t = 2 ^ (eE + eL + eU) * (DZ rows m j t : ℚ) := fun t ht => by
    simp only [Dif, Mval_eq, DZ, hrows m hm, hrows j hj, getD_rowZ hm ht, getD_rowZ hj ht]
    push_cast; ring
  rw [pairOkZ_eq rows (by rw [hlen m hm]; omega) (by rw [hlen j hj]; omega)]
  unfold pairOk mu
  have hfold := foldl_min_scale hc.le
    (fun t => if t < V then Dif (dyadicTensor sE mE eE) (dyadicTensor sL mL eL)
      (dyadicTensor sU mU eU) V d m j t else 2 ^ (eE + eL + eU) * (DZ rows m j t : ℚ))
    (DZ rows m j) (fun t => by split_ifs with ht <;> [exact hD t ht; rfl]) (List.range m)
    (DZ rows m j m)
  have hcongr : ∀ (l : List ℕ), (∀ t ∈ l, t < V) → ∀ a : ℚ,
      l.foldl (fun x t => min x (Dif (dyadicTensor sE mE eE) (dyadicTensor sL mL eL)
        (dyadicTensor sU mU eU) V d m j t)) a =
      l.foldl (fun x t => min x (if t < V then Dif (dyadicTensor sE mE eE) (dyadicTensor sL mL eL)
        (dyadicTensor sU mU eU) V d m j t else 2 ^ (eE + eL + eU) * (DZ rows m j t : ℚ))) a := by
    intro l hl
    induction l with
    | nil => intro a; rfl
    | cons t l ih =>
      intro a
      simp only [List.foldl_cons, hl t List.mem_cons_self, ↓reduceIte]
      exact ih (fun u hu => hl u (List.mem_cons_of_mem _ hu)) _
  rw [hD m hm, hcongr (List.range m) (fun t ht => by have := List.mem_range.mp ht; omega), hfold]
  rw [decide_eq_decide]
  constructor
  · intro h
    have : (0 : ℚ) < 2 ^ (eE + eL + eU) * ((DZ rows m j m + ((k - 1 : ℕ) : ℤ) *
        (List.range m).foldl (fun x t => min x (DZ rows m j t)) (DZ rows m j m) : ℤ) : ℚ) := by
      push_cast; linarith
    exact_mod_cast (pos_of_mul_pos_right this hc.le)
  · intro h
    have h' : (0 : ℚ) < ((DZ rows m j m + ((k - 1 : ℕ) : ℤ) *
        (List.range m).foldl (fun x t => min x (DZ rows m j t)) (DZ rows m j m) : ℤ) : ℚ) := by
      exact_mod_cast h
    have := mul_pos hc h'
    push_cast at this; linarith

/-- On a table of the rows of `MZ`, a group's tests have the same outcome as on `M`. -/
theorem groupOk_eq (hrows : ∀ j < V, rows.getD j [] = rowZ mE mL mU V d j) {k m : ℕ} (hm : m < V) :
    groupOk (dyadicTensor sE mE eE) (dyadicTensor sL mL eL) (dyadicTensor sU mU eU) V d k m =
      groupOkZ rows k V m := by
  unfold groupOk groupOkZ
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  refine forall₂_congr fun j hj => ?_
  rw [pairOk_eq hrows hm (List.mem_range.mp hj)]

end Bridge

open Classical in
/-- **The count from a table.** On weights given as integer mantissas with one exponent per
    tensor, with a table whose rows are the rows of `MZ`, the checker's count is `countZ` of the
    table, and its bill is `bill V d`. -/
theorem check_billed_of_table {g : Graph} {w : Weights ℚ} {d : ℕ}
    {mE mL mU : List ℤ} {eE eL eU : ℤ}
    (hE : List.lookup nE w = some (dyadicTensor [d, g.values] mE eE))
    (hL : List.lookup nL w = some (dyadicTensor [d, d] mL eL))
    (hU : List.lookup nU w = some (dyadicTensor [g.values, d] mU eU))
    (hEn : mE.length = d * g.values) (hLn : mL.length = d * d) (hUn : mU.length = g.values * d)
    {rows : List (List ℤ)} (hrows : ∀ j < g.values, rows.getD j [] = rowZ mE mL mU g.values d j)
    (c : Cert) :
    CostM.billed (check Interp.counting g (maxTask g.positions g.values)) ⟨w, c⟩ =
      some (countZ rows g.positions g.values, bill g.values d) := by
  have hw : WF w g.values d (dyadicTensor [d, g.values] mE eE) (dyadicTensor [d, d] mL eL)
      (dyadicTensor [g.values, d] mU eU) :=
    ⟨hE, rfl, by simp [dyadicTensor, hEn], hL, rfl, by simp [dyadicTensor, hLn], hU, rfl,
      by simp [dyadicTensor, hUn]⟩
  rw [(runs_check (env := ⟨w, c⟩) hw (maxTask g.positions g.values)).billed]
  congr 2
  unfold countZ
  congr 1
  refine List.map_congr_left fun m hm => ?_
  rw [groupOk_eq hrows (List.mem_range.mp hm)]

/-- An instance's count, from the outcomes `bs` of its groups' tests. -/
theorem countZ_eq {rows : List (List ℤ)} {k V : ℕ} (bs : List Bool)
    (h : ∀ m < V, groupOkZ rows k V m = bs.getD m false) :
    countZ rows k V =
      ((List.range V).map fun m =>
        cond (bs.getD m false) (Nat.pow (m + 1) k - Nat.pow m k) 0).sum := by
  unfold countZ
  congr 1
  exact List.map_congr_left fun m hm => by rw [h m (List.mem_range.mp hm)]

end LinearMaxK
