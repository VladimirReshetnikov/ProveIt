import Diophantine.Paper1982.EnumerationQuadratic

/-!
# Gate circuits over natural-number coordinates

The coefficient coding of the 99-operation system starts from a
"compiled circuit": a finite list of primitive rows

* `X i + X j = X k`, `X i * X j = X k`, `X i = X j`, `X i = 0`, `X i = 1`

over nonnegative integer coordinates, one of which is the input.  This module
defines such circuits and shows that every Diophantine set is accepted, on
positive inputs, by one of them.  The source is the existing finite integer
gate system `Jones1982.EnumerationQuadratic.GateSys` for the 1978 enumeration
`W n`; each integer node value is represented as a difference `p − m` of two
natural coordinates, computed gate by gate (`pm`), so that additions and
multiplications of integers become additions and multiplications of naturals.
-/

namespace Jones1980
namespace Gates

open Jones1978 (K L K_le L_le)
open Jones1982.EnumerationQuadratic

/-- A primitive row over the coordinates `Fin m`. -/
inductive Row (m : ℕ)
  | add (i j k : Fin m)
  | mul (i j k : Fin m)
  | eq (i j : Fin m)
  | zero (i : Fin m)
  | one (i : Fin m)

/-- The condition expressed by a row at the assignment `X`. -/
def Row.Holds {m : ℕ} (X : Fin m → ℕ) : Row m → Prop
  | .add i j k => X i + X j = X k
  | .mul i j k => X i * X j = X k
  | .eq i j => X i = X j
  | .zero i => X i = 0
  | .one i => X i = 1

/-- A circuit: `m` coordinates, one of them the input, and a list of rows. -/
structure Circuit where
  m : ℕ
  inp : Fin m
  rows : List (Row m)

/-- `C` accepts `x`: some nonnegative assignment with input `x` satisfies every row. -/
def Circuit.Accepts (C : Circuit) (x : ℕ) : Prop :=
  ∃ X : Fin C.m → ℕ, X C.inp = x ∧ ∀ ρ ∈ C.rows, ρ.Holds X

/-! ### The pair representation of the enumeration nodes -/

/-- Natural pair `(p, m)` with `p − m` equal to the node value `t k`, computed
gate by gate: variables split by sign, additions and multiplications of pairs. -/
def pm (t : ℕ → ℤ) : ℕ → ℕ × ℕ
  | k =>
    if h0 : k = 0 then (0, 0)
    else if k % 3 = 2 then ((t k).toNat, (-t k).toNat)
    else if h3 : k % 3 = 0 then
      have hK : K (k / 3) < k := by have := K_le (k / 3); omega
      have hL : L (k / 3) < k := by have := L_le (k / 3); omega
      ((pm t (K (k / 3))).1 + (pm t (L (k / 3))).1, (pm t (K (k / 3))).2 + (pm t (L (k / 3))).2)
    else
      have hK : K (k / 3) < k := by have := K_le (k / 3); omega
      have hL : L (k / 3) < k := by have := L_le (k / 3); omega
      ((pm t (K (k / 3))).1 * (pm t (L (k / 3))).1 + (pm t (K (k / 3))).2 * (pm t (L (k / 3))).2,
       (pm t (K (k / 3))).1 * (pm t (L (k / 3))).2 + (pm t (K (k / 3))).2 * (pm t (L (k / 3))).1)
termination_by k => k

theorem pm_zero (t : ℕ → ℤ) : pm t 0 = (0, 0) := by rw [pm]; simp

theorem pm_var (t : ℕ → ℤ) (i : ℕ) :
    pm t (3 * i + 2) = ((t (3 * i + 2)).toNat, (-t (3 * i + 2)).toNat) := by
  rw [pm]; simp [Nat.add_mod, Nat.mul_mod_right]

theorem pm_add (t : ℕ → ℤ) {i : ℕ} (hi : 1 ≤ i) :
    pm t (3 * i) = ((pm t (K i)).1 + (pm t (L i)).1, (pm t (K i)).2 + (pm t (L i)).2) := by
  rw [pm]
  have h0 : 3 * i ≠ 0 := by omega
  simp [h0, Nat.mul_mod_right]

theorem pm_mul (t : ℕ → ℤ) (i : ℕ) :
    pm t (3 * i + 1) =
      ((pm t (K i)).1 * (pm t (L i)).1 + (pm t (K i)).2 * (pm t (L i)).2,
       (pm t (K i)).1 * (pm t (L i)).2 + (pm t (K i)).2 * (pm t (L i)).1) := by
  rw [pm]
  have h1 : (3 * i + 1) % 3 = 1 := by omega
  have h2 : (3 * i + 1) / 3 = i := by omega
  simp [h1, h2]

/-- Under the gate equations, the pair at every node represents the node value. -/
theorem pm_diff {n x : ℕ} {t : GateIndex n → ℤ} (h : GateSys n x t) :
    ∀ k, k < 3 * (n + 1) → ((pm (extend t) k).1 : ℤ) - (pm (extend t) k).2 = extend t k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases Nat.lt_or_ge k 1 with h0 | h1
    · have : k = 0 := by omega
      subst this
      rw [pm_zero]
      have hz := h.zero
      rw [← extend_at t (nodeZero n)] at hz
      simpa [nodeZero] using hz.symm
    · obtain ⟨i, r, hr, rfl⟩ : ∃ i r, r < 3 ∧ k = 3 * i + r :=
        ⟨k / 3, k % 3, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod k 3).symm⟩
      have hi : i < n + 1 := by omega
      have hK : K i < 3 * (n + 1) := lt_of_le_of_lt (K_le i) (by omega)
      have hL : L i < 3 * (n + 1) := lt_of_le_of_lt (L_le i) (by omega)
      have hKlt : K i < 3 * i + r := by have := K_le i; omega
      have hLlt : L i < 3 * i + r := by have := L_le i; omega
      have ihK := ih (K i) hKlt hK
      have ihL := ih (L i) hLlt hL
      let j : Fin (n + 1) := ⟨i, hi⟩
      interval_cases r
      · -- addition gate
        have hi1 : 1 ≤ i := by omega
        have e0 : 3 * i + 0 = 3 * i := rfl
        rw [e0, pm_add _ hi1]
        have ha := h.add j
        rw [← extend_at t (nodeAdd n j), ← extend_at t (nodeLeft n j),
          ← extend_at t (nodeRight n j)] at ha
        simp only [nodeAdd, nodeLeft, nodeRight, j] at ha
        push_cast
        rw [ha]; linarith
      · -- multiplication gate
        rw [pm_mul]
        have hm := h.mul j
        rw [← extend_at t (nodeMul n j), ← extend_at t (nodeLeft n j),
          ← extend_at t (nodeRight n j)] at hm
        simp only [nodeMul, nodeLeft, nodeRight, j] at hm
        push_cast
        rw [hm, ← ihK, ← ihL]; ring
      · -- variable
        rw [pm_var]
        push_cast
        by_cases hpos : 0 ≤ extend t (3 * i + 2)
        · rw [Int.toNat_of_nonneg hpos, Int.toNat_eq_zero.mpr (by linarith)]; simp
        · have hneg : extend t (3 * i + 2) < 0 := lt_of_not_ge hpos
          rw [Int.toNat_eq_zero.mpr hneg.le, Int.toNat_of_nonneg (by linarith)]; simp

/-! ### The compiled circuit -/

/-- Number of coordinates: the input, six per node, and three output auxiliaries. -/
def size (n : ℕ) : ℕ := 1 + 6 * (3 * (n + 1)) + 3

/-- Coordinate of the input. -/
def inp (n : ℕ) : Fin (size n) := ⟨0, by unfold size; omega⟩

/-- Coordinate of slot `sl < 6` of node `g < 3(n+1)`: `1 + 6g + sl`. -/
def slot (n : ℕ) (g sl : ℕ) (hg : g < 3 * (n + 1)) (hs : sl < 6) : Fin (size n) :=
  ⟨1 + 6 * g + sl, by unfold size; omega⟩

/-- The three output auxiliaries. -/
def out (n : ℕ) (u : ℕ) (hu : u < 3) : Fin (size n) :=
  ⟨1 + 6 * (3 * (n + 1)) + u, by unfold size; omega⟩

theorem K_lt (n : ℕ) {i : ℕ} (hi : i < n + 1) : K i < 3 * (n + 1) :=
  lt_of_le_of_lt (K_le i) (by omega)

theorem L_lt (n : ℕ) {i : ℕ} (hi : i < n + 1) : L i < 3 * (n + 1) :=
  lt_of_le_of_lt (L_le i) (by omega)

/-- Pair coordinates of node `g`: `pc` the positive part, `mc` the negative part. -/
def pc (n : ℕ) (g : ℕ) (hg : g < 3 * (n + 1)) : Fin (size n) := slot n g 0 hg (by omega)
def mc (n : ℕ) (g : ℕ) (hg : g < 3 * (n + 1)) : Fin (size n) := slot n g 1 hg (by omega)

/-- Temporaries of the multiplication gate `3i + 1`. -/
def tm (n : ℕ) (i : Fin (n + 1)) (sl : ℕ) (hs : sl < 6) : Fin (size n) :=
  slot n (3 * i + 1) sl (by omega) hs

/-! The rows, named so that membership proofs are syntactic. -/

def rowZ0 (n : ℕ) : Row (size n) := .zero (pc n 0 (by omega))
def rowZ1 (n : ℕ) : Row (size n) := .zero (mc n 0 (by omega))
def rowO0 (n : ℕ) : Row (size n) :=
  .add (pc n (K n) (K_lt n (by omega))) (mc n (L n) (L_lt n (by omega))) (out n 0 (by omega))
def rowO1 (n : ℕ) : Row (size n) :=
  .add (pc n (L n) (L_lt n (by omega))) (mc n (K n) (K_lt n (by omega))) (out n 1 (by omega))
def rowO2 (n : ℕ) : Row (size n) := .add (out n 1 (by omega)) (inp n) (out n 2 (by omega))
def rowO3 (n : ℕ) : Row (size n) := .eq (out n 0 (by omega)) (out n 2 (by omega))

def rowA0 (n : ℕ) (i : Fin (n + 1)) : Row (size n) :=
  .add (pc n (K i) (K_lt n i.isLt)) (pc n (L i) (L_lt n i.isLt)) (pc n (3 * i) (by omega))
def rowA1 (n : ℕ) (i : Fin (n + 1)) : Row (size n) :=
  .add (mc n (K i) (K_lt n i.isLt)) (mc n (L i) (L_lt n i.isLt)) (mc n (3 * i) (by omega))
def rowM0 (n : ℕ) (i : Fin (n + 1)) : Row (size n) :=
  .mul (pc n (K i) (K_lt n i.isLt)) (pc n (L i) (L_lt n i.isLt)) (tm n i 2 (by omega))
def rowM1 (n : ℕ) (i : Fin (n + 1)) : Row (size n) :=
  .mul (mc n (K i) (K_lt n i.isLt)) (mc n (L i) (L_lt n i.isLt)) (tm n i 3 (by omega))
def rowM2 (n : ℕ) (i : Fin (n + 1)) : Row (size n) :=
  .add (tm n i 2 (by omega)) (tm n i 3 (by omega)) (pc n (3 * i + 1) (by omega))
def rowM3 (n : ℕ) (i : Fin (n + 1)) : Row (size n) :=
  .mul (pc n (K i) (K_lt n i.isLt)) (mc n (L i) (L_lt n i.isLt)) (tm n i 4 (by omega))
def rowM4 (n : ℕ) (i : Fin (n + 1)) : Row (size n) :=
  .mul (mc n (K i) (K_lt n i.isLt)) (pc n (L i) (L_lt n i.isLt)) (tm n i 5 (by omega))
def rowM5 (n : ℕ) (i : Fin (n + 1)) : Row (size n) :=
  .add (tm n i 4 (by omega)) (tm n i 5 (by omega)) (mc n (3 * i + 1) (by omega))

/-- The rows of one node index `i ≤ n`: the addition gate `3i` and the multiplication
gate `3i + 1`, both reading the pairs at `K i` and `L i`. -/
def nodeRows (n : ℕ) (i : Fin (n + 1)) : List (Row (size n)) :=
  [rowA0 n i, rowA1 n i, rowM0 n i, rowM1 n i, rowM2 n i, rowM3 n i, rowM4 n i, rowM5 n i]

/-- The zero node and the output equation `t(K n) = t(L n) + x`, i.e.
`p_K + m_L = p_L + m_K + x`. -/
def fixedRows (n : ℕ) : List (Row (size n)) :=
  [rowZ0 n, rowZ1 n, rowO0 n, rowO1 n, rowO2 n, rowO3 n]

/-- The compiled circuit of the enumeration index `n`. -/
def compiled (n : ℕ) : Circuit :=
  ⟨size n, inp n, fixedRows n ++ (List.finRange (n + 1)).flatMap (nodeRows n)⟩

theorem mem_compiled_rows (n : ℕ) (ρ : Row (size n)) :
    ρ ∈ fixedRows n ++ (List.finRange (n + 1)).flatMap (nodeRows n) ↔
      ρ ∈ fixedRows n ∨ ∃ i : Fin (n + 1), ρ ∈ nodeRows n i := by
  rw [List.mem_append, List.mem_flatMap]
  simp only [List.mem_finRange, true_and]

/-- The assignment built from an integer node function. -/
def assign (n x : ℕ) (t : ℕ → ℤ) (idx : Fin (size n)) : ℕ :=
  if idx.val = 0 then x
  else if idx.val ≤ 6 * (3 * (n + 1)) then
    let g := (idx.val - 1) / 6
    let sl := (idx.val - 1) % 6
    if sl = 0 then (pm t g).1
    else if sl = 1 then (pm t g).2
    else if sl = 2 then (pm t (K (g / 3))).1 * (pm t (L (g / 3))).1
    else if sl = 3 then (pm t (K (g / 3))).2 * (pm t (L (g / 3))).2
    else if sl = 4 then (pm t (K (g / 3))).1 * (pm t (L (g / 3))).2
    else (pm t (K (g / 3))).2 * (pm t (L (g / 3))).1
  else if idx.val = 6 * (3 * (n + 1)) + 1 then (pm t (K n)).1 + (pm t (L n)).2
  else if idx.val = 6 * (3 * (n + 1)) + 2 then (pm t (L n)).1 + (pm t (K n)).2
  else (pm t (L n)).1 + (pm t (K n)).2 + x

theorem assign_inp (n x : ℕ) (t : ℕ → ℤ) : assign n x t (inp n) = x := by
  simp [assign, inp]

theorem assign_slot (n x : ℕ) (t : ℕ → ℤ) (g sl : ℕ) (hg : g < 3 * (n + 1)) (hs : sl < 6) :
    assign n x t (slot n g sl hg hs) =
      if sl = 0 then (pm t g).1
      else if sl = 1 then (pm t g).2
      else if sl = 2 then (pm t (K (g / 3))).1 * (pm t (L (g / 3))).1
      else if sl = 3 then (pm t (K (g / 3))).2 * (pm t (L (g / 3))).2
      else if sl = 4 then (pm t (K (g / 3))).1 * (pm t (L (g / 3))).2
      else (pm t (K (g / 3))).2 * (pm t (L (g / 3))).1 := by
  have h1 : 1 + 6 * g + sl ≠ 0 := by omega
  have h2 : 1 + 6 * g + sl ≤ 6 * (3 * (n + 1)) := by omega
  have h3 : (1 + 6 * g + sl - 1) / 6 = g := by omega
  have h4 : (1 + 6 * g + sl - 1) % 6 = sl := by omega
  simp only [assign, slot, h1, h2, h3, h4, if_false, if_true]

theorem assign_pc (n x : ℕ) (t : ℕ → ℤ) (g : ℕ) (hg : g < 3 * (n + 1)) :
    assign n x t (pc n g hg) = (pm t g).1 := by
  rw [pc, assign_slot]; simp

theorem assign_mc (n x : ℕ) (t : ℕ → ℤ) (g : ℕ) (hg : g < 3 * (n + 1)) :
    assign n x t (mc n g hg) = (pm t g).2 := by
  rw [mc, assign_slot]; simp

theorem assign_tm (n x : ℕ) (t : ℕ → ℤ) (i : Fin (n + 1)) (sl : ℕ) (hs : sl < 6) :
    assign n x t (tm n i sl hs) =
      if sl = 0 then (pm t (3 * i + 1)).1
      else if sl = 1 then (pm t (3 * i + 1)).2
      else if sl = 2 then (pm t (K i)).1 * (pm t (L i)).1
      else if sl = 3 then (pm t (K i)).2 * (pm t (L i)).2
      else if sl = 4 then (pm t (K i)).1 * (pm t (L i)).2
      else (pm t (K i)).2 * (pm t (L i)).1 := by
  rw [tm, assign_slot]
  have hdiv : (3 * i.val + 1) / 3 = i.val := by omega
  rw [hdiv]

theorem assign_out0 (n x : ℕ) (t : ℕ → ℤ) :
    assign n x t (out n 0 (by omega)) = (pm t (K n)).1 + (pm t (L n)).2 := by
  simp only [assign, out]
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]

theorem assign_out1 (n x : ℕ) (t : ℕ → ℤ) :
    assign n x t (out n 1 (by omega)) = (pm t (L n)).1 + (pm t (K n)).2 := by
  simp only [assign, out]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]

theorem assign_out2 (n x : ℕ) (t : ℕ → ℤ) :
    assign n x t (out n 2 (by omega)) = (pm t (L n)).1 + (pm t (K n)).2 + x := by
  simp only [assign, out]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-- A gate system gives an accepting assignment of the compiled circuit. -/
theorem accepts_of_gateSys {n x : ℕ} {t : GateIndex n → ℤ} (h : GateSys n x t) :
    (compiled n).Accepts x := by
  refine ⟨assign n x (extend t), assign_inp n x _, ?_⟩
  intro ρ hρ
  have hρ' := (mem_compiled_rows n ρ).1 hρ
  have hd := pm_diff h
  rcases hρ' with hρ' | ⟨i, hρ'⟩
  · simp only [fixedRows, List.mem_cons, List.not_mem_nil, or_false] at hρ'
    rcases hρ' with rfl | rfl | rfl | rfl | rfl | rfl
    · simp [rowZ0, Row.Holds, assign_pc, pm_zero]
    · simp [rowZ1, Row.Holds, assign_mc, pm_zero]
    · simp only [rowO0, Row.Holds, assign_pc, assign_mc, assign_out0]
    · simp only [rowO1, Row.Holds, assign_pc, assign_mc, assign_out1]
    · simp only [rowO2, Row.Holds, assign_out1, assign_out2, assign_inp]
    · simp only [rowO3, Row.Holds, assign_out0, assign_out2]
      have ho := h.output
      rw [← extend_at t (nodeLeft n (Fin.last n)), ← extend_at t (nodeRight n (Fin.last n))] at ho
      simp only [nodeLeft, nodeRight, Fin.val_last] at ho
      have h1 := hd (K n) (K_lt n (by omega))
      have h2 := hd (L n) (L_lt n (by omega))
      have : ((pm (extend t) (K n)).1 : ℤ) + (pm (extend t) (L n)).2 =
          (pm (extend t) (L n)).1 + (pm (extend t) (K n)).2 + x := by
        linarith
      exact_mod_cast this
  · simp only [nodeRows, List.mem_cons, List.not_mem_nil, or_false] at hρ'
    rcases hρ' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp only [rowA0, Row.Holds, assign_pc]
      rcases Nat.eq_zero_or_pos i.val with h0 | hpos
      · rw [h0]; simp [pm_zero, Jones1978.K_zero, Jones1978.L_zero]
      · rw [pm_add _ hpos]
    · simp only [rowA1, Row.Holds, assign_mc]
      rcases Nat.eq_zero_or_pos i.val with h0 | hpos
      · rw [h0]; simp [pm_zero, Jones1978.K_zero, Jones1978.L_zero]
      · rw [pm_add _ hpos]
    · simp only [rowM0, Row.Holds, assign_pc, assign_tm]; simp
    · simp only [rowM1, Row.Holds, assign_mc, assign_tm]; simp
    · simp only [rowM2, Row.Holds, assign_pc, assign_tm]; simp [pm_mul]
    · simp only [rowM3, Row.Holds, assign_pc, assign_mc, assign_tm]; simp
    · simp only [rowM4, Row.Holds, assign_pc, assign_mc, assign_tm]; simp
    · simp only [rowM5, Row.Holds, assign_mc, assign_tm]; simp [pm_mul]

/-- An accepting assignment of the compiled circuit gives a gate system. -/
theorem gateSys_of_accepts {n x : ℕ} (h : (compiled n).Accepts x) :
    ∃ t : GateIndex n → ℤ, GateSys n x t := by
  obtain ⟨X, hX, hrows⟩ := h
  have hfix : ∀ ρ ∈ fixedRows n, ρ.Holds X := fun ρ hρ =>
    hrows ρ ((mem_compiled_rows n ρ).2 (Or.inl hρ))
  have hnode : ∀ (i : Fin (n + 1)), ∀ ρ ∈ nodeRows n i, ρ.Holds X := fun i ρ hρ =>
    hrows ρ ((mem_compiled_rows n ρ).2 (Or.inr ⟨i, hρ⟩))
  have hZ0 : (rowZ0 n).Holds X := hfix _ (by simp [fixedRows])
  have hZ1 : (rowZ1 n).Holds X := hfix _ (by simp [fixedRows])
  have hO0 : (rowO0 n).Holds X := hfix _ (by simp [fixedRows])
  have hO1 : (rowO1 n).Holds X := hfix _ (by simp [fixedRows])
  have hO2 : (rowO2 n).Holds X := hfix _ (by simp [fixedRows])
  have hO3 : (rowO3 n).Holds X := hfix _ (by simp [fixedRows])
  have hA0 : ∀ i, (rowA0 n i).Holds X := fun i => hnode i _ (by simp [nodeRows])
  have hA1 : ∀ i, (rowA1 n i).Holds X := fun i => hnode i _ (by simp [nodeRows])
  have hM0 : ∀ i, (rowM0 n i).Holds X := fun i => hnode i _ (by simp [nodeRows])
  have hM1 : ∀ i, (rowM1 n i).Holds X := fun i => hnode i _ (by simp [nodeRows])
  have hM2 : ∀ i, (rowM2 n i).Holds X := fun i => hnode i _ (by simp [nodeRows])
  have hM3 : ∀ i, (rowM3 n i).Holds X := fun i => hnode i _ (by simp [nodeRows])
  have hM4 : ∀ i, (rowM4 n i).Holds X := fun i => hnode i _ (by simp [nodeRows])
  have hM5 : ∀ i, (rowM5 n i).Holds X := fun i => hnode i _ (by simp [nodeRows])
  simp only [rowZ0, rowZ1, rowO0, rowO1, rowO2, rowO3, Row.Holds] at hZ0 hZ1 hO0 hO1 hO2 hO3
  simp only [rowA0, rowA1, rowM0, rowM1, rowM2, rowM3, rowM4, rowM5, Row.Holds] at hA0 hA1 hM0 hM1 hM2 hM3 hM4 hM5
  refine ⟨fun g => (X (pc n g.val g.isLt) : ℤ) - X (mc n g.val g.isLt), ?_, ?_, ?_, ?_⟩
  · simp only [nodeZero]
    rw [hZ0, hZ1]; simp
  · show (X (pc n (K n) (K_lt n (by omega))) : ℤ) - X (mc n (K n) (K_lt n (by omega))) =
      (X (pc n (L n) (L_lt n (by omega))) : ℤ) - X (mc n (L n) (L_lt n (by omega))) + (x : ℤ)
    have hX' : X (inp n) = x := hX
    rw [← hX']
    have : (X (pc n (K n) (K_lt n (by omega))) : ℤ) + X (mc n (L n) (L_lt n (by omega))) =
        X (pc n (L n) (L_lt n (by omega))) + X (mc n (K n) (K_lt n (by omega))) + X (inp n) := by
      have := hO3; rw [← hO0, ← hO2, ← hO1] at this
      exact_mod_cast this
    linarith
  · intro i
    simp only [nodeAdd, nodeLeft, nodeRight]
    rw [← hA0 i, ← hA1 i]
    push_cast; ring
  · intro i
    simp only [nodeMul, nodeLeft, nodeRight]
    rw [← hM2 i, ← hM5 i, ← hM0 i, ← hM1 i, ← hM3 i, ← hM4 i]
    push_cast; ring

/-- Every Diophantine set is accepted on positive inputs by a compiled circuit. -/
theorem exists_circuit {S : Set ℕ} (hS : Jones1978.IsDiophantine S) :
    ∃ C : Circuit, ∀ x : ℕ, 0 < x → (x ∈ S ↔ C.Accepts x) := by
  obtain ⟨n, hn⟩ := exists_gateSys_representation hS
  exact ⟨compiled n, fun x hx => (hn x hx).trans
    ⟨fun ⟨_, h⟩ => accepts_of_gateSys h, gateSys_of_accepts⟩⟩

end Gates
end Jones1980
