/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Matrix.Rank
import OAI.Combinatorics.Progressions.Dynamics.CandidateFrontSourceLossBudget
import OAI.Combinatorics.Progressions.Lattices.IntegerColumnMinor

namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

def rationalSolveHeight (r H : ℕ) : ℕ :=
  r.factorial * (H ^ (r * r + r)) ^ r

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exists_bounded_rational_system_solution (A : Matrix ι ι ℚ) (b : ι → ℚ)
    (hdet : A.det ≠ 0) {H : ℕ} (hA : ∀ i j, RationalHeightLE (A i j) H)
    (hb : ∀ i, RationalHeightLE (b i) H) :
    ∃ x : ι → ℚ, A *ᵥ x = b ∧
      ∀ i, RationalHeightLE (x i) (rationalSolveHeight (Fintype.card ι) H) := by
  let q : (ι × ι) ⊕ ι → ℚ := Sum.elim (fun p => A p.1 p.2) b
  have hq : ∀ u, RationalHeightLE (q u) H := by
    intro u
    cases u with
    | inl p => exact hA p.1 p.2
    | inr i => exact hb i
  obtain ⟨D, hDpos, _, a, ha, hbound⟩ := exists_bounded_integer_array q hq
  let Z : Matrix ι ι ℤ := fun i j => a (.inl (i, j))
  let c : ι → ℤ := fun i => a (.inr i)
  have hD : (D : ℚ) ≠ 0 := by exact_mod_cast hDpos.ne'
  have hZ : Z.map (Int.castRingHom ℚ) = (D : ℚ) • A := by
    ext i j
    exact ha (.inl (i, j))
  have hc : (fun i => (c i : ℚ)) = (D : ℚ) • b := by
    funext i
    exact ha (.inr i)
  have hZdet : Z.det ≠ 0 := by
    have hcast : (Z.det : ℚ) = (D : ℚ) ^ Fintype.card ι * A.det := by
      calc
        (Z.det : ℚ) = (Z.map (Int.castRingHom ℚ)).det :=
          (Int.castRingHom ℚ).map_det Z
        _ = _ := by rw [hZ, Matrix.det_smul]
    have hn := mul_ne_zero (pow_ne_zero (Fintype.card ι) hD) hdet
    rw [← hcast] at hn
    exact_mod_cast hn
  have hZA : ∀ i j, (Z i j).natAbs ≤ H ^ (Fintype.card ι * Fintype.card ι +
      Fintype.card ι) := by
    intro i j
    simpa only [Fintype.card_sum, Fintype.card_prod] using hbound (.inl (i, j))
  have hcA : ∀ i, (c i).natAbs ≤ H ^ (Fintype.card ι * Fintype.card ι +
      Fintype.card ι) := by
    intro i
    simpa only [Fintype.card_sum, Fintype.card_prod] using hbound (.inr i)
  obtain ⟨x, hx, hxH⟩ := exists_bounded_integer_system_solution Z c hZdet hZA hcA
  refine ⟨x, ?_, hxH⟩
  rw [hZ, hc, Matrix.smul_mulVec] at hx
  funext i
  have hi := congrFun hx i
  change (D : ℚ) * (A *ᵥ x) i = (D : ℚ) * b i at hi
  exact mul_left_cancel₀ hD hi

theorem rationalCramerSolution_height (A : Matrix ι ι ℚ) (b : ι → ℚ)
    (hdet : A.det ≠ 0) {H : ℕ} (hA : ∀ i j, RationalHeightLE (A i j) H)
    (hb : ∀ i, RationalHeightLE (b i) H) (i : ι) :
    RationalHeightLE (rationalCramerSolution A b i)
      (rationalSolveHeight (Fintype.card ι) H) := by
  obtain ⟨x, hx, hheight⟩ := exists_bounded_rational_system_solution A b hdet hA hb
  rw [← rationalCramerSolution_unique A b x hdet hx]
  exact hheight i

theorem rationalHeightLE_zero {H : ℕ} (hH : 1 ≤ H) : RationalHeightLE 0 H := by
  exact ⟨by simp, by simpa using hH⟩

theorem rationalHeightLE_one {H : ℕ} (hH : 1 ≤ H) : RationalHeightLE 1 H := by
  exact ⟨by simpa using hH, by simpa using hH⟩

theorem exists_bounded_rational_right_inverse (A : Matrix ι ι ℚ) (hdet : A.det ≠ 0)
    {H : ℕ} (hH : 1 ≤ H) (hA : ∀ i j, RationalHeightLE (A i j) H) :
    ∃ B : Matrix ι ι ℚ, A * B = 1 ∧
      ∀ i j, RationalHeightLE (B i j) (rationalSolveHeight (Fintype.card ι) H) := by
  let B : Matrix ι ι ℚ := fun i j => rationalCramerSolution A (Pi.single j 1) i
  refine ⟨B, ?_, ?_⟩
  · ext i j
    have h := congrFun (rationalCramerSolution_solves A (Pi.single j 1) hdet) i
    change (A *ᵥ rationalCramerSolution A (Pi.single j 1)) i = (1 : Matrix ι ι ℚ) i j
    simpa only [Pi.single_apply, Matrix.one_apply, eq_comm] using h
  · intro i j
    apply rationalCramerSolution_height A (Pi.single j 1) hdet hA
    intro k
    by_cases hkj : k = j
    · simpa [Pi.single_apply, hkj] using rationalHeightLE_one hH
    · simpa [Pi.single_apply, hkj, Ne.symm hkj] using rationalHeightLE_zero hH

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix

theorem RationalHeightLE.neg {q : ℚ} {H : ℕ} (hq : RationalHeightLE q H) :
    RationalHeightLE (-q) H := by
  simpa only [RationalHeightLE, Rat.neg_num, Rat.neg_den, Int.natAbs_neg] using hq

theorem RationalHeightLE.mul {q r : ℚ} {H K : ℕ}
    (hq : RationalHeightLE q H) (hr : RationalHeightLE r K) :
    RationalHeightLE (q * r) (H * K) := by
  have hd : (q.den : ℤ) * r.den ≠ 0 := by
    exact mul_ne_zero (by exact_mod_cast q.den_ne_zero) (by exact_mod_cast r.den_ne_zero)
  have heq : q * r = ((q.num * r.num : ℤ) : ℚ) / ((q.den : ℤ) * r.den : ℤ) := by
    push_cast
    rw [mul_div_mul_comm, Rat.num_div_den, Rat.num_div_den]
  rw [heq]
  apply rationalHeightLE_fraction _ _ hd
  · simpa only [Int.natAbs_mul] using Nat.mul_le_mul hq.1 hr.1
  · simpa only [Int.natAbs_mul, Int.natAbs_natCast] using Nat.mul_le_mul hq.2 hr.2

theorem RationalHeightLE.add {q r : ℚ} {H K : ℕ}
    (hq : RationalHeightLE q H) (hr : RationalHeightLE r K) :
    RationalHeightLE (q + r) (2 * H * K) := by
  have hqd : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have hrd : (r.den : ℚ) ≠ 0 := by exact_mod_cast r.den_ne_zero
  have hd : (q.den : ℤ) * r.den ≠ 0 := by
    exact_mod_cast mul_ne_zero hqd hrd
  have heq : q + r = ((q.num * r.den + (q.den : ℤ) * r.num : ℤ) : ℚ) /
      ((q.den : ℤ) * r.den : ℤ) := by
    calc
      q + r = (q.num : ℚ) / q.den + (r.num : ℚ) / r.den :=
        congrArg₂ (· + ·) q.num_div_den.symm r.num_div_den.symm
      _ = _ := by push_cast; exact div_add_div _ _ hqd hrd
  rw [heq]
  apply rationalHeightLE_fraction _ _ hd
  · calc
      _ ≤ (q.num * r.den).natAbs + ((q.den : ℤ) * r.num).natAbs :=
        Int.natAbs_add_le _ _
      _ ≤ H * K + H * K := by
        simp only [Int.natAbs_mul, Int.natAbs_natCast]
        exact Nat.add_le_add (Nat.mul_le_mul hq.1 hr.2) (Nat.mul_le_mul hq.2 hr.1)
      _ = _ := by ring
  · calc
      _ = q.den * r.den := by simp only [Int.natAbs_mul, Int.natAbs_natCast]
      _ ≤ H * K := Nat.mul_le_mul hq.2 hr.2
      _ ≤ 2 * H * K := by
        simpa only [mul_assoc] using Nat.le_mul_of_pos_left (H * K) (by decide : 0 < 2)

theorem RationalHeightLE.sub {q r : ℚ} {H K : ℕ}
    (hq : RationalHeightLE q H) (hr : RationalHeightLE r K) :
    RationalHeightLE (q - r) (2 * H * K) := by
  simpa only [sub_eq_add_neg] using hq.add hr.neg

theorem rationalHeightLE_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℚ) {H : ℕ} (hq : ∀ i, RationalHeightLE (q i) H) :
    RationalHeightLE (∑ i, q i) ((Fintype.card ι + 1) * H ^ Fintype.card ι) := by
  obtain ⟨D, hDpos, hD, a, ha, hbound⟩ := exists_bounded_integer_array q hq
  have hsum : ((∑ i, a i : ℤ) : ℚ) = (D : ℚ) * ∑ i, q i := by
    push_cast
    simp_rw [ha]
    rw [Finset.mul_sum]
  have heq : (∑ i, q i) = ((∑ i, a i : ℤ) : ℚ) / (D : ℤ) := by
    apply (eq_div_iff (by exact_mod_cast hDpos.ne')).mpr
    simpa only [Int.cast_natCast, mul_comm] using hsum.symm
  rw [heq]
  apply rationalHeightLE_fraction _ _ (by exact_mod_cast hDpos.ne')
  · calc
      _ ≤ ∑ i, (a i).natAbs := Int.natAbs_sum_le _ _
      _ ≤ ∑ _ : ι, H ^ Fintype.card ι := Finset.sum_le_sum fun i _ => hbound i
      _ = Fintype.card ι * H ^ Fintype.card ι := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.le_succ _)
  · simp only [Int.natAbs_natCast]
    exact hD.trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos _))

theorem rationalHeightLE_matrix_mul {ι κ ν : Type*}
    [Fintype κ] [DecidableEq κ] (A : Matrix ι κ ℚ) (B : Matrix κ ν ℚ)
    {H K : ℕ} (hA : ∀ i j, RationalHeightLE (A i j) H)
    (hB : ∀ i j, RationalHeightLE (B i j) K) (i : ι) (j : ν) :
    RationalHeightLE ((A * B) i j) ((Fintype.card κ + 1) * (H * K) ^ Fintype.card κ) :=
  rationalHeightLE_sum (fun k => A i k * B k j) (fun k => (hA i k).mul (hB k j))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [DecidableEq κ] in

theorem exists_nonsingular_columns (A : Matrix ι κ ℚ)
    (hA : Function.Surjective A.mulVec) :
    ∃ c : ι → κ, Function.Injective c ∧ (A.submatrix id c).det ≠ 0 := by
  classical
  have hspan : Submodule.span ℚ (Set.range A.col) = ⊤ := by
    rw [← Matrix.range_mulVecLin, LinearMap.range_eq_top]
    exact hA
  have hex := Submodule.exists_fun_fin_finrank_span_eq ℚ (Set.range A.col)
  rw [hspan, finrank_top, Module.finrank_pi] at hex
  obtain ⟨v, hv, _, hli⟩ := hex
  choose f hf using hv
  let e := Fintype.equivFin ι
  let c : ι → κ := fun i => f (e i)
  have hcol : (A.submatrix id c).col = fun i => v (e i) := by
    funext i
    exact hf (e i)
  have hcols : LinearIndependent ℚ (A.submatrix id c).col := by
    rw [hcol]
    exact hli.comp e e.injective
  refine ⟨c, ?_, ?_⟩
  · intro i j hij
    apply hcols.injective
    change A.col (c i) = A.col (c j)
    rw [hij]
  · exact (isUnit_iff_ne_zero.mp
      ((A.submatrix id c).isUnit_iff_isUnit_det.mp
        (Matrix.linearIndependent_cols_iff_isUnit.mp hcols)))

def extendRows (c : ι → κ) (B : Matrix ι ι ℚ) : Matrix κ ι ℚ :=
  fun k j => ∑ i, if c i = k then B i j else 0

omit [Fintype κ] in
theorem extendRows_apply (c : ι → κ) (hc : Function.Injective c)
    (B : Matrix ι ι ℚ) (i j : ι) : extendRows c B (c i) j = B i j := by
  simp only [extendRows, hc.eq_iff]
  simp

omit [DecidableEq ι] [Fintype κ] in
theorem extendRows_apply_of_not_mem (c : ι → κ) (B : Matrix ι ι ℚ)
    (k : κ) (hk : k ∉ Set.range c) (j : ι) : extendRows c B k j = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  exact ite_eq_right (fun h => hk ⟨i, h⟩)

omit [DecidableEq ι] in
theorem mul_extendRows (A : Matrix ι κ ℚ) (c : ι → κ) (B : Matrix ι ι ℚ) :
    A * extendRows c B = A.submatrix id c * B := by
  ext r j
  change (∑ k, A r k * ∑ i, if c i = k then B i j else 0) =
    ∑ i, A r (c i) * B i j
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [mul_ite, mul_zero]
  simp

theorem rationalSolveHeight_pos (r : ℕ) {H : ℕ} (hH : 1 ≤ H) :
    0 < rationalSolveHeight r H := by
  have hHpos : 0 < H := Nat.zero_lt_one.trans_le hH
  unfold rationalSolveHeight
  positivity

theorem exists_bounded_rational_section (A : Matrix ι κ ℚ)
    (hsurj : Function.Surjective A.mulVec) {H : ℕ} (hH : 1 ≤ H)
    (hA : ∀ i j, RationalHeightLE (A i j) H) :
    ∃ S : Matrix κ ι ℚ, A * S = 1 ∧
      ∀ i j, RationalHeightLE (S i j) (rationalSolveHeight (Fintype.card ι) H) := by
  obtain ⟨c, hc, hdet⟩ := exists_nonsingular_columns A hsurj
  obtain ⟨B, hB, hBH⟩ := exists_bounded_rational_right_inverse (A.submatrix id c) hdet
    hH (fun i j => hA i (c j))
  refine ⟨extendRows c B, ?_, ?_⟩
  · rw [mul_extendRows, hB]
  · intro k j
    by_cases hk : k ∈ Set.range c
    · obtain ⟨i, rfl⟩ := hk
      rw [extendRows_apply c hc]
      exact hBH i j
    · rw [extendRows_apply_of_not_mem c B k hk]
      exact rationalHeightLE_zero (rationalSolveHeight_pos _ hH)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem rationalHeightLE_prod {ι : Type*} (s : Finset ι) (q : ι → ℚ) (H : ι → ℕ)
    (hq : ∀ i ∈ s, RationalHeightLE (q i) (H i)) :
    RationalHeightLE (∏ i ∈ s, q i) (∏ i ∈ s, H i) := by
  classical
  revert hq
  induction s using Finset.induction_on with
  | empty =>
    intro _
    simpa only [Finset.prod_empty] using rationalHeightLE_one (by decide : 1 ≤ 1)
  | @insert i s hi ih =>
    intro hq
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact (hq i (Finset.mem_insert_self i s)).mul
      (ih fun j hj => hq j (Finset.mem_insert_of_mem hj))

theorem rational_product_exp_height {ι : Type*} (s : Finset ι) (q : ι → ℚ) (H : ι → ℕ)
    (hq : ∀ i ∈ s, RationalHeightLE (q i) (H i))
    {p : ℝ} (hp : 0 ≤ p) (a c : ℕ)
    (hH : ∀ i ∈ s, (H i : ℝ) ≤ Real.exp ((p + 2) ^ a))
    (hcard : (s.card : ℝ) ≤ (p + 2) ^ c) :
    ((∏ i ∈ s, q i).num.natAbs : ℝ) ≤ Real.exp ((p + 2) ^ (a + c)) ∧
      ((∏ i ∈ s, q i).den : ℝ) ≤ Real.exp ((p + 2) ^ (a + c)) := by
  have hheight := rationalHeightLE_prod s q H hq
  have hprod : ((∏ i ∈ s, H i : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ (a + c)) := by
    simpa only [Nat.cast_prod] using
      product_exponential_budget s (fun i => (H i : ℝ)) hp a c (fun _ _ => Nat.cast_nonneg _) hH hcard
  constructor
  · exact (show ((∏ i ∈ s, q i).num.natAbs : ℝ) ≤ (∏ i ∈ s, H i : ℕ) from
      by exact_mod_cast hheight.1).trans hprod
  · exact (show ((∏ i ∈ s, q i).den : ℝ) ≤ (∏ i ∈ s, H i : ℕ) from
      by exact_mod_cast hheight.2).trans hprod

theorem rational_sum_cost_le_exp (m H : ℕ) {p : ℝ} (hp : 0 ≤ p) (a c : ℕ)
    (hH : (H : ℝ) ≤ Real.exp ((p + 2) ^ a)) (hm : (m : ℝ) ≤ (p + 2) ^ c) :
    (((m + 1) * H ^ m : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ (a + c + 1)) := by
  have hpower := pow_le_pow_left₀ (Nat.cast_nonneg H) hH m
  rw [← Real.exp_nat_mul] at hpower
  have hone : 1 + (p + 2) ^ a ≤ (p + 2) ^ (a + 1) := by
    have ha : (1 : ℝ) ≤ (p + 2) ^ a := one_le_pow₀ (by linarith)
    calc
      _ ≤ 2 * (p + 2) ^ a := by linarith
      _ ≤ (p + 2) * (p + 2) ^ a :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by rw [pow_succ]; ring
  push_cast
  calc
    _ ≤ Real.exp m * Real.exp ((m : ℝ) * (p + 2) ^ a) :=
      mul_le_mul (Real.add_one_le_exp m) hpower (by positivity) (by positivity)
    _ = Real.exp ((m : ℝ) * (1 + (p + 2) ^ a)) := by
      rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp ((p + 2) ^ c * (p + 2) ^ (a + 1)) :=
      Real.exp_le_exp.mpr (mul_le_mul hm hone (by positivity) (by positivity))
    _ = _ := by rw [← pow_add]; congr 2; omega

theorem rational_sum_exp_height {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℚ) {H : ℕ} (hq : ∀ i, RationalHeightLE (q i) H)
    {p : ℝ} (hp : 0 ≤ p) (a c : ℕ)
    (hH : (H : ℝ) ≤ Real.exp ((p + 2) ^ a))
    (hcard : (Fintype.card ι : ℝ) ≤ (p + 2) ^ c) :
    ((∑ i, q i).num.natAbs : ℝ) ≤ Real.exp ((p + 2) ^ (a + c + 1)) ∧
      ((∑ i, q i).den : ℝ) ≤ Real.exp ((p + 2) ^ (a + c + 1)) := by
  have hheight := rationalHeightLE_sum q hq
  have hcost := rational_sum_cost_le_exp (Fintype.card ι) H hp a c hH hcard
  constructor
  · exact (show ((∑ i, q i).num.natAbs : ℝ) ≤ ((Fintype.card ι + 1) * H ^ Fintype.card ι : ℕ) from
      by exact_mod_cast hheight.1).trans hcost
  · exact (show ((∑ i, q i).den : ℝ) ≤ ((Fintype.card ι + 1) * H ^ Fintype.card ι : ℕ) from
      by exact_mod_cast hheight.2).trans hcost

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

omit [Fintype ι] in

theorem mulVec_eq_zero_iff_row_span (A : Matrix ι κ ℚ) (x : κ → ℚ) :
    A *ᵥ x = 0 ↔ ∀ v ∈ Submodule.span ℚ (Set.range A.row), v ⬝ᵥ x = 0 := by
  constructor
  · intro hx v hv
    induction hv using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact congrFun hx i
    | zero => exact zero_dotProduct x
    | add y z _ _ hy hz => rw [add_dotProduct, hy, hz, add_zero]
    | smul a y _ hy => rw [smul_dotProduct, hy, smul_zero]
  · intro hx
    funext i
    exact hx (A.row i) (Submodule.subset_span ⟨i, rfl⟩)

theorem mulVec_surjective_of_independent_rows (A : Matrix ι κ ℚ)
    (hA : LinearIndependent ℚ A.row) : Function.Surjective A.mulVec := by
  change Function.Surjective A.mulVecLin
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_finrank_eq
  change A.rank = Module.finrank ℚ (ι → ℚ)
  rw [hA.rank_matrix, Module.finrank_pi]

theorem exists_independent_defining_rows (A : Matrix ι κ ℚ) :
    ∃ r : ℕ, r ≤ Fintype.card ι ∧ ∃ rows : Fin r → ι,
      Function.Injective rows ∧ Function.Surjective (A.submatrix rows id).mulVec ∧
      LinearMap.ker (A.submatrix rows id).mulVecLin = LinearMap.ker A.mulVecLin := by
  classical
  let r := Module.finrank ℚ (Submodule.span ℚ (Set.range A.row))
  obtain ⟨v, hv, hspan, hli⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq ℚ (Set.range A.row)
  choose rows hrows using hv
  have hrow : (A.submatrix rows id).row = v := by
    funext i
    exact hrows i
  have hind : LinearIndependent ℚ (A.submatrix rows id).row := by
    rw [hrow]
    exact hli
  refine ⟨r, ?_, rows, ?_, mulVec_surjective_of_independent_rows _ hind, ?_⟩
  · change Module.finrank ℚ (Submodule.span ℚ (Set.range A.row)) ≤ Fintype.card ι
    rw [← A.rank_eq_finrank_span_row]
    exact A.rank_le_card_height
  · intro i j hij
    apply hind.injective
    change A.row (rows i) = A.row (rows j)
    rw [hij]
  · ext x
    change (A.submatrix rows id) *ᵥ x = 0 ↔ A *ᵥ x = 0
    rw [mulVec_eq_zero_iff_row_span, mulVec_eq_zero_iff_row_span, hrow, hspan]

end Erdos3

end

end OAI
