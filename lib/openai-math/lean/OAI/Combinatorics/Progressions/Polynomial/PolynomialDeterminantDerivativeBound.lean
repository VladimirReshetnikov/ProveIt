/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Data.Fintype.Perm
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import OAI.Combinatorics.Progressions.Estimates.BooleanCubeModeWitness
import OAI.Combinatorics.Progressions.Estimates.PaddedBooleanFeatures
import OAI.Combinatorics.Progressions.Geometry.OperatorCoordinateBound
import OAI.Combinatorics.Progressions.Polynomial.PolynomialAnalyticDerivative

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem pderiv_prod_zero {α ι : Type*} (j : α) (s : Finset ι)
    (p : ι → MvPolynomial α ℝ) (hp : ∀ i ∈ s, MvPolynomial.pderiv j (p i) = 0) :
    MvPolynomial.pderiv j (∏ i ∈ s, p i) = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, MvPolynomial.pderiv_mul, hp i (Finset.mem_insert_self i s),
      ih (fun k hk => hp k (Finset.mem_insert_of_mem hk))]
    simp

theorem pderiv_prod_one_active {α ι : Type*} [DecidableEq ι] (j : α) (s : Finset ι)
    (p : ι → MvPolynomial α ℝ) (i : ι) (hi : i ∈ s)
    (hp : ∀ k ∈ s.erase i, MvPolynomial.pderiv j (p k) = 0) :
    MvPolynomial.pderiv j (∏ k ∈ s, p k) =
      MvPolynomial.pderiv j (p i) * ∏ k ∈ s.erase i, p k := by
  rw [← Finset.mul_prod_erase s p hi, MvPolynomial.pderiv_mul, pderiv_prod_zero j _ p hp]
  simp

theorem pderiv_booleanCoefficient {α ι : Type*} [DecidableEq α]
    (j : ι) (f : Finset α → MvPolynomial ι ℝ) (s : Finset α) :
    MvPolynomial.pderiv j (booleanCoefficient f s) =
      booleanCoefficient (fun t => MvPolynomial.pderiv j (f t)) s := by
  classical
  unfold booleanCoefficient
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro t _
  have hc : (-1 : MvPolynomial ι ℝ) ^ (s \ t).card =
      MvPolynomial.C ((-1 : ℝ) ^ (s \ t).card) := by simp
  rw [hc, MvPolynomial.pderiv_C_mul]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

abbrev BlockParameter (B F α : Type*) := B × F × Option α

noncomputable def booleanAffinePolynomial {B F α : Type*} [Fintype α] [DecidableEq α]
    (b : B) (v : F) (t : Finset α) : MvPolynomial (BlockParameter B F α) ℝ :=
  ∑ r : Option α, MvPolynomial.C (booleanFeature r t : ℝ) * MvPolynomial.X (b, v, r)

def blockSpecialization {B F α : Type*} [DecidableEq α]
    (label : B → F → Option α) (z : BlockParameter B F α) : ℝ :=
  if z.2.2 = label z.1 z.2.1 then 1 else 0

theorem booleanAffinePolynomial_eval {B F α : Type*} [Fintype α] [DecidableEq α]
    (a : BlockParameter B F α → ℝ) (b : B) (v : F) (t : Finset α) :
    MvPolynomial.eval a (booleanAffinePolynomial b v t) =
      ∑ r : Option α, (booleanFeature r t : ℝ) * a (b, v, r) := by
  simp only [booleanAffinePolynomial, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]

theorem blockSpecialization_abs_le_one {B F α : Type*} [DecidableEq α]
    (label : B → F → Option α) (z : BlockParameter B F α) : |blockSpecialization label z| ≤ 1 := by
  unfold blockSpecialization
  split_ifs <;> norm_num

theorem booleanAffinePolynomial_specialization {B F α : Type*} [Fintype α] [DecidableEq α]
    (label : B → F → Option α) (b : B) (v : F) (t : Finset α) :
    MvPolynomial.eval (blockSpecialization label) (booleanAffinePolynomial b v t) =
      (booleanFeature (label b v) t : ℝ) := by
  classical
  simp only [booleanAffinePolynomial, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
    blockSpecialization, mul_ite, mul_one, mul_zero]
  simp

theorem booleanAffinePolynomial_pderiv {B F α : Type*} [Fintype α] [DecidableEq α]
    [DecidableEq B] [DecidableEq F]
    (b b₀ : B) (v v₀ : F) (r : Option α) (t : Finset α) :
    MvPolynomial.pderiv (b₀, v₀, r) (booleanAffinePolynomial b v t) =
      if b = b₀ ∧ v = v₀ then MvPolynomial.C (booleanFeature r t : ℝ) else 0 := by
  classical
  simp only [booleanAffinePolynomial, map_sum, MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_X,
    Pi.single_apply, Prod.mk.injEq, mul_ite, mul_one, mul_zero]
  by_cases hb : b = b₀ <;> by_cases hv : v = v₀
  · subst b
    subst v
    simp
  · simp [hb, hv]
  · simp [hb, hv]
  · simp [hb, hv]

theorem booleanAffinePolynomial_degreeOf_le {B F α : Type*} [Fintype α] [DecidableEq α]
    (b : B) (v : F) (t : Finset α) (j : BlockParameter B F α) :
    (booleanAffinePolynomial b v t).degreeOf j ≤ 1 := by
  classical
  unfold booleanAffinePolynomial
  apply (MvPolynomial.degreeOf_sum_le j Finset.univ _).trans
  apply Finset.sup_le
  intro r _
  apply (MvPolynomial.degreeOf_C_mul_le _ j _).trans
  simp only [MvPolynomial.degreeOf_X]
  split_ifs <;> omega

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem mvPolynomial_prod_eval_abs_le {I K : Type*} (s : Finset K)
    (p : K → MvPolynomial I ℝ) (a : I → ℝ) {L : ℝ}
    (hp : ∀ k ∈ s, |MvPolynomial.eval a (p k)| ≤ L) :
    |MvPolynomial.eval a (∏ k ∈ s, p k)| ≤ L ^ s.card := by
  rw [map_prod, Finset.abs_prod]
  calc
    _ ≤ ∏ _k ∈ s, L := Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) hp
    _ = _ := by simp

theorem mvPolynomial_prod_pderiv_eval_abs_le_of_bound {I K : Type*} (s : Finset K)
    (p : K → MvPolynomial I ℝ) (j : I) (a : I → ℝ) {L D : ℝ}
    (hL : 1 ≤ L) (hD : 0 ≤ D)
    (hp : ∀ k ∈ s, |MvPolynomial.eval a (p k)| ≤ L)
    (hd : ∀ k ∈ s, |MvPolynomial.eval a (MvPolynomial.pderiv j (p k))| ≤ D) :
    |MvPolynomial.eval a (MvPolynomial.pderiv j (∏ k ∈ s, p k))| ≤
      s.card * D * L ^ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hL0 : 0 ≤ L := zero_le_one.trans hL
    have hps : ∀ k ∈ s, |MvPolynomial.eval a (p k)| ≤ L :=
      fun k hk => hp k (Finset.mem_insert_of_mem hk)
    have hds : ∀ k ∈ s, |MvPolynomial.eval a (MvPolynomial.pderiv j (p k))| ≤ D :=
      fun k hk => hd k (Finset.mem_insert_of_mem hk)
    have hprod := mvPolynomial_prod_eval_abs_le s p a hps
    have hder := ih hps hds
    rw [Finset.prod_insert hi, MvPolynomial.pderiv_mul, map_add, map_mul, map_mul]
    calc
      _ ≤ |MvPolynomial.eval a (MvPolynomial.pderiv j (p i))| *
          |MvPolynomial.eval a (∏ k ∈ s, p k)| +
          |MvPolynomial.eval a (p i)| * |MvPolynomial.eval a (MvPolynomial.pderiv j (∏ k ∈ s, p k))| :=
        (abs_add_le _ _).trans_eq (by simp only [abs_mul])
      _ ≤ D * L ^ s.card + L * (s.card * D * L ^ s.card) :=
        add_le_add (mul_le_mul (hd i (Finset.mem_insert_self i s)) hprod (abs_nonneg _) hD)
          (mul_le_mul (hp i (Finset.mem_insert_self i s)) hder (abs_nonneg _) hL0)
      _ ≤ L * (D * L ^ s.card) + L * (s.card * D * L ^ s.card) := by
        apply add_le_add _ le_rfl
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hL (mul_nonneg hD (pow_nonneg hL0 _))
      _ = _ := by rw [Finset.card_insert_of_notMem hi, Nat.cast_add, Nat.cast_one, pow_succ]; ring

theorem mvPolynomial_prod_pderiv_eval_abs_le {I K : Type*} (s : Finset K)
    (p : K → MvPolynomial I ℝ) (j : I) (a : I → ℝ) {L : ℝ} (hL : 1 ≤ L)
    (hp : ∀ k ∈ s, |MvPolynomial.eval a (p k)| ≤ L)
    (hd : ∀ k ∈ s, |MvPolynomial.eval a (MvPolynomial.pderiv j (p k))| ≤ 1) :
    |MvPolynomial.eval a (MvPolynomial.pderiv j (∏ k ∈ s, p k))| ≤ s.card * L ^ s.card := by
  have h := mvPolynomial_prod_pderiv_eval_abs_le_of_bound s p j a hL zero_le_one hp hd
  simpa only [mul_one] using h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem polynomial_det_pderiv_eval_abs_le {I O : Type*} [Fintype O] [DecidableEq O]
    (M : Matrix O O (MvPolynomial I ℝ)) (a : I → ℝ) (j : I) {L D : ℝ}
    (hL : 1 ≤ L) (hD : 0 ≤ D)
    (hM : ∀ row col, |MvPolynomial.eval a (M row col)| ≤ L)
    (hd : ∀ row col, |MvPolynomial.eval a (MvPolynomial.pderiv j (M row col))| ≤ D) :
    |MvPolynomial.eval a (MvPolynomial.pderiv j M.det)| ≤
      (Fintype.card O).factorial * (Fintype.card O * D * L ^ Fintype.card O) := by
  classical
  rw [Matrix.det_apply', map_sum, map_sum]
  calc
    _ ≤ ∑ σ : Equiv.Perm O, |MvPolynomial.eval a (MvPolynomial.pderiv j
        (((Equiv.Perm.sign σ : ℤ) : MvPolynomial I ℝ) * ∏ i, M (σ i) i))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _σ : Equiv.Perm O, Fintype.card O * D * L ^ Fintype.card O := by
      apply Finset.sum_le_sum
      intro σ _
      have hsign : (((Equiv.Perm.sign σ : ℤ) : MvPolynomial I ℝ)) =
          MvPolynomial.C ((Equiv.Perm.sign σ : ℤ) : ℝ) := by simp
      rw [hsign, MvPolynomial.pderiv_C_mul, map_mul, MvPolynomial.eval_C, abs_mul,
        ← Int.cast_abs, Equiv.Perm.sign_abs, Int.cast_one, one_mul]
      simpa only [Finset.card_univ] using mvPolynomial_prod_pderiv_eval_abs_le_of_bound
        Finset.univ (fun i => M (σ i) i) j a hL hD
        (fun i _ => hM (σ i) i) (fun i _ => hd (σ i) i)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, nsmul_eq_mul]

theorem polynomial_det_eval_function {I O : Type*} [Fintype O] [DecidableEq O]
    (M : Matrix O O (MvPolynomial I ℝ)) :
    (fun a => (M.map (MvPolynomial.eval a)).det) = (fun a => MvPolynomial.eval a M.det) := by
  funext a
  have h := (MvPolynomial.eval a).map_det M
  simp only [RingHom.mapMatrix_apply] at h
  exact h.symm

theorem polynomial_det_fderiv_norm_le {I O : Type*}
    [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
    (M : Matrix O O (MvPolynomial I ℝ)) (a : I → ℝ) {L D : ℝ}
    (hL : 1 ≤ L) (hD : 0 ≤ D)
    (hM : ∀ row col, |MvPolynomial.eval a (M row col)| ≤ L)
    (hd : ∀ row col j, |MvPolynomial.eval a (MvPolynomial.pderiv j (M row col))| ≤ D) :
    ‖fderiv ℝ (fun x => (M.map (MvPolynomial.eval x)).det) a‖ ≤
      Fintype.card I * ((Fintype.card O).factorial *
        (Fintype.card O * D * L ^ Fintype.card O)) := by
  rw [polynomial_det_eval_function]
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  apply clm_norm_le_card_mul_of_basis _ (by positivity)
  intro j
  rw [mvPolynomial_fderiv_coordinate, Real.norm_eq_abs]
  exact polynomial_det_pderiv_eval_abs_le M a j hL hD hM (fun row col => hd row col j)

end Erdos3

end

end OAI
