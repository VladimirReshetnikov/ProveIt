/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Lattices.ResidueSliceNormalizedCell

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X]

noncomputable def finiteProductIntegral (w : I → X → ℝ) (f : (I → X) → ℝ) : ℝ :=
  ∑ v, (∏ i, w i (v i)) * f v

theorem finiteProductIntegral_nonneg (w : I → X → ℝ) (hw : ∀ i x, 0 ≤ w i x)
    (f : (I → X) → ℝ) (hf : ∀ v, 0 ≤ f v) : 0 ≤ finiteProductIntegral w f :=
  Finset.sum_nonneg (fun v _ => mul_nonneg (Finset.prod_nonneg (fun i _ => hw i (v i))) (hf v))

theorem finiteTuple_sum_snoc {A : Type*} [AddCommMonoid A] (n : ℕ)
    (f : (Fin (n + 1) → X) → A) :
    (∑ v, f v) = ∑ v : Fin n → X, ∑ a : X, f (Fin.snoc v a) := by
  calc
    (∑ v, f v) = ∑ p : X × (Fin n → X), f (Fin.snoc p.2 p.1) :=
      (Fintype.sum_equiv (Fin.snocEquiv (fun _ : Fin (n + 1) => X))
        (fun p => f (Fin.snoc p.2 p.1)) f (fun p => rfl)).symm
    _ = _ := by rw [Fintype.sum_prod_type, Finset.sum_comm]

theorem finiteProductIntegral_zero (w : Fin 0 → X → ℝ) (f : (Fin 0 → X) → ℝ) :
    finiteProductIntegral w f = f (fun i => Fin.elim0 i) := by
  classical
  simp only [finiteProductIntegral, Fin.prod_univ_zero, one_mul]
  rw [Fintype.sum_unique]
  congr 1

theorem finiteProductIntegral_snoc (n : ℕ) (w : Fin (n + 1) → X → ℝ)
    (f : (Fin (n + 1) → X) → ℝ) :
    finiteProductIntegral w f = finiteProductIntegral (fun i : Fin n => w i.castSucc)
      (fun v => ∑ a, w (Fin.last n) a * f (Fin.snoc v a)) := by
  unfold finiteProductIntegral
  rw [finiteTuple_sum_snoc]
  apply Finset.sum_congr rfl
  intro v _
  simp only [Fin.prod_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

end Erdos3

end

section

namespace Erdos3

variable {I X : Type*}

def finiteSplitPoint (p : I → Prop) [DecidablePred p]
    (u : {i // p i} → X) (v : {i // ¬p i} → X) : I → X :=
  fun i => if h : p i then u ⟨i, h⟩ else v ⟨i, h⟩

theorem finiteSplitPoint_fixed (p : I → Prop) [DecidablePred p]
    (u : {i // p i} → X) (v : {i // ¬p i} → X) (i : {i // p i}) :
    finiteSplitPoint p u v i = u i := by
  simp only [finiteSplitPoint, dite_eq_left i.property]

theorem finiteSplitPoint_free (p : I → Prop) [DecidablePred p]
    (u : {i // p i} → X) (v : {i // ¬p i} → X) (i : {i // ¬p i}) :
    finiteSplitPoint p u v i = v i := by
  simp only [finiteSplitPoint, dite_eq_right i.property]

theorem finiteSplitPoint_restrict (p : I → Prop) [DecidablePred p] (x : I → X) :
    finiteSplitPoint p (fun i => x i) (fun i => x i) = x := by
  funext i
  by_cases hi : p i <;> simp only [finiteSplitPoint, hi, dite_true, dite_false]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem finiteProductIntegral_mono {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X]
    (w : I → X → ℝ) (hw : ∀ i x, 0 ≤ w i x) (f g : (I → X) → ℝ)
    (hfg : ∀ v, f v ≤ g v) : finiteProductIntegral w f ≤ finiteProductIntegral w g :=
  Finset.sum_le_sum (fun v _ => mul_le_mul_of_nonneg_left (hfg v)
    (Finset.prod_nonneg (fun i _ => hw i (v i))))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I J X : Type*}

def finiteProductCoordinateEquiv (e : I ≃ J) : (I → X) ≃ (J → X) where
  toFun v j := v (e.symm j)
  invFun v i := v (e i)
  left_inv v := by funext i; simp
  right_inv v := by funext j; simp

theorem finiteProductIntegral_reindex [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype X]
    (e : I ≃ J) (w : J → X → ℝ) (f : (J → X) → ℝ) :
    finiteProductIntegral (fun i => w (e i)) (fun v => f (fun j => v (e.symm j))) =
      finiteProductIntegral w f := by
  unfold finiteProductIntegral
  apply Fintype.sum_equiv (finiteProductCoordinateEquiv e)
  intro v
  have hprod : (∏ i, w (e i) (v i)) = ∏ j, w j (v (e.symm j)) := by
    apply Fintype.prod_equiv e
    intro i
    simp only [Equiv.symm_apply_apply]
  simpa only [finiteProductCoordinateEquiv, Equiv.coe_fn_mk] using
    congrArg (fun t => t * f (fun j => v (e.symm j))) hprod

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X]

theorem finiteProductIntegral_split (p : I → Prop) [DecidablePred p]
    (w : I → X → ℝ) (f : (I → X) → ℝ) :
    finiteProductIntegral w f =
      finiteProductIntegral (fun i : {i // p i} => w i) (fun u =>
        finiteProductIntegral (fun i : {i // ¬p i} => w i) (fun v => f (finiteSplitPoint p u v))) := by
  classical
  calc
    finiteProductIntegral w f =
        ∑ uv : ({i // p i} → X) × ({i // ¬p i} → X),
          (∏ i : {i // p i}, w i (uv.1 i)) *
            (∏ i : {i // ¬p i}, w i (uv.2 i)) * f (finiteSplitPoint p uv.1 uv.2) := by
      apply Fintype.sum_equiv (Equiv.piEquivPiSubtypeProd p (fun _ => X))
      intro x
      change (∏ i, w i (x i)) * f x =
        (∏ i : {i // p i}, w i (x i)) * (∏ i : {i // ¬p i}, w i (x i)) *
          f (finiteSplitPoint p (fun i => x i) (fun i => x i))
      rw [finiteSplitPoint_restrict, Fintype.prod_subtype_mul_prod_subtype p (fun i => w i (x i))]
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp only [finiteProductIntegral, Finset.mul_sum, mul_assoc]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I J X : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype X]

theorem finiteProductIntegral_pullback_equiv (e : J ≃ I) (w : I → X → ℝ)
    (g : (J → X) → ℝ) :
    finiteProductIntegral w (fun x => g (fun j => x (e j))) =
      finiteProductIntegral (fun j => w (e j)) g := by
  unfold finiteProductIntegral
  apply Fintype.sum_equiv (finiteProductCoordinateEquiv e).symm
  intro x
  change (∏ i, w i (x i)) * g (fun j => x (e j)) =
    (∏ j, w (e j) (x (e j))) * g (fun j => x (e j))
  rw [e.prod_comp (fun i => w i (x i))]

end Erdos3

end

section

namespace Erdos3.ResidueBoxSlice

open MvPolynomial

variable {X : Type*} {keep : X → Prop} {N : {x // keep x} → ℕ} {q s d : ℕ}

noncomputable def fiberInverseParameters (S : ResidueBoxSlice N q) (k : {x // keep x}) :
    MvPolynomial X ℝ :=
  (q : ℝ)⁻¹ • (MvPolynomial.X k.val - C (S.start k : ℝ))

theorem fiberInverseParameters_degree (S : ResidueBoxSlice N q) (k : {x // keep x}) :
    S.fiberInverseParameters k ∈ weightedSupportLE (fun _ : X => 1) 1 :=
  (weightedSupportLE _ _).smul_mem _
    ((weightedSupportLE _ _).sub_mem (weightedSupportLE_X _ _) (weightedSupportLE_C _ _ _))

noncomputable def fiberReinsertPatch (S : ResidueBoxSlice N q)
    (Q : PolynomialPatch {x // keep x} s d) : PolynomialPatch X s d :=
  Q.reparam S.fiberInverseParameters S.fiberInverseParameters_degree

@[simp] theorem fiberReinsertPatch_kernel (S : ResidueBoxSlice N q)
    (Q : PolynomialPatch {x // keep x} s d) : (S.fiberReinsertPatch Q).kernel = Q.kernel := rfl

@[simp] theorem fiberReinsertPatch_weight (S : ResidueBoxSlice N q)
    (Q : PolynomialPatch {x // keep x} s d) : (S.fiberReinsertPatch Q).weight = Q.weight := rfl

@[simp] theorem fiberReinsertPatch_lip (S : ResidueBoxSlice N q)
    (Q : PolynomialPatch {x // keep x} s d) : (S.fiberReinsertPatch Q).kernel.lip = Q.kernel.lip := rfl

theorem fiberReinsertPatch_value (S : ResidueBoxSlice N q)
    (Q : PolynomialPatch {x // keep x} s d) (x : X → ℝ) :
    (S.fiberReinsertPatch Q).value x =
      Q.value (fun k => (x k.val - (S.start k : ℝ)) / (q : ℝ)) := by
  rw [fiberReinsertPatch, PolynomialPatch.reparam_value]
  congr 1
  funext k
  simp only [fiberInverseParameters, map_smul, map_sub, aeval_X, aeval_C,
    smul_eq_mul, div_eq_mul_inv, mul_comm, Algebra.algebraMap_self, RingHom.id_apply]

def fiberIntegerPoint [DecidablePred keep] (S : ResidueBoxSlice N q)
    (fixed : {x // ¬keep x} → ℤ) (u : ∀ k, Fin (S.length k)) : X → ℤ :=
  finiteSplitPoint keep (fun k => ((S.point u k).val : ℤ)) fixed

theorem fiberReinsertPatch_point_value [DecidablePred keep] (S : ResidueBoxSlice N q)
    (Q : PolynomialPatch {x // keep x} s d) (hq : 0 < q)
    (fixed : {x // ¬keep x} → ℤ) (u : ∀ k, Fin (S.length k)) :
    (S.fiberReinsertPatch Q).value
      (fun k => ((finiteSplitPoint keep (fun i => ((S.point u i).val : ℤ)) fixed k : ℤ) : ℝ)) =
        Q.value (fun k => ((u k).val : ℝ)) := by
  rw [fiberReinsertPatch_value]
  congr 1
  funext k
  rw [finiteSplitPoint_fixed]
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  simp only [point, Nat.cast_add, Nat.cast_mul, Int.cast_add, Int.cast_mul, Int.cast_natCast]
  field_simp
  ring

@[simp] theorem fiberReinsertPatch_integerPoint_value [DecidablePred keep]
    (S : ResidueBoxSlice N q) (Q : PolynomialPatch {x // keep x} s d) (hq : 0 < q)
    (fixed : {x // ¬keep x} → ℤ) (u : ∀ k, Fin (S.length k)) :
    (S.fiberReinsertPatch Q).value (fun k => (S.fiberIntegerPoint fixed u k : ℝ)) =
      Q.value (fun k => ((u k).val : ℝ)) :=
  S.fiberReinsertPatch_point_value Q hq fixed u

end Erdos3.ResidueBoxSlice

end

end OAI
