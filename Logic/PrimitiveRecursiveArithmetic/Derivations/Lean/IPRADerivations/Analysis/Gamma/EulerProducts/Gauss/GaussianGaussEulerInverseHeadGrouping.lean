import IPRADerivations.Analysis.Gamma.EulerProducts.Gauss.GaussianGaussEulerReferenceHeads
import IPRADerivations.Analysis.Gamma.EulerProducts.FiniteHeads.GaussianGammaEulerFullHeadInverse
import IPRADerivations.Analysis.Gamma.FunctionalEquations.Multiplication.GaussianGammaGaussShiftedProduct
import IPRADerivations.Analysis.Gamma.GaussianGammaNormalization
import IPRADerivations.Analysis.RationalArithmetic.FiniteProducts.GaussianRationalProductAlgebra

/-!
# Exact grouping of the original finite Euler inverse heads

Each row inverse is the reciprocal of the actual returned Euler head.
The pole margin gives a unit equation for each shifted row, and the
positive real arguments give the unit equations on the reference side.
Finite product multiplication and the exact direct-head identity then
give the corresponding inverse-head identity.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGaussEulerInverseHeadGrouping

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (oneCode scale)
open GaussianGammaEulerDenominatorGrouping (shiftedNumerator shiftedData)
open GaussianGammaEulerFullHeadInverse (headInverse extended_guard)
open GaussianGammaEulerHead (run)
open GaussianGammaEulerHeadLower (returned_inverse_identity)
open GaussianGammaGaussEulerHeads (cutoff shiftedHeadBody shiftedHeads shifted_head_at)
open GaussianGammaGaussReferenceProduct (argument)
open GaussianGammaGaussShiftedProduct (source)
open GaussianGaussEulerReferenceHeads (referenceHeadBody referenceHeads reference_head_at head_grouping)
open GaussianRationalFiniteProduct (qprod)
open GaussianRationalHorner (qmul canonical qmul_canonical)
open GaussianRationalPowerAlgebra (qmul_commutative qmul_shuffle)
open GaussianRationalProductAlgebra (multiplyBody oneTerms product_multiply product_one_of_terms)
open GaussianRationalReciprocal (reciprocal subst_reciprocal)
open GaussianRationalSyntheticDivision (qone qone_canonical qmul_congr)
open GaussianReciprocalHorner (qmul_associative qmul_one_right)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def shiftedInverseBody : PTm 2 := reciprocal shiftedHeadBody
def referenceInverseBody : PTm 2 := reciprocal referenceHeadBody
def shiftedInverses (z B m N : PTm n) : PTm n := qprod shiftedInverseBody m (shiftedData z B m N)
def referenceInverses (m N : PTm n) : PTm n := qprod referenceInverseBody m (pairT m N)

@[simp] theorem subst_shiftedInverses {l : ℕ} (σ : Fin n → PTm l) (z B m N : PTm n) :
    Syn.subst σ (shiftedInverses z B m N) = shiftedInverses (Syn.subst σ z) (Syn.subst σ B)
      (Syn.subst σ m) (Syn.subst σ N) := by simp [shiftedInverses]

@[simp] theorem subst_referenceInverses {l : ℕ} (σ : Fin n → PTm l) (m N : PTm n) :
    Syn.subst σ (referenceInverses m N) = referenceInverses (Syn.subst σ m) (Syn.subst σ N) := by
  simp [referenceInverses]

private theorem reciprocal_congr {u v : PTm n} (h : Γ ⊢[PRAAx] u ≐ v) :
    Γ ⊢[PRAAx] reciprocal u ≐ reciprocal v := by
  simpa only [subst_reciprocal,Syn.subst_var,Matrix.cons_val_zero] using
    Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (reciprocal (var 0) : PTm 1)
      (σ := ![u]) (σ' := ![v]) (fun i => by fin_cases i; exact h)

theorem shifted_inverse_at (r z B m N : PTm n) : Γ ⊢[PRAAx]
    inst2 shiftedInverseBody r (shiftedData z B m N) ≐ headInverse (shiftedNumerator z B m r) (B*m) N := by
  simpa only [shiftedInverseBody,headInverse,inst2,subst_reciprocal] using
    reciprocal_congr (shifted_head_at r z B m N)

theorem reference_inverse_at (r m N : PTm n) : Γ ⊢[PRAAx]
    inst2 referenceInverseBody r (pairT m N) ≐ headInverse (argument r) m N := by
  simpa only [referenceInverseBody,headInverse,inst2,subst_reciprocal] using
    reciprocal_congr (reference_head_at r m N)

theorem head_inverse_unit (z R B a d N : PTm n) (h : Γ ⊢[PRAAx] GaussianGammaReciprocalInverse.source z R B a d) :
    Γ ⊢[PRAAx] qmul (run z B N) (headInverse z B N) ≐ qone :=
  returned_inverse_identity z B one d N h.andE₁.andE₂.andE₁ (le_refl one) h.andE₂.andE₂.andE₁
    (extended_guard z R B a d N h)

theorem shifted_inverse_unit (z R B m a d N : PTm n) (h : Γ ⊢[PRAAx] source z R B m a d) :
    Γ ⊢[PRAAx] qmul (shiftedHeads z B m N) (shiftedInverses z B m N) ≐ qone := by
  let x := shiftedData z B m N
  have rows : Γ ⊢[PRAAx] oneTerms (multiplyBody shiftedHeadBody shiftedInverseBody) m x := by
    refine .allI (.impI ?_)
    let sh (u : PTm n) := Syn.shift u
    let Δ := lt (var 0) (sh m) :: Γ.map Fm.shift
    have hs : Δ ⊢[PRAAx] source (sh z) (sh R) (sh B) (sh m) (sh a) (sh d) := by
      simpa [Δ,sh,Fm.shift,Syn.shift] using h.shift.wk
    have hr : Δ ⊢[PRAAx] lt (var 0) (sh m) := Prf.hyp0
    have hc := GaussianGammaGaussShiftedProduct.row_source (sh z) (sh R) (sh B) (sh m) (var 0) (sh a) (sh d) hs hr
    have eq := qmul_congr (shifted_head_at (Γ := Δ) (var 0) (sh z) (sh B) (sh m) (sh N))
      (shifted_inverse_at (var 0) (sh z) (sh B) (sh m) (sh N))
    have step := eq.eqTrans (head_inverse_unit _ _ _ _ _ (sh N) hc)
    simpa only [x,sh,Δ,oneTerms,GaussianRationalProductAlgebra.multiply_body_at,
      GaussianGammaEulerDenominatorGrouping.subst_shiftedData,Syn.shift] using step
  exact (product_multiply shiftedHeadBody shiftedInverseBody m x).eqSymm.eqTrans (product_one_of_terms _ _ _ rows)

theorem reference_inverse_unit (m N : PTm n) :
    Γ ⊢[PRAAx] qmul (referenceHeads m N) (referenceInverses m N) ≐ qone := by
  let x := pairT m N
  have rows : Γ ⊢[PRAAx] oneTerms (multiplyBody referenceHeadBody referenceInverseBody) m x := by
    refine .allI (.impI ?_)
    let M := Syn.shift m
    let K := Syn.shift N
    let Δ := lt (var 0) M :: Γ.map Fm.shift
    have hr : Δ ⊢[PRAAx] lt (var 0) M := Prf.hyp0
    have hc := GaussianGammaGaussReferenceProduct.row_source (var 0) M hr
    have eq := qmul_congr (reference_head_at (Γ := Δ) (var 0) M K) (reference_inverse_at (var 0) M K)
    have step := eq.eqTrans (head_inverse_unit _ _ _ _ _ K hc)
    simpa only [x,M,K,Δ,oneTerms,GaussianRationalProductAlgebra.multiply_body_at,subst_pairT,Syn.shift] using step
  exact (product_multiply referenceHeadBody referenceInverseBody m x).eqSymm.eqTrans (product_one_of_terms _ _ _ rows)

private theorem inverse_unique (a b u v : PTm n) (h : Γ ⊢[PRAAx] a ≐ b)
    (hu : Γ ⊢[PRAAx] qmul a u ≐ qone) (hv : Γ ⊢[PRAAx] qmul b v ≐ qone)
    (cu : Γ ⊢[PRAAx] canonical u) (cv : Γ ⊢[PRAAx] canonical v) : Γ ⊢[PRAAx] u ≐ v := by
  have sub := (qmul_congr h (.eqRefl v)).eqTrans hv
  have left : Γ ⊢[PRAAx] u ≐ qmul u (qmul a v) :=
    (qmul_one_right u cu).eqSymm.eqTrans (qmul_congr (.eqRefl _) sub.eqSymm)
  have commute : Γ ⊢[PRAAx] qmul u a ≐ qone := (qmul_commutative _ _).eqTrans hu
  have right : Γ ⊢[PRAAx] qmul qone v ≐ v := (qmul_commutative _ _).eqTrans (qmul_one_right v cv)
  exact left.eqTrans ((qmul_associative u a v).eqSymm.eqTrans
    ((qmul_congr commute (.eqRefl v)).eqTrans right))

theorem inverse_grouping (z R B m a d N : PTm n) (h : Γ ⊢[PRAAx] source z R B m a d) :
    Γ ⊢[PRAAx] qmul (shiftedInverses z B m N) (headInverse oneCode one (cutoff m N)) ≐
      qmul (headInverse (scale m z) B (cutoff m N)) (referenceInverses m N) := by
  let L := cutoff m N
  let w := scale m z
  have s := shifted_inverse_unit z R B m a d N h
  have r := reference_inverse_unit (Γ := Γ) m N
  have l := head_inverse_unit w (GaussianGammaGaussDomain.scaledRadius R m) B a d L h.andE₂
  have u := head_inverse_unit (Γ := Γ) oneCode one one one one L GaussianGammaNormalization.unit_gamma_source
  have left : Γ ⊢[PRAAx] qmul (qmul (shiftedHeads z B m N) (run oneCode one L))
      (qmul (shiftedInverses z B m N) (headInverse oneCode one L)) ≐ qone :=
    (qmul_shuffle _ _ _ _).eqTrans ((qmul_congr s u).eqTrans (qmul_one_right qone qone_canonical))
  have right : Γ ⊢[PRAAx] qmul (qmul (run w B L) (referenceHeads m N))
      (qmul (headInverse w B L) (referenceInverses m N)) ≐ qone :=
    (qmul_shuffle _ _ _ _).eqTrans ((qmul_congr l r).eqTrans (qmul_one_right qone qone_canonical))
  exact inverse_unique _ _ _ _ (head_grouping z B m N h.andE₂.andE₁.andE₂.andE₁ h.andE₁.andE₁).eqSymm
    left right (qmul_canonical _ _) (qmul_canonical _ _)

theorem original_Gauss_inverse_head_grouping_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      qmul (shiftedInverses (var 0) (var 2) (var 3) (var 6))
        (headInverse oneCode one (cutoff (var 3) (var 6))) ≐
      qmul (headInverse (scale (var 3) (var 0)) (var 2) (cutoff (var 3) (var 6)))
        (referenceInverses (var 3) (var 6))) :=
  closeUniv 7 (.impI (inverse_grouping _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGaussEulerInverseHeadGrouping
