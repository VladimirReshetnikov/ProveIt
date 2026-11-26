import IPRADerivations.Analysis.Names.GaussianNameConjugation
import IPRADerivations.Analysis.Exponential.GaussianExponentialInverse

/-!
# Named negation and conjugation on the imaginary axis

An exact zero real coordinate identifies native negation and
conjugation. The proof transports that identity through independent
original normalization clocks and the original Gaussian exponential.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianImaginaryNameConjugation

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (re)
open GaussianCoefficientNameBounds (unit)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_trans)
open GaussianNameRingLaws (negativeF negativeData negative_fast negative_sample_error
  equivalent_of_envelope three)
open GaussianRationalConjugation (point point_represents point_canonical)
open GaussianRationalHorner (canonical_unique scalar_congr represents_congr qzero)
open GaussianRationalL1 (rawGaussian rawDen raw_den_positive raw_represents)
open GaussianRationalMetric (qnegative qnegative_represents qnegative_canonical)
open GaussianRationalReciprocal (conjugate re_conjugate im_conjugate)
open GaussianRationalSyntheticDivision (qzero_add)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRootAlgebra (equal equal_of_values re_neg im_neg)
open GaussianRadiusExponentialName (input nameF data)
open RationalGaussianEmbedding (scalarZero scalar_zero_represents)
open RationalSupMetric (denominatorOf)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def imaginarySamples (f : PR 2) (x : PTm n) : Fm PTm n := .all
  (fstT (ap2 f (var 0) (Syn.shift x)) ≐ scalarZero)

@[simp] theorem subst_imaginarySamples {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (x : PTm n) :
    (imaginarySamples f x).subst σ = imaginarySamples f (Syn.subst σ x) := by
  simp [imaginarySamples, Syn.subst_shift, Syn.shift_subst]

theorem imaginary_at (f : PR 2) (p x : PTm n) (h : Γ ⊢[PRAAx] imaginarySamples f x) :
    Γ ⊢[PRAAx] fstT (ap2 f p x) ≐ scalarZero := by
  simpa only [imaginarySamples, Fm.subst_eq, subst_fstT, subst_ap2, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift, RationalGaussianEmbedding.subst_scalarZero] using h.allE p

theorem negative_point (q : PTm n) (h : Γ ⊢[PRAAx] fstT q ≐ scalarZero) :
    Γ ⊢[PRAAx] qnegative q ≐ point q := by
  let a := rawGaussian q
  let E := rawDen q
  let D := denominatorOf (fstT q)
  have hE := raw_den_positive (Γ := Γ) q
  have hq := raw_represents (Γ := Γ) q
  have hz := scalar_congr h.eqSymm (.eqRefl _) (.eqRefl _) (scalar_zero_represents E)
  have realZero : Γ ⊢[PRAAx] ZT.eq (re a) (ZT.ofNat zero) := by
    apply RationalNormalForm.positive_integer_cancel D _ _ (RationalArgmin.denominator_positive (fstT q))
    apply ZT.derive
    have ea := ZT.toZ_eq hq.andE₁
    have ez := ZT.toZ_eq hz
    simp only [ZT.toZ_mul, ZT.toZ_ofNat] at ea ez ⊢
    dsimp only [a,D,E] at ea ez ⊢
    linear_combination ea - ez
  have e : Γ ⊢[PRAAx] equal (ComplexLogarithmRemainder.neg a) (conjugate a) := by
    apply equal_of_values
    · simp only [re_neg, re_conjugate]
      rw [ZT.toZ_eq realZero]
      simp [ZT.toZ_ofNat, Q.mk_zero, map_zero]
    · simp only [im_neg, im_conjugate]
  exact canonical_unique _ _ _ E (qnegative_canonical _) (point_canonical _) hE
    (represents_congr (.eqRefl _) e (.eqRefl _) (qnegative_represents _ _ _ hq)) (point_represents _ _ _ hE hq)

theorem negative_conjugate_cross (f : PR 2) (x : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hi : Γ ⊢[PRAAx] imaginarySamples f x) :
    Γ ⊢[PRAAx] crossEquivalent (negativeF f) (GaussianNameConjugation.nameF f) (negativeData x) x := by
  apply equivalent_of_envelope _ _ _ _ three (negative_fast f x hf) (GaussianNameConjugation.regular f x hf)
  refine .allI ?_
  let C := Γ.map Fm.shift
  let y := Syn.shift x
  let p : PTm (n+1) := var 0
  have hr : C ⊢[PRAAx] pointCN f y := by simpa [Fm.shift, Syn.shift, y, C] using hf.shift
  have hAxis : C ⊢[PRAAx] imaginarySamples f y := by simpa [Fm.shift, Syn.shift, y, C] using hi.shift
  have e := (qzero_add (qnegative (ap2 f p y)) (qnegative_canonical (Γ := C) _)).eqTrans
    ((negative_point _ (imaginary_at f p y hAxis)).eqTrans (GaussianNameConjugation.sample_at f p y).eqSymm)
  simpa only [Syn.shift, GaussianNameRingLaws.subst_negativeData, three, two, one,
    PTm.subst_add, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero, C, y, p] using
    distance_congr (.eqRefl _) e (.eqRefl _) (.eqRefl _) (negative_sample_error f y p hr)

theorem negative_exponential_conjugate_cross (f : PR 2) (R x : PTm n)
    (hf : Γ ⊢[PRAAx] input f R x) (hi : Γ ⊢[PRAAx] imaginarySamples f x) :
    Γ ⊢[PRAAx] crossEquivalent (nameF (negativeF f)) (GaussianNameConjugation.nameF (nameF f))
      (data R (negativeData x)) (data R x) :=
  cross_trans _ _ _ _ _ _
    (GaussianExponentialRadiusIndependence.independent_radii_proper _ _ _ _ _ _
      (GaussianExponentialInverse.negative_input f R x hf) (GaussianNameConjugation.exponential_input f R x hf)
      (negative_conjugate_cross f x hf.andE₁ hi))
    (cross_symm _ _ _ _ (GaussianNameConjugation.exponential_cross f R x hf))

theorem actual_imaginary_name_negation_conjugation_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    ((pointCN f (var 0) ⋏ imaginarySamples f (var 0)) ⟶
      crossEquivalent (negativeF f) (GaussianNameConjugation.nameF f) (negativeData (var 0)) (var 0)) :=
  closeUniv 1 (.impI (negative_conjugate_cross f _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

theorem actual_imaginary_exponential_conjugation_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    ((input f (var 0) (var 1) ⋏ imaginarySamples f (var 1)) ⟶
      crossEquivalent (nameF (negativeF f)) (GaussianNameConjugation.nameF (nameF f))
        (data (var 0) (negativeData (var 1))) (data (var 0) (var 1))) :=
  closeUniv 2 (.impI (negative_exponential_conjugate_cross f _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianImaginaryNameConjugation
