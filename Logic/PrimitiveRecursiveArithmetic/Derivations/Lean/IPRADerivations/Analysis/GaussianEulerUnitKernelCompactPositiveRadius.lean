import IPRADerivations.Analysis.GaussianEulerUnitKernelCompactDominance

/-!
# The explicit positive projected-real radius for compact unit kernels

The actual represented scalar bound becomes the literal Gaussian sum
of the projected original comparator and both requested dyadic errors.
Its native nonnegative representation follows from the comparator's
proved lower observation envelope. No new positivity bound is supplied.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerUnitKernelCompactPositiveRadius

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerUnitKernelCompactName (source nameF data)
open GaussianEulerVerticalNativeProjection (argument)
open GaussianGammaRealValues (projection projection_represents)
open GaussianRationalL1 (rawGaussian rawDen raw_represents raw_den_positive)
open GaussianEulerVerticalRealRadius (gap denominator gap_identity)
open GaussianDominantPairAlgebra (radiusPoint radius_represents)
open GaussianRationalHorner (qadd positive_product scalar_congr)
open GaussianPositiveRadiusFiniteSum (boundBy)
open RationalGaussianEmbedding (scalarZero)
open GaussianCoefficientNameBounds (unit unit_positive)
open ComplexLogarithmRemainder (re)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def positiveRadius (v P Q : PTm n) : PTm n := qadd (projection v) (radiusPoint (P+Q) (P*Q))
def nativeNumerator (v P Q : PTm n) : PTm n := gap v Q*P+denominator v Q
def nativeDenominator (v P Q : PTm n) : PTm n := denominator v Q*P
def radius (p q z R B a C E G : PTm n) : PTm n := positiveRadius
  (ap2 nameF q (data (argument z) R B a C E G)) (unit p) (unit q)

@[simp] theorem subst_positiveRadius {m : ℕ} (σ : Fin n → PTm m) (v P Q : PTm n) :
    Syn.subst σ (positiveRadius v P Q) = positiveRadius (Syn.subst σ v) (Syn.subst σ P) (Syn.subst σ Q) := by simp [positiveRadius]
@[simp] theorem subst_nativeNumerator {m : ℕ} (σ : Fin n → PTm m) (v P Q : PTm n) :
    Syn.subst σ (nativeNumerator v P Q) = nativeNumerator (Syn.subst σ v) (Syn.subst σ P) (Syn.subst σ Q) := by
  simp [nativeNumerator,gap,denominator,ComplexLogarithmRemainder.re]
@[simp] theorem subst_nativeDenominator {m : ℕ} (σ : Fin n → PTm m) (v P Q : PTm n) :
    Syn.subst σ (nativeDenominator v P Q) = nativeDenominator (Syn.subst σ v) (Syn.subst σ P) (Syn.subst σ Q) := by
  simp [nativeDenominator,denominator]
@[simp] theorem subst_radius {m : ℕ} (σ : Fin n → PTm m) (p q z R B a C E G : PTm n) :
    Syn.subst σ (radius p q z R B a C E G) = radius (Syn.subst σ p) (Syn.subst σ q) (Syn.subst σ z) (Syn.subst σ R)
      (Syn.subst σ B) (Syn.subst σ a) (Syn.subst σ C) (Syn.subst σ E) (Syn.subst σ G) := by simp [radius]

theorem denominator_positive (v P Q : PTm n) (hP : Γ ⊢[PRAAx] le one P) (hQ : Γ ⊢[PRAAx] le one Q) : Γ ⊢[PRAAx]
    le one (nativeDenominator v P Q) := positive_product _ _ (GaussianEulerVerticalRealRadius.denominator_positive v Q hQ) hP

/-- Exact scalar representation, valid for arbitrary raw observations. -/
theorem scalar_representation (v P Q : PTm n) (hP : Γ ⊢[PRAAx] le one P) (hQ : Γ ⊢[PRAAx] le one Q)
    (hl : Γ ⊢[PRAAx] RationalValueBounds.upper scalarZero (fstT v) one Q) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (fstT (positiveRadius v P Q)) (ZT.ofNat (nativeNumerator v P Q)) (nativeDenominator v P Q) := by
  have proj : Γ ⊢[PRAAx] RationalArithmetic.represents (fstT (projection v)) (re (rawGaussian v)) (rawDen v) :=
    scalar_congr (.eqRefl _) (by
      apply ZT.derive
      simp only [RationalGaussianEmbedding.native,ComplexLogarithmRemainder.eval_re_code]) (.eqRefl _)
      (projection_represents v (rawGaussian v) (rawDen v) (raw_represents v)).andE₁
  have extra : Γ ⊢[PRAAx] RationalArithmetic.represents (fstT (radiusPoint (P+Q) (P*Q))) (ZT.ofNat (P+Q)) (P*Q) :=
    scalar_congr (.eqRefl _) (by
      apply ZT.derive
      simp only [GaussianDominantPairAlgebra.radiusNumerator,ComplexLogarithmRemainder.eval_re_code]) (.eqRefl _)
      (radius_represents (P+Q) (P*Q) (positive_product _ _ hP hQ)).andE₁
  have actual := RationalRepresentations.represents_add _ _ _ _ _ _ proj extra
  apply scalar_congr (RationalGaussianRealPart.real_add _ _).eqSymm _ (by unfold nativeDenominator denominator; ipra_ring) actual
  apply ZT.derive
  have e := natEq (gap_identity (Γ := Γ) v Q hl)
  simp only [nativeNumerator,denominator,ZT.toZ_add,ZT.toZ_mul,ZT.toZ_ofNat]
  dsimp only [ZT.toZ]
  ipra_simps
  linear_combination (𝔞 P)*e

theorem radius_positive (v P Q : PTm n) (hP : Γ ⊢[PRAAx] le one P) (hQ : Γ ⊢[PRAAx] le one Q)
    (hl : Γ ⊢[PRAAx] RationalValueBounds.upper scalarZero (fstT v) one Q) : Γ ⊢[PRAAx]
    GaussianPositiveRealArithmetic.positive (positiveRadius v P Q) := by
  have extra := GaussianPositiveRealArithmetic.positive_from_representation (radiusPoint (P+Q) (P*Q)) (P+Q) (P*Q)
    (GaussianRationalHorner.ofGaussian_canonical _ _ (positive_product _ _ hP hQ)) (positive_product _ _ hP hQ)
    (radius_represents (P+Q) (P*Q) (positive_product _ _ hP hQ))
  exact .andI (RationalGaussianEmbedding.axis_add _ _ (RationalGaussianEmbedding.embed_axis _) extra.andE₁)
    (GaussianRationalL1.nonnegative_of_representation _ _ _ (denominator_positive v P Q hP hQ) (scalar_representation v P Q hP hQ hl))

theorem from_represented_bound (w v P Q : PTm n) (hP : Γ ⊢[PRAAx] le one P) (hQ : Γ ⊢[PRAAx] le one Q)
    (hl : Γ ⊢[PRAAx] RationalValueBounds.upper scalarZero (fstT v) one Q)
    (hb : Γ ⊢[PRAAx] GaussianRationalMetric.bounded w (nativeNumerator v P Q) (nativeDenominator v P Q)) : Γ ⊢[PRAAx]
    boundBy w (positiveRadius v P Q) :=
  GaussianPositiveRadiusFiniteSum.from_representation _ _ _ _ (denominator_positive v P Q hP hQ)
    (radius_positive v P Q hP hQ hl) (scalar_representation v P Q hP hQ hl) hb

theorem original_boundBy (p q z R B a C E G : PTm n) (h : Γ ⊢[PRAAx] source z R B a C E G) : Γ ⊢[PRAAx]
    boundBy (ap2 nameF p (data z R B a C E G)) (radius p q z R B a C E G) :=
  from_represented_bound _ _ _ _ (unit_positive p) (unit_positive q)
    (GaussianEulerUnitKernelCompactDominance.original_companion_nonnegative q z R B a C E G h)
    (GaussianEulerUnitKernelCompactDominance.original_observations p q z R B a C E G h)

theorem actual_original_compact_unit_kernel_explicit_positive_radius_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (source (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⟶
      boundBy (ap2 nameF (var 0) (data (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8)))
        (radius (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8))) :=
  closeUniv 9 (.impI (original_boundBy _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerUnitKernelCompactPositiveRadius
