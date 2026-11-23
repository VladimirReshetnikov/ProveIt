import IPRADerivations.Analysis.GaussianRationalParameterTelescope
import IPRADerivations.Analysis.GaussianNamedDifferenceQuotient
import IPRADerivations.Analysis.GaussianApproximateInverseDistance

/-!
# Exact normalization of an original finite parameter telescope

The literal reciprocal step multiplies the local accumulated error.
Its product with the original small step is exactly 1/N, so averaging
the slope errors cancels N before applying their bound. The resulting
slope contribution retains B/E, independent of the increment denominator.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRationalNormalizedTelescope

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalParameterTelescope (localRows slopeRows step local_error constant_slope_product)
open GaussianNamedDifferenceQuotient (separated inverse inverse_bound actual_inverse scale_distance)
open GaussianRationalHorner (ofGaussian qmul positive_product canonical_unique represents_congr)
open GaussianRationalMetric (qsub bounded distanceBounded bounded_of_cleared)
open GaussianRationalReciprocal (bound_congr bounded_product)
open GaussianRationalFiniteSum (sum)
open GaussianRationalRiemannRefinement (constantBody)
open GaussianRationalNaturalScale (natScale)
open GaussianRationalSyntheticDivision (qone qmul_congr)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianReciprocalHorner (qmul_associative qmul_one_right)
open GaussianRationalPowerAlgebra (qmul_commutative)
open ComplexLogarithmRemainder (oneCode)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def weight (N : PTm n) : PTm n := ofGaussian oneCode N
def numerator (D N A L B E : PTm n) : PTm n := D*N*A*E+B*L
def denominator (L E : PTm n) : PTm n := L*E
def input (f g : PTm 2) (N x y h D v A L B E : PTm n) : Fm PTm n :=
  separated h D ⋏ (le one N ⋏ (le one L ⋏ (le one E ⋏
    (localRows f g N x y (step h D N) A L ⋏ slopeRows g N y v B E))))

@[simp] theorem subst_weight {m : ℕ} (σ : Fin n → PTm m) (N : PTm n) :
    Syn.subst σ (weight N) = weight (Syn.subst σ N) := by simp [weight]
@[simp] theorem subst_numerator {m : ℕ} (σ : Fin n → PTm m) (D N A L B E : PTm n) :
    Syn.subst σ (numerator D N A L B E) = numerator (Syn.subst σ D) (Syn.subst σ N) (Syn.subst σ A)
      (Syn.subst σ L) (Syn.subst σ B) (Syn.subst σ E) := by simp [numerator]
@[simp] theorem subst_denominator {m : ℕ} (σ : Fin n → PTm m) (L E : PTm n) :
    Syn.subst σ (denominator L E) = denominator (Syn.subst σ L) (Syn.subst σ E) := by simp [denominator]
@[simp] theorem subst_input {m : ℕ} (σ : Fin n → PTm m) (f g : PTm 2) (N x y h D v A L B E : PTm n) :
    (input f g N x y h D v A L B E).subst σ = input f g (Syn.subst σ N) (Syn.subst σ x) (Syn.subst σ y)
      (Syn.subst σ h) (Syn.subst σ D) (Syn.subst σ v) (Syn.subst σ A) (Syn.subst σ L) (Syn.subst σ B) (Syn.subst σ E) := by
  simp [input]

theorem step_factorization (h D N : PTm n) (hD : Γ ⊢[PRAAx] le one D) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    step h D N ≐ qmul (ofGaussian h D) (weight N) := by
  have hd := positive_product _ _ hD hN
  have product := GaussianRationalHorner.qmul_represents _ _ h oneCode D N hD hN
    (GaussianRationalHorner.ofGaussian_represents h D hD) (GaussianRationalHorner.ofGaussian_represents oneCode N hN)
  have native : Γ ⊢[PRAAx] GaussianRootAlgebra.equal (ComplexLogarithmRemainder.mul h oneCode) h := by
    apply GaussianRootAlgebra.equal_of_values <;>
      simp only [GaussianRootAlgebra.re_mul,GaussianRootAlgebra.im_mul,GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one] <;> ring
  exact canonical_unique _ _ h (D*N) (GaussianRationalHorner.ofGaussian_canonical _ _ hd)
    (GaussianRationalHorner.qmul_canonical _ _) hd (GaussianRationalHorner.ofGaussian_represents h (D*N) hd)
    (represents_congr (.eqRefl _) native (.eqRefl _) product)

theorem normalized_step (h D N : PTm n) (hs : Γ ⊢[PRAAx] separated h D) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    qmul (inverse h D) (step h D N) ≐ weight N :=
  (qmul_congr (.eqRefl _) (step_factorization h D N hs.andE₁ hN)).eqTrans
    ((qmul_associative _ _ _).eqSymm.eqTrans
      ((qmul_congr (actual_inverse h D hs) (.eqRefl _)).eqTrans
        ((qmul_commutative _ _).eqTrans (qmul_one_right _ (GaussianRationalHorner.ofGaussian_canonical _ _ hN)))))

theorem weight_bound (N : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx] bounded (weight N) one N := by
  apply bounded_of_cleared _ oneCode N one N hN hN (GaussianRationalHorner.ofGaussian_represents oneCode N hN)
  exact le_congr ((congrMul (.eqRefl _) ComplexLogarithmRemainder.normSq_one).eqTrans (by ipra_ring)).eqSymm
    (by ipra_ring) (le_refl (N*N))

theorem weight_sum_one (N : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx] natScale N (weight N) ≐ qone := by
  have left := GaussianRationalNaturalScale.natScale_represents N (weight N) oneCode N hN
    (GaussianRationalHorner.ofGaussian_represents oneCode N hN)
  have right := GaussianRationalHorner.represents_rescale (Γ := Γ) qone oneCode one N
    (GaussianRationalHorner.ofGaussian_represents oneCode one (le_refl one))
  exact canonical_unique _ _ (ComplexLogarithmRemainder.scale N oneCode) N
    (GaussianRationalNaturalScale.natScale_canonical _ _) GaussianRationalSyntheticDivision.qone_canonical hN left
    (represents_congr (.eqRefl _) (GaussianRootAlgebra.equal_refl _) (one_mul _) right)

theorem mean_error (g : PTm 2) (N y v B E : PTm n) (hN : Γ ⊢[PRAAx] le one N) (hE : Γ ⊢[PRAAx] le one E)
    (hs : Γ ⊢[PRAAx] slopeRows g N y v B E) : Γ ⊢[PRAAx]
    distanceBounded (qmul (weight N) (sum g N y)) v B E := by
  have rows := GaussianRationalRiemannRefinement.sum_distance g constantBody N y v B E hE hs
  have actual := bounded_product _ _ one N (N*B) E hN hE (weight_bound N hN) rows
  have product : Γ ⊢[PRAAx] distanceBounded (qmul (weight N) (sum g N y)) (qmul (weight N) (sum constantBody N v))
      (N*B) (N*E) :=
    bound_congr (GaussianRationalRoundedPower.multiplication_difference _ _ _).eqSymm (one_mul _) (.eqRefl _) actual
  have first := distance_radius_mono _ _ _ _ B E (positive_product _ _ hN hE) hE
    (le_of_eq_add (d := zero) (by ipra_ring)) product
  have exactMean : Γ ⊢[PRAAx] qmul (weight N) (sum constantBody N v) ≐ qmul qone v :=
    (constant_slope_product N (weight N) v).eqTrans (qmul_congr (weight_sum_one N hN) (.eqRefl _))
  have zero := distance_congr (qmul_commutative v qone) (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (GaussianApproximateInverseDistance.unit_product_distance v E hE)
  have last := distance_congr exactMean.eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) zero
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hE first last)

theorem normalized_error (f g : PTm 2) (N x y h D v A L B E : PTm n)
    (hs : Γ ⊢[PRAAx] separated h D) (hN : Γ ⊢[PRAAx] le one N) (hL : Γ ⊢[PRAAx] le one L) (hE : Γ ⊢[PRAAx] le one E)
    (hl : Γ ⊢[PRAAx] localRows f g N x y (step h D N) A L)
    (hg : Γ ⊢[PRAAx] slopeRows g N y v B E) : Γ ⊢[PRAAx]
    distanceBounded (qmul (inverse h D) (qsub (inst2 f N x) (inst2 f zero x))) v
      (numerator D N A L B E) (denominator L E) := by
  have adjacent := scale_distance (inverse h D) _ _ D (N*A) L hL (inverse_bound h D hs)
    (local_error f g N x y (step h D N) A L hL hl)
  have center : Γ ⊢[PRAAx] qmul (inverse h D) (qmul (step h D N) (sum g N y)) ≐ qmul (weight N) (sum g N y) :=
    (qmul_associative _ _ _).eqSymm.eqTrans (qmul_congr (normalized_step h D N hs hN) (.eqRefl _))
  have first := distance_congr (.eqRefl _) center (.eqRefl _) (.eqRefl _) adjacent
  have joined := GaussianReconstructionRoots.distance_triangle _ _ _ (D*(N*A)) L B E hL hE first (mean_error g N y v B E hN hE hg)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold numerator; ipra_ring) (.eqRefl _) joined

theorem actual_normalized_finite_parameter_telescope_closed (f g : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    (input f g (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) ⟶
      distanceBounded (qmul (inverse (var 3) (var 4)) (qsub (inst2 f (var 0) (var 1)) (inst2 f zero (var 1)))) (var 5)
        (numerator (var 4) (var 0) (var 6) (var 7) (var 8) (var 9)) (denominator (var 7) (var 9))) :=
  closeUniv 10 (.impI (normalized_error f g _ _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianRationalNormalizedTelescope
