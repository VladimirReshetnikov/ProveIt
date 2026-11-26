import IPRADerivations.Analysis.Trigonometry.GaussianNamedSinc

/-!
# Quadratic bounds on the original sinc name

At its actual normalization clock each named observation is exactly
a canonical finite factorial sum. Thus the small-disk bounds pass to
the name with the original constants.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianNamedSincQuadraticBounds

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianNamedSincSamples (argument argumentClock cutoff sampleSize value value_nonempty value_canonical sample_bound)
open GaussianNamedSinc (nameF data modulus rawF raw_at sample_near)
open GaussianNamedSineTaylor (rawData)
open GaussianRationalHorner (qmul canonical positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianRationalReciprocal (qone bound_congr)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianApproximateInverseDistance (multiply_distance)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNameEquivalence (crossEquivalent)
open GaussianNamedDiagonalRate (diagonalRate cross_of_diagonal_rate)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def query (f : PR 2) (R x p : PTm n) : PTm n :=
  GaussianFastValueCut.exponent (modulus f R x) p

def observationBound (f : PR 2) (x A B : PTm n) : Fm PTm n :=
  .all (bounded (ap2 f (var 0) (Syn.shift x)) (Syn.shift A) (Syn.shift B))

@[simp] theorem subst_observationBound {l : ℕ} (σ : Fin n → PTm l) (f : PR 2) (x A B : PTm n) :
    (observationBound f x A B).subst σ =
      observationBound f (Syn.subst σ x) (Syn.subst σ A) (Syn.subst σ B) := by
  simp [observationBound, Syn.subst_shift, Syn.shift_subst]

theorem observation_bound_at (f : PR 2) (x A B p : PTm n)
    (h : Γ ⊢[PRAAx] observationBound f x A B) :
    Γ ⊢[PRAAx] bounded (ap2 f p x) A B := by simpa [observationBound] using h.allE p

theorem exact_sample (f : PR 2) (R x p : PTm n) : Γ ⊢[PRAAx]
    ap2 (nameF f) p (data f R x) ≐ value f R x (query f R x p) :=
  (GaussianFastValueCut.name_at (rawF f) (modulus f R x) (rawData R x) p).eqTrans
    ((GaussianNameArithmetic.recode_congr (raw_at f R x (query f R x p))).eqTrans
      (GaussianExponentialReference.recode_fixed _ (value_canonical f R x (query f R x p))))

theorem quadratic_bound (f : PR 2) (R x A B p : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hAB : Γ ⊢[PRAAx] le A B)
    (h : Γ ⊢[PRAAx] observationBound f x A B) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (nameF f) p (data f R x)) qone (A*A) (two*(B*B)) :=
  distance_congr (exact_sample f R x p).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (sample_near f R x (query f R x p) A B hB hAB
      (observation_bound_at f x A B (argumentClock R (query f R x p)) h))

theorem unit_disk_bound (f : PR 2) (R x A B p : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hAB : Γ ⊢[PRAAx] le A B)
    (h : Γ ⊢[PRAAx] observationBound f x A B) :
    Γ ⊢[PRAAx] bounded (ap2 (nameF f) p (data f R x)) two one := by
  let q := query f R x p
  have a := observation_bound_at f x A B (argumentClock R q) h
  have unitBound := bounded_radius_mono _ _ _ one one hB (le_refl one)
    (le_congr ((mul_comm A one).eqTrans (one_mul A)).eqSymm (one_mul B).eqSymm hAB) a
  have finite := GaussianScalarSincTaylorBounds.unit_disk_sinc_bound (argument f R x q)
    (pred (cutoff R q)) unitBound
  exact bound_congr ((exact_sample f R x p).eqTrans (value_nonempty f R x q)).eqSymm (.eqRefl _) (.eqRefl _) finite

theorem uniform_bound (f : PR 2) (R x p : PTm n) (h : Γ ⊢[PRAAx] GaussianRadiusExponentialName.input f R x) :
    Γ ⊢[PRAAx] bounded (ap2 (nameF f) p (data f R x)) (sampleSize f R x) one :=
  bound_congr (exact_sample f R x p).eqSymm (.eqRefl _) (.eqRefl _)
    (sample_bound f R x (query f R x p) h)

theorem square_quadratic_bound (f : PR 2) (R x A B p : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hAB : Γ ⊢[PRAAx] le A B)
    (h : Γ ⊢[PRAAx] observationBound f x A B) :
    Γ ⊢[PRAAx] distanceBounded (qmul (ap2 (nameF f) p (data f R x)) (ap2 (nameF f) p (data f R x)))
      qone (num 3*(A*A)) (two*(B*B)) := by
  let a := ap2 (nameF f) p (data f R x)
  let D := two*(B*B)
  let N := A*A
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ (le_succ_self one) (positive_product _ _ hB hB)
  have ha : Γ ⊢[PRAAx] canonical a :=
    GaussianFastValueCut.name_canonical (rawF f) (modulus f R x) (rawData R x) p
  have small := quadratic_bound f R x A B p hB hAB h
  have step := multiply_distance a a qone two N D hD (unit_disk_bound f R x A B p hB hAB h) small
  have id : Γ ⊢[PRAAx] qmul a qone ≐ a :=
    (qmul_commutative a qone).eqTrans (GaussianPolynomialDeterminantTerms.one_mul_canonical a ha)
  have tail := distance_congr id.eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) small
  exact distance_congr (.eqRefl _) (.eqRefl _) (by dsimp only [N]; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hD step tail)

theorem zero_is_one (f : PR 2) (R x : PTm n)
    (hf : Γ ⊢[PRAAx] GaussianRadiusExponentialName.input f R x)
    (h : Γ ⊢[PRAAx] observationBound f x zero one) :
    Γ ⊢[PRAAx] crossEquivalent (nameF f) constantF (data f R x) qone := by
  apply cross_of_diagonal_rate _ _ _ _ zero (GaussianNamedSinc.name_regular f R x hf) (constant_regular _)
  refine .allI ?_
  let C := Γ.map Fm.shift
  let Rt := Syn.shift R
  let xt := Syn.shift x
  let p : PTm (n+1) := var 0
  have ht : C ⊢[PRAAx] observationBound f xt zero one := by
    simpa [Fm.shift, Syn.shift, C, xt, one] using h.shift
  have hl := quadratic_bound f Rt xt zero one p (le_refl one) (zero_le one) ht
  have hD : C ⊢[PRAAx] le one (two*(one*one)) :=
    positive_product _ _ (le_succ_self one) (positive_product _ _ (le_refl one) (le_refl one))
  have hl' := distance_congr (.eqRefl _) (constant_at p qone).eqSymm (zero_mul zero) (.eqRefl _) hl
  have result := distance_radius_mono _ _ _ _ _ _ hD (unit_positive p)
    (le_congr (zero_mul (unit p)).eqSymm (zero_mul (two*(one*one))).eqSymm (le_refl zero)) hl'
  simpa [diagonalRate, Syn.shift, C, Rt, xt, p, GaussianRationalReciprocal.qone] using result

theorem actual_named_sinc_quadratic_bound_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      ((le one (var 2) ⋏ le (var 3) (var 2)) ⟶ observationBound f (var 1) (var 3) (var 2) ⟶
        distanceBounded (ap2 (nameF f) (var 0) (data f (var 4) (var 1))) qone
          (var 3*var 3) (two*(var 2*var 2))) :=
  closeUniv 5 (.impI (.impI (quadratic_bound f _ _ _ _ _ Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianNamedSincQuadraticBounds
