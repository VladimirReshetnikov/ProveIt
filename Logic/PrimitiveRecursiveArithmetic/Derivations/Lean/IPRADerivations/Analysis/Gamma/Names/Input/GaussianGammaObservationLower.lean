import IPRADerivations.Analysis.Gamma.EulerProducts.Approximants.Inverse.GaussianGammaEulerReciprocalInverse
import IPRADerivations.Analysis.Names.Rates.Order.GaussianRationalLowerPerturbation

/-!
# Quantitative separation for the original Gamma observations

A named inverse with exact bound `A/B` gives a lower bound
`(B/A) max(0,1-K/2^p)` on the actual samples of its partner, where
`K` is computed from the original product clock. This supplies the
separation on both C14 denominator programs and the corresponding
nonvanishing bound for the actual Gamma reciprocal.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaObservationLower

open_ipra
open GaussianRationalLowerBounds (lower lower_congr lower_from_representation)
open GaussianRationalLowerPerturbation (lower_near_unit fractional_factor_lower)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalL1 (rawDen rawGaussian raw_den_positive raw_represents)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalReciprocal (qone)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_triangle_same)
open GaussianNameArithmetic (multiplyF multiplyData)
open GaussianNameRingLaws (oneF one_at multiply_sample_error multiply_commutative)
open GaussianNameEquivalence (crossEquivalent cross_to_diagonal diagonal_at cross_symm cross_trans)
open GaussianEuclideanDistanceName (pointCN)
open GaussianExponentialSmallPerturbation (smallSamples small_samples_at)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianBoundedInverseApartness (productError)
open GaussianGammaReciprocalInverse (lambdaNumerator lambdaDenominator lambda_positive source gammaF gammaData)
open GaussianGammaFiniteApproximantName (qF qData q_regular)
open GaussianGammaC9Bound (majorant)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def observationLower (f g : PR 2) (x y A B p : PTm n) : Fm PTm n :=
  lower (ap2 f p x) (monus (unit p) (productError f g x y)*B) (unit p*A)

theorem zero_lower (q D : PTm n) (h : Γ ⊢[PRAAx] le one D) : Γ ⊢[PRAAx] lower q zero D :=
  lower_from_representation q (rawGaussian q) (rawDen q) zero D (raw_den_positive q) h (raw_represents q)
    (le_congr (by ipra_ring) (.eqRefl _) (zero_le _))

theorem inverse_observation_lower (f g : PR 2) (x y r A B p : PTm n)
    (ha : Γ ⊢[PRAAx] le one A) (hb : Γ ⊢[PRAAx] le one B)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y)
    (bound : Γ ⊢[PRAAx] bounded (ap2 g p y) A B)
    (law : Γ ⊢[PRAAx] crossEquivalent (multiplyF f g) oneF (multiplyData f g x y) r) :
    Γ ⊢[PRAAx] observationLower f g x y A B p := by
  let U := unit p
  let K := productError f g x y
  let a := ap2 f p x
  let b := ap2 g p y
  have hU := unit_positive (Γ := Γ) p
  have diagonal := diagonal_at _ _ _ _ p (cross_to_diagonal _ _ _ _ law)
  have close : Γ ⊢[PRAAx] distanceBounded (qmul a b) qone K U :=
    distance_triangle_same _ _ _ _ _ _ hU
      (distance_symmetric _ _ _ _ hU (multiply_sample_error f g x y p hf hg))
      (distance_congr (.eqRefl _) (one_at p r) (.eqRefl _) (.eqRefl _) diagonal)
  refine .orE (le_total K U) ?_ ?_
  · exact fractional_factor_lower _ _ _ _ _ _ hU.wk ha.wk hb.wk
      (lower_near_unit _ _ _ hU.wk Prf.hyp0 close.wk) bound.wk
  · have e : (le U K) :: Γ ⊢[PRAAx] monus U K ≐ zero := Prf.hyp0
    exact lower_congr (.eqRefl _) ((congrMul e (.eqRefl B)).eqTrans (zero_mul B)).eqSymm (.eqRefl _)
      (zero_lower a (U*A) (positive_product _ _ hU.wk ha.wk))

theorem reciprocal_gamma_lower (p z R B a d : PTm n) (h : Γ ⊢[PRAAx] source z R B a d) : Γ ⊢[PRAAx]
    observationLower GaussianGammaC7Name.nameF GaussianGammaReciprocalInverse.inverseF
      (GaussianGammaC7Name.data z R B) (GaussianGammaReciprocalInverse.inverseData z R B)
      (lambdaDenominator R d) (lambdaNumerator R a) p := by
  have l := lambda_positive R a d h.andE₂.andE₁ h.andE₂.andE₂.andE₁
  exact inverse_observation_lower _ _ _ _ _ _ _ _ l.andE₂ l.andE₁
    (GaussianGammaC7Name.name_regular z R B h.andE₁) (GaussianGammaReciprocalInverse.inverse_regular z R B h.andE₁)
    (GaussianGammaReciprocalInverse.inverse_sample_bound p z R B a d h)
    (GaussianGammaReciprocalInverse.inverse_product z R B a d h)

theorem reciprocal_euler_lower (p z R B a d N : PTm n)
    (h : Γ ⊢[PRAAx] GaussianGammaEulerReciprocalInverse.source z R B a d N) : Γ ⊢[PRAAx]
    observationLower qF GaussianGammaEulerReciprocalInverse.inverseF (qData z B N)
      (GaussianGammaEulerReciprocalInverse.inverseData z R B N) (lambdaDenominator R d) (lambdaNumerator R a) p := by
  have g := h.andE₁
  have q := GaussianGammaEulerReciprocalInverse.folded_source z R B a d N h
  have pos := (GaussianGammaFoldedMajorantExponent.tail_source z R B N q).andE₂.andE₁
  have l := lambda_positive R a d g.andE₂.andE₁ g.andE₂.andE₂.andE₁
  exact inverse_observation_lower _ _ _ _ _ _ _ _ l.andE₂ l.andE₁ (q_regular z B N pos)
    (GaussianGammaEulerReciprocalInverse.inverse_regular z R B N q)
    (GaussianGammaEulerReciprocalInverse.inverse_sample_bound p z R B a d N h)
    (GaussianGammaEulerReciprocalInverse.inverse_product z R B a d N h)

theorem majorant_positive (R : PTm n) (hR : Γ ⊢[PRAAx] le one R) : Γ ⊢[PRAAx] le one (majorant R) :=
  positive_product _ _ (positive_product _ _ hR
    (GaussianFactorBudget.power_positive (one+R) (two*R) (le_add_right _ _)))
    (GaussianFactorBudget.power_positive (num 3) _ (zero_lt_succ two))

theorem original_gamma_lower (p z R B a d : PTm n) (h : Γ ⊢[PRAAx] source z R B a d) : Γ ⊢[PRAAx]
    observationLower gammaF GaussianGammaC7Name.nameF (gammaData z R B d) (GaussianGammaC7Name.data z R B) (majorant R) one p := by
  let f := GaussianGammaC7Name.nameF
  let x := GaussianGammaC7Name.data z R B
  let y := gammaData z R B d
  have hf := GaussianGammaC7Name.name_regular z R B h.andE₁
  have hg := GaussianGammaReciprocalInverse.gamma_regular z R B a d h
  have comm := cross_symm _ _ _ _ (multiply_commutative f gammaF x y hf hg)
  have law := cross_trans _ _ _ _ _ _ comm (GaussianGammaReciprocalInverse.gamma_product z R B a d h)
  exact inverse_observation_lower _ _ _ _ _ _ _ _ (majorant_positive R h.andE₁.andE₁) (le_refl _)
    hg hf (GaussianGammaC9Bound.reciprocal_sample_bound p z R B h.andE₁) law

theorem original_C14_P_observation_separation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      observationLower GaussianGammaC7Name.nameF GaussianGammaReciprocalInverse.inverseF
        (GaussianGammaC7Name.data (var 0) (var 1) (var 2)) (GaussianGammaReciprocalInverse.inverseData (var 0) (var 1) (var 2))
        (lambdaDenominator (var 1) (var 4)) (lambdaNumerator (var 1) (var 3)) (var 5)) :=
  closeUniv 6 (.impI (reciprocal_gamma_lower _ _ _ _ _ _ Prf.hyp0))

theorem original_C14_Q_observation_separation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (GaussianGammaEulerReciprocalInverse.source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      observationLower qF GaussianGammaEulerReciprocalInverse.inverseF (qData (var 0) (var 2) (var 5))
        (GaussianGammaEulerReciprocalInverse.inverseData (var 0) (var 1) (var 2) (var 5))
        (lambdaDenominator (var 1) (var 4)) (lambdaNumerator (var 1) (var 3)) (var 6)) :=
  closeUniv 7 (.impI (reciprocal_euler_lower _ _ _ _ _ _ _ Prf.hyp0))

theorem original_Gamma_nonvanishing_observations_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ observationLower gammaF GaussianGammaC7Name.nameF
      (gammaData (var 0) (var 1) (var 2) (var 4)) (GaussianGammaC7Name.data (var 0) (var 1) (var 2))
      (majorant (var 1)) one (var 5)) :=
  closeUniv 6 (.impI (original_gamma_lower _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaObservationLower
