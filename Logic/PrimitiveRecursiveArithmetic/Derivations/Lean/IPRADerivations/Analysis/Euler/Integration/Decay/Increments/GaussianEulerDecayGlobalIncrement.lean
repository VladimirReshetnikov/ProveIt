import IPRADerivations.Analysis.Euler.Integration.Decay.Increments.GaussianEulerDecayGlobalTaylor
import IPRADerivations.Analysis.Euler.Integration.Decay.Quadrature.GaussianEulerDecayMesh
import IPRADerivations.Analysis.Stirling.Binet.Laplace.Integrands.GaussianBinetLaplaceDomination

/-!
# Actual real decay products at independently encoded parameters

The exact exponential addition law is read at a common observation
clock. The bound includes zero numerators. The nonnegative real
representatives of the unshifted and shifted decay may replace the
corresponding original exponential observations.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

namespace LeanProofs.IPRA.Analysis.GaussianEulerDecayGlobalIncrement

open_ipra
open GaussianBinetLaplaceDomination (realDecay)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianEulerDecayMesh (observation subst_observation observation_rescale)
open GaussianEulerDecayOrder (signedTime original_decay_nonnegative_representative)
open GaussianEulerIntegrandName (decayF decayData decayPoint)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianNameArithmetic (multiplyF multiplyData multiplyModulus multiply_at product_distance)
open GaussianNameEquivalence (cross_at point_at)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (qmul positive_product qmul_canonical)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalReciprocal (bound_congr)
open GaussianRealExponentialPositiveRepresentative (positiveF positiveData)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)

theorem observation_bound (p a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] bounded (observation a b p) two one := by
  have hu := unit_positive (Γ := Γ) p
  exact bounded_radius_mono _ _ _ _ _ hu (le_refl one) (by ipra_le sl hu)
    (GaussianBinetLaplaceScalarMajorant.original_decay_unit_bound p a b hb)

theorem positive_observation_distance (p a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] distanceBounded (realDecay p a b) (observation a b p) two (unit p) := by
  have hU := unit_positive (Γ := Γ) p
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hU hU) hU
    (le_of_eq_add (d := zero) (by ipra_ring))
    (cross_at positiveF decayF (positiveData (signedTime a b)) (decayData a b) p p
      (original_decay_nonnegative_representative a b hb))

theorem positive_observation_bound (p a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] bounded (realDecay p a b) (num 4) one := by
  have hU := unit_positive (Γ := Γ) p
  have b := GaussianReconstructionRoots.norm_from_distance _ _ two (unit p) two one hU (le_refl one)
    (positive_observation_distance p a b hb) (observation_bound p a b hb)
  exact bounded_radius_mono _ _ _ _ _ (positive_product _ _ hU (le_refl one)) (le_refl one)
    (by ipra_le 2*sl hU) b

private theorem decay_later (p q a b : PTm n) (hpq : Γ ⊢[PRAAx] le p q) :
    Γ ⊢[PRAAx] distanceBounded (observation a b q) (observation a b p) two (unit p) := by
  let x := decayPoint a b
  have r := GaussianRadiusExponentialName.name_regular (Γ := Γ) constantF _ x
    (GaussianGammaFiniteApproximantName.exponential_input constantF x (constant_regular x))
  have late := GaussianExponentialReference.unit_monotone hpq
  have hP := unit_positive (Γ := Γ) p
  have hQ := unit_positive (Γ := Γ) q
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hQ hP) hP
    (by ipra_le 𝔞(unit p)*sl late) (point_at decayF (decayData a b) q p r)

theorem product_observation (p a b c d : PTm n)
    (hb : Γ ⊢[PRAAx] le one b) (hd : Γ ⊢[PRAAx] le one d) :
    Γ ⊢[PRAAx] distanceBounded (observation (a*d+c*b) (b*d) p)
      (qmul (observation a b p) (observation c d p)) (num 10) (unit p) := by
  let x := decayData a b
  let y := decayData c d
  let q := GaussianFastValueCut.exponent (multiplyModulus decayF decayF x y) p
  let z := ap2 (multiplyF decayF decayF) p (multiplyData decayF decayF x y)
  have hQ : Γ ⊢[PRAAx] le p q := le_add_right _ _
  have hP := unit_positive (Γ := Γ) p
  have read : Γ ⊢[PRAAx] z ≐ qmul (observation a b q) (observation c d q) :=
    (multiply_at decayF decayF x y p).eqTrans
      (GaussianExponentialReference.recode_fixed _ (qmul_canonical _ _))
  have between := product_distance (observation a b q) (observation a b p) (observation c d q) (observation c d p)
    two two (unit p) two two hP (decay_later p q a b hQ) (decay_later p q c d hQ)
    (observation_bound q c d hd) (observation_bound p a b hb)
  have original := cross_at decayF (multiplyF decayF decayF) (decayData (a*d+c*b) (b*d))
    (multiplyData decayF decayF x y) p p
    (GaussianNameEquivalence.cross_symm _ _ _ _ (GaussianEulerDecayAddition.original_decay_add a b c d hb hd))
  have toZ : Γ ⊢[PRAAx] distanceBounded (observation (a*d+c*b) (b*d) p) z two (unit p) :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hP hP) hP (le_of_eq_add (d := zero) (by ipra_ring)) original
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hP toZ (distance_congr read.eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) between))

private theorem shift_observation (p X D H Q A B : PTm n)
    (hD : Γ ⊢[PRAAx] le one D) (hQ : Γ ⊢[PRAAx] le one Q) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] observation ((X*Q+H*D)*A) ((D*Q)*B) p ≐
      observation ((X*A)*(Q*B)+(H*A)*(D*B)) ((D*B)*(Q*B)) p := by
  let a := (X*Q+H*D)*A
  let b := (D*Q)*B
  have hb := positive_product _ _ (positive_product _ _ hD hQ) hB
  refine (observation_rescale a b B p hb hB).eqSymm.eqTrans ?_
  have e₁ : Γ ⊢[PRAAx] a*B ≐ (X*A)*(Q*B)+(H*A)*(D*B) := by dsimp only [a]; ipra_ring
  have e₂ : Γ ⊢[PRAAx] b*B ≐ (D*B)*(Q*B) := by dsimp only [b]; ipra_ring
  simpa only [subst_observation,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
      Prf.eqCongr (observation (var 0) (var 1) (var 2) : PTm 3)
        (σ := ![a*B,b*B,p]) (σ' := ![(X*A)*(Q*B)+(H*A)*(D*B),(D*B)*(Q*B),p])
        (fun i => by fin_cases i; exact e₁; exact e₂; exact .eqRefl _)

theorem shifted_positive_product (p X D H Q A B : PTm n)
    (hD : Γ ⊢[PRAAx] le one D) (hQ : Γ ⊢[PRAAx] le one Q) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] distanceBounded (realDecay p ((X*Q+H*D)*A) ((D*Q)*B))
      (qmul (realDecay p (X*A) (D*B)) (observation (H*A) (Q*B) p))
      (num 16) (unit p) := by
  let a := X*A
  let b := D*B
  let c := H*A
  let d := Q*B
  let x := observation a b p
  let y := observation c d p
  let x' := realDecay p a b
  have hb := positive_product _ _ hD hB
  have hd := positive_product _ _ hQ hB
  have hp := unit_positive (Γ := Γ) p
  have first := positive_observation_distance p ((X*Q+H*D)*A) ((D*Q)*B)
    (positive_product _ _ (positive_product _ _ hD hQ) hB)
  have prod := distance_congr (shift_observation p X D H Q A B hD hQ hB).eqSymm
    (.eqRefl _) (.eqRefl _) (.eqRefl _) (product_observation p a b c d hb hd)
  have last := GaussianApproximateInverseDistance.multiply_distance y x x' two two (unit p) hp
    (observation_bound p c d hd)
    (distance_symmetric _ _ _ _ hp (positive_observation_distance p a b hb))
  have last' := distance_congr (GaussianRationalPowerAlgebra.qmul_commutative y x)
    (GaussianRationalPowerAlgebra.qmul_commutative y x') (.eqRefl _) (.eqRefl _) last
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hp (distance_triangle_same _ _ _ _ _ _ hp first prod) last')

theorem actual_global_shifted_decay_product_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    ((le one (var 2) ⋏ le one (var 4)) ⋏ le one (var 6) ⟶
      distanceBounded (realDecay (var 0) ((var 1*var 4+var 3*var 2)*var 5) ((var 2*var 4)*var 6))
        (qmul (realDecay (var 0) (var 1*var 5) (var 2*var 6)) (observation (var 3*var 5) (var 4*var 6) (var 0)))
        (num 16) (unit (var 0))) :=
  closeUniv 7 (.impI (shifted_positive_product _ _ _ _ _ _ _ Prf.hyp0.andE₁.andE₁ Prf.hyp0.andE₁.andE₂ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerDecayGlobalIncrement
