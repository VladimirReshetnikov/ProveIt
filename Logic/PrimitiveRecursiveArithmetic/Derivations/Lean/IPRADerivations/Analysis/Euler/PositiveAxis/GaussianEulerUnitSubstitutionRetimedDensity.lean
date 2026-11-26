import IPRADerivations.Analysis.Euler.PositiveAxis.GaussianEulerUnitSubstitutionCompactName

/-!
# Retiming the actual original compact density at its unchanged grid count

The original count is retained exactly. Any later power/decay row query
preserves the original finite and mesh budgets, hence the full original
Euler compact readback with independently requested output precision.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerUnitSubstitutionRetimedDensity

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerUnitSubstitutionCompactName (source count rowQuery stage refinement refinement_positive count_positive count_budget)
open GaussianEulerUnitSubstitutionDensity (density numerator denominator)
open GaussianEulerCompactPowerMajorant (majorant)
open GaussianEulerIntegrationByPartsGridObservation (rowCost)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianCompactRiemannName (mesh precision)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

theorem old_count_unit_lower (t R C E T : PTm n) : Γ ⊢[PRAAx] le (unit t) (count t R C E T) := by
  let L := GaussianEulerCompactModulus.lipschitz R E T
  have grow : Γ ⊢[PRAAx] le t (stage t+num 6) := le_of_eq_add (d := num 4+num 6) (by unfold stage; ipra_ring)
  have first := GaussianExponentialReference.unit_monotone (Γ := Γ) grow
  have second : Γ ⊢[PRAAx] le (unit (stage t+num 6)) (mesh (stage t) L T) :=
    le_of_eq_add (d := unit (stage t+num 6)*(L*T*T)) (by unfold mesh; ipra_ring)
  have third : Γ ⊢[PRAAx] le (mesh (stage t) L T) (count t R C E T) :=
    le_congr (one_mul _) (.eqRefl _) (mul_le_mul_right (mesh (stage t) L T) (refinement_positive t R C E T))
  exact le_trans first (le_trans second third)

theorem finite_budget (t r z R B a C E T : PTm n) (hs : Γ ⊢[PRAAx] source z R B a C E T)
    (hr : Γ ⊢[PRAAx] le (rowQuery t R C E T) r) : Γ ⊢[PRAAx]
    le (numerator r R E T C (count t R C E T)*unit (stage t))
      (two*denominator r E (count t R C E T)) := by
  let N := count t R C E T
  let U := unit r
  let P := unit (stage t)
  let K := majorant R E T
  have hE := hs.andE₁.andE₁.andE₂.andE₁
  have width : Γ ⊢[PRAAx] le C (E*T) := le_trans (le_add_left C a) hs.andE₁.andE₂.andE₂
  have curv : Γ ⊢[PRAAx] le (num 3*K*C*C*P) N := count_budget t R C E T
  have old : Γ ⊢[PRAAx] le ((num 20*K*N+T*rowCost R E T)*P) (unit (rowQuery t R C E T)) :=
    le_trans (GaussianFastValueCut.query_budget _ _) (GaussianExponentialReference.unit_monotone (le_add_left _ _))
  have obs : Γ ⊢[PRAAx] le ((num 20*K*N+T*rowCost R E T)*P) U :=
    le_trans old (GaussianExponentialReference.unit_monotone hr)
  have e2 : Γ ⊢[PRAAx] le one (E*E) := positive_product _ _ hE hE
  unfold numerator denominator
  ipra_le 𝔞 U*sl curv+𝔞 (E*E*N)*sl obs+𝔞 (N*U)*sl e2+𝔞 (rowCost R E T*E*N*P)*sl width

theorem retimed_observation_to_old (t r z R B a C E T : PTm n) (hs : Γ ⊢[PRAAx] source z R B a C E T)
    (hr : Γ ⊢[PRAAx] le (rowQuery t R C E T) r) : Γ ⊢[PRAAx]
    distanceBounded (density r (count t R C E T) z B a C E)
      (ap2 GaussianEulerCompactAdditivity.nameF (stage t) (GaussianEulerCompactAdditivity.data z R B a C E T))
      (num 5) (unit (stage t)) := by
  let s := stage t
  let N := count t R C E T
  have hE := hs.andE₁.andE₁.andE₂.andE₁
  have hN := count_positive (Γ := Γ) t R C E T
  have hd := positive_product _ _ (positive_product _ _ (positive_product _ _ hE hE) hN) (unit_positive r)
  have finite := GaussianEulerUnitSubstitutionDensity.original_finite_bound r z R B a C E T N
    (GaussianEulerUnitSubstitutionCompactName.finite_source t z R B a C E T hs)
  have first := distance_symmetric _ _ _ _ (unit_positive s)
    (distance_radius_mono _ _ _ _ two (unit s) hd (unit_positive s) (finite_budget t r z R B a C E T hs hr) finite)
  have minPrecision : Γ ⊢[PRAAx] le (precision s T) r := le_trans (le_add_right _ _) hr
  have old := GaussianCompactMeshIndependence.arbitrary_refinement GaussianEulerIntegrandName.evaluatorF s r
    (refinement t R C E T) a C E (GaussianEulerCompactModulus.lipschitz R E T) T (GaussianEulerIntegrandName.fixedData z B)
    (GaussianEulerCompactAdditivity.compact_input z R B a C E T hs.andE₁) (refinement_positive t R C E T) minPrecision
  have grown : Γ ⊢[PRAAx] le (unit s) (unit (s+num 6)) := GaussianExponentialReference.unit_monotone (le_add_right _ _)
  have second := distance_congr (.eqRefl _)
    (GaussianCompactRiemannName.name_at GaussianEulerIntegrandName.evaluatorF s a C E
      (GaussianEulerCompactModulus.lipschitz R E T) T (GaussianEulerIntegrandName.fixedData z B)).eqSymm (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ _ (num 3) (unit s) (unit_positive _) (unit_positive s)
      (le_congr (mul_comm _ _) (mul_comm _ _) (mul_le_mul_right (num 3) grown)) old)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ (unit_positive s) first second)

theorem original_observations (t r q z R B a C E T : PTm n) (hs : Γ ⊢[PRAAx] source z R B a C E T)
    (hr : Γ ⊢[PRAAx] le (rowQuery t R C E T) r) : Γ ⊢[PRAAx]
    distanceBounded (density r (count t R C E T) z B a C E)
      (ap2 GaussianEulerCompactAdditivity.nameF q (GaussianEulerCompactAdditivity.data z R B a C E T))
      (unit t+unit q) (unit t*unit q) := by
  let s := stage t
  have ht := unit_positive (Γ := Γ) t
  have hq := unit_positive (Γ := Γ) q
  have hs' := unit_positive (Γ := Γ) s
  have first := distance_radius_mono _ _ _ _ (num 5*unit q) (unit s*unit q) hs' (positive_product _ _ hs' hq)
    (le_of_eq_add (d := zero) (by ipra_ring)) (retimed_observation_to_old t r z R B a C E T hs hr)
  have second := GaussianNameEquivalence.point_at GaussianEulerCompactAdditivity.nameF
    (GaussianEulerCompactAdditivity.data z R B a C E T) s q (GaussianEulerCompactAdditivity.name_regular z R B a C E T hs.andE₁)
  have joined := distance_triangle_same _ _ _ _ _ _ (positive_product _ _ hs' hq) first second
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hs' hq) (positive_product _ _ ht hq)
    (by ipra_le (𝔞 (unit q)^2)*sl (GaussianEulerUnitSubstitutionCompactName.stage_budget (Γ := Γ) t)) joined

theorem original_sample_observations (t r q z R B a C E T : PTm n) (hs : Γ ⊢[PRAAx] source z R B a C E T)
    (hr : Γ ⊢[PRAAx] le (rowQuery t R C E T) r) : Γ ⊢[PRAAx]
    distanceBounded (density r (count t R C E T) z B a C E)
      (GaussianCompactRiemannName.sample GaussianEulerIntegrandName.evaluatorF q a C E
        (GaussianEulerCompactModulus.lipschitz R E T) T (GaussianEulerIntegrandName.fixedData z B))
      (unit t+unit q) (unit t*unit q) :=
  distance_congr (.eqRefl _)
    (GaussianCompactRiemannName.name_at GaussianEulerIntegrandName.evaluatorF q a C E
      (GaussianEulerCompactModulus.lipschitz R E T) T (GaussianEulerIntegrandName.fixedData z B))
    (.eqRefl _) (.eqRefl _) (original_observations t r q z R B a C E T hs hr)

theorem actual_original_density_count_growth_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le (unit (var 0)) (count (var 0) (var 1) (var 2) (var 3) (var 4))) :=
  closeUniv 5 (old_count_unit_lower _ _ _ _ _)

theorem actual_original_retimed_density_compact_readback_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    ((source (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) ⋏
      le (rowQuery (var 0) (var 4) (var 7) (var 8) (var 9)) (var 1)) ⟶
      distanceBounded (density (var 1) (count (var 0) (var 4) (var 7) (var 8) (var 9)) (var 3) (var 5) (var 6) (var 7) (var 8))
      (ap2 GaussianEulerCompactAdditivity.nameF (var 2) (GaussianEulerCompactAdditivity.data (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9)))
      (unit (var 0)+unit (var 2)) (unit (var 0)*unit (var 2))) :=
  closeUniv 10 (.impI (original_observations _ _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerUnitSubstitutionRetimedDensity
