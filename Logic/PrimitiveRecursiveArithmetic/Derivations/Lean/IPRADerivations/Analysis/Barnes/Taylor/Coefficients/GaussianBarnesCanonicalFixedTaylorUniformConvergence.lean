import IPRADerivations.Analysis.Barnes.Taylor.Coefficients.GaussianBarnesCanonicalFixedTaylorCoefficientName
import IPRADerivations.Analysis.Barnes.Taylor.Coefficients.GaussianBarnesCanonicalTaylorProductUniformGap
import IPRADerivations.Analysis.Names.Rates.GaussianNamedLipschitzRate

/-!
# Disk-uniform convergence of the original fixed-cutoff coefficient name

At any observation clock the two original names compare with a pair of
later raw observations, whose prefactor clock meets both schedules.
The static cutoff estimate controls the gap between the raw observations.
Regularity removes the auxiliary observation error and retains the
disk-only cutoff for the actual names.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFixedTaylorUniformConvergence

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesCanonicalHigherRows (previous)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalTaylorProductCoefficientCauchy (productCoefficient)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianExponentialReference (unit_monotone)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedLipschitzRate (diagonalNumerator diagonalDenominator diagonalEnvelope)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "C" => GaussianBarnesCanonicalTaylorProductCoefficientName.nameF
local notation "cd" => GaussianBarnesCanonicalTaylorProductCoefficientName.data
local notation "F" => GaussianBarnesCanonicalFixedTaylorCoefficientName.nameF
local notation "fd" => GaussianBarnesCanonicalFixedTaylorCoefficientName.data
local notation "cutoff" => GaussianBarnesCanonicalTaylorProductUniformGap.cutoff


theorem diagonal_at (p k z R B r M e : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (he : Γ ⊢[PRAAx] le e (previous M)) (hr : Γ ⊢[PRAAx] le (cutoff p R M e) r) : Γ ⊢[PRAAx]
    distanceBounded (ap2 C k (cd z R B M e)) (ap2 F k (fd z R B r M e))
      (diagonalNumerator one (unit p) two k) (diagonalDenominator (unit p) k) := by
  let t := GaussianBarnesCanonicalTaylorProductCoefficientName.clock k z R B M e
  let q₀ := GaussianBarnesCanonicalExponentTaylorRetainedCoefficient.precision t R
  let q₁ := GaussianBarnesCanonicalTaylorProductUniformGap.precision p R M e
  let s₀ := GaussianBarnesCanonicalExponentTaylorRetainedCoefficient.cutoff t R M
  let s₁ := cutoff p R M e
  let q := q₀+q₁
  let s := s₀+s₁
  let left := GaussianBarnesCanonicalTaylorProductCoefficientName.sample k z R B M e
  let u := productCoefficient q z R B s M e
  let v := productCoefficient q z R B r M e
  let right := GaussianBarnesCanonicalFixedTaylorCoefficientName.sample k z R B r M e
  let D := unit p*unit k
  have hk := GaussianBarnesCanonicalTaylorProductCoefficientName.sample_ready (Γ := Γ) k z R B M e
  have hu := GaussianBarnesCanonicalTaylorProductUniformGap.sample_ready (Γ := Γ) p R M e
  have clock₀ : Γ ⊢[PRAAx] le (GaussianBarnesCanonicalExponentTaylorRetainedCoefficient.prefactorGain R*unit t) (unit q) :=
    le_trans hk.andE₁ (unit_monotone (le_add_right q₀ q₁))
  have clock₁ : Γ ⊢[PRAAx] le (GaussianBarnesCanonicalExponentTaylorRetainedCoefficient.prefactorGain R*unit (GaussianBarnesCanonicalTaylorProductUniformGap.clock p R M e)) (unit q) :=
    le_trans hu.andE₁ (unit_monotone (le_add_left q₁ q₀))
  have hleft : Γ ⊢[PRAAx] distanceBounded left u one (unit k) :=
    GaussianBarnesCanonicalTaylorProductCoefficientName.ready_gap k q₀ q z R B s₀ s M e hz he hk (.andI clock₀ (le_add_right s₀ s₁))
  have hmiddle : Γ ⊢[PRAAx] distanceBounded u v one (unit p) :=
    GaussianBarnesCanonicalTaylorProductUniformGap.ready_gap p q q z R B s r M e hz he (.andI clock₁ (le_add_left s₁ s₀)) (.andI clock₁ hr)
  have hright : Γ ⊢[PRAAx] distanceBounded v right one (unit k) :=
    GaussianBarnesCanonicalFixedTaylorCoefficientName.ready_gap k q q₀ z R B r M e hz he clock₀ (GaussianBarnesCanonicalFixedTaylorCoefficientName.sample_ready k z R B M e)
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ (unit_positive p) (unit_positive k)
  have scaled_left : Γ ⊢[PRAAx] distanceBounded left u (unit p) D :=
    distance_radius_mono _ _ _ _ _ _ (unit_positive k) hD
      (le_congr (one_mul D).eqSymm (.eqRefl _) (le_refl D)) hleft
  have scaled_middle : Γ ⊢[PRAAx] distanceBounded u v (unit k) D :=
    distance_radius_mono _ _ _ _ _ _ (unit_positive p) hD
      (le_of_eq_add (d := zero) (by dsimp [D]; ipra_ring)) hmiddle
  have scaled_right : Γ ⊢[PRAAx] distanceBounded v right (unit p) D :=
    distance_radius_mono _ _ _ _ _ _ (unit_positive k) hD
      (le_congr (one_mul D).eqSymm (.eqRefl _) (le_refl D)) hright
  exact distance_congr (GaussianBarnesCanonicalTaylorProductCoefficientName.sample_at k z R B M e).eqSymm (GaussianBarnesCanonicalFixedTaylorCoefficientName.sample_at k z R B r M e).eqSymm
    (by unfold diagonalNumerator; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hD
      (distance_triangle_same _ _ _ _ _ _ hD scaled_left scaled_middle) scaled_right)

theorem cofinal_rate (p z R B r M e : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (he : Γ ⊢[PRAAx] le e (previous M)) (hr : Γ ⊢[PRAAx] le (cutoff p R M e) r) : Γ ⊢[PRAAx]
    independentRate C F (cd z R B M e) (fd z R B r M e) one (unit p) := by
  refine GaussianNamedLipschitzRate.independent_rate _ _ _ _ _ _ two (unit_positive p)
    (GaussianBarnesCanonicalTaylorProductCoefficientName.regular z R B M e hz he) (GaussianBarnesCanonicalFixedTaylorCoefficientName.regular z R B r M e hz he) (.allI ?_)
  let a (x : PTm n) := Syn.shift x
  have hzs : Γ.map Fm.shift ⊢[PRAAx] source (a z) (a R) (a B) := by simpa [Fm.shift,Syn.shift,a] using hz.shift
  have hes : Γ.map Fm.shift ⊢[PRAAx] le (a e) (previous (a M)) := by simpa [Fm.shift,Syn.shift,a] using he.shift
  have hrs : Γ.map Fm.shift ⊢[PRAAx] le (cutoff (a p) (a R) (a M) (a e)) (a r) := by
    simpa [Fm.shift,Syn.shift,a] using hr.shift
  simpa only [diagonalEnvelope,a,Syn.shift,GaussianBarnesCanonicalTaylorProductCoefficientName.subst_data,GaussianBarnesCanonicalFixedTaylorCoefficientName.subst_data,GaussianCoefficientNameBounds.subst_unit,
    one,two,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    diagonal_at (a p) (var 0) (a z) (a R) (a B) (a r) (a M) (a e) hzs hes hrs

theorem actual_Barnes_fixed_coefficient_disk_uniform_convergence_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (let p := var 0
     let z := var 1
     let R := var 2
     let B := var 3
     let r := var 4
     let M := var 5
     let e := var 6
     (source z R B ⋏ le e (previous M)) ⟶ le (cutoff p R M e) r ⟶
       independentRate C F (cd z R B M e) (fd z R B r M e) one (unit p)) :=
  closeUniv 7 (.impI (.impI (cofinal_rate (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)
    Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFixedTaylorUniformConvergence
