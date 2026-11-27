import IPRADerivations.Analysis.Gamma.Digamma.LogGammaDerivative.GaussianLogGammaEulerDigammaFractionsRate

/-!
# A cofinal name that reads the original digamma partial fractions

The literal finite name at clock `p+1` and cutoff `(R+2)·2^(p+1)`
uses the original Euler–Mascheroni constant. The explicit cutoff pays
for the truncation, and the faster clock pays for its observations.
The resulting regular name is independently equivalent to the original
cofinal complex Euler slope.
-/

set_option autoImplicit false
set_option maxHeartbeats 430000

namespace LeanProofs.IPRA.Analysis.GaussianLogGammaEulerDigammaFractionsCofinal

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianLogGammaEulerHead (rowData subst_rowData)
open GaussianLogGammaEulerResidualRadius (radius subst_radius)
open GaussianLogGammaEulerDigammaFractionsRate (canonical_fraction_rate)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_trans)
open GaussianNamedInverseRate (rateNumerator rateDenominator rate_at denominator_positive)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRightHalfPlaneLogarithm (source)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "cofinalF" => GaussianLogGammaEulerReciprocalSlopeCofinal.nameF
local notation "cofinalData" => GaussianLogGammaEulerReciprocalSlopeCofinal.canonicalData
local notation "fractionsF" => GaussianLogGammaEulerDigammaFractions.nameF
local notation "fractionsData" => GaussianLogGammaEulerDigammaFractions.data

def cutoff (A B p : PTm n) : PTm n := (radius A B + two) * unit (succ p)
def observed (p A B D neg : PTm n) : PTm n := ap2 fractionsF (succ p) (fractionsData A B D neg (cutoff A B p))
abbrev data (A B D neg : PTm n) : PTm n := rowData A B D neg

private def body : PTm 2 :=
  observed (var 0) (fstT (var 1)) (fstT (sndT (var 1))) (fstT (sndT (sndT (var 1)))) (sndT (sndT (sndT (var 1))))

def nameF : PR 2 := PTm.toPR body

ipra_subst cutoff [two, one]

ipra_subst observed

theorem sample_at (p A B D neg : PTm n) :
    Γ ⊢[PRAAx] ap2 nameF p (data A B D neg) ≐ observed p A B D neg := by
  simpa [nameF, body, data, rowData, pairVector, pairVectorField] using
    (toPR_pairVector_eq (Γ := Γ) (k := 3)
      (observed (var 0) (var 1) (var 2) (var 3) (var 4)) p ![A, B, D, neg])

private theorem cutoff_positive (A B p : PTm n) : Γ ⊢[PRAAx] le one (cutoff A B p) :=
  positive_product _ _ (le_trans (le_succ_self one) (le_add_left two (radius A B))) (unit_positive (succ p))

/-- The retimed literal partial fractions give the sharp comparison of two requested observations. -/
theorem distance_at (p q A B D neg : PTm n) (h : Γ ⊢[PRAAx] source A D neg) :
    Γ ⊢[PRAAx] distanceBounded (ap2 cofinalF p (cofinalData A B D neg)) (ap2 nameF q (data A B D neg))
      (unit p + unit q) (unit p * unit q) := by
  let N := cutoff A B q
  let T := radius A B + two
  let U := unit p
  let V := unit q
  have hN := cutoff_positive (Γ := Γ) A B q
  have hp := positive_product (Γ := Γ) _ _ (unit_positive p) (unit_positive q)
  have raw := rate_at cofinalF fractionsF (cofinalData A B D neg) (fractionsData A B D neg N)
    T N p (succ q) (canonical_fraction_rate A B D neg N h hN)
  have cmp : Γ ⊢[PRAAx] le (rateNumerator T N p (succ q) * (U * V))
      ((U + V) * rateDenominator N p (succ q)) := by
    have e : Γ ⊢[PRAAx] unit (succ q) ≐ unit q * two := pw_succ two q
    apply le_of_eq_add (d := zero)
    apply deriveNat
    dsimp only [rateNumerator, rateDenominator, N, cutoff, T, U, V]
    ipra_simps
    rw [natEq e]
    ipra_simps
    ring
  exact distance_congr (.eqRefl _) (sample_at q A B D neg).eqSymm (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ _ _ _ (denominator_positive N p (succ q) hN) hp cmp raw)

theorem cofinal_equivalent (A B D neg : PTm n) (h : Γ ⊢[PRAAx] source A D neg) :
    Γ ⊢[PRAAx] crossEquivalent cofinalF nameF (cofinalData A B D neg) (data A B D neg) := by
  refine .allI (.allI ?_)
  let s (t : PTm n) := Syn.shift (Syn.shift t)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  have hs : Δ ⊢[PRAAx] source (s A) (s D) (s neg) := by
    simpa [Δ, s, Fm.shift, Syn.shift, source, GaussianRightHalfPlaneArgument.source] using h.shift.shift
  simpa only [crossEquivalent, Δ, s, Syn.shift, subst_rowData, GaussianLogGammaEulerReciprocalSlopeCofinal.canonicalData,
    GaussianLogGammaEulerReciprocalSlopeCofinal.subst_data, subst_radius] using
    distance_at (var 1) (var 0) (s A) (s B) (s D) (s neg) hs

theorem regular (A B D neg : PTm n) (h : Γ ⊢[PRAAx] source A D neg) : Γ ⊢[PRAAx] pointCN nameF (data A B D neg) := by
  let x := cofinalData A B D neg
  let y := data A B D neg
  have e := cofinal_equivalent A B D neg h
  exact cross_trans nameF cofinalF nameF y x y (cross_symm cofinalF nameF x y e) e

theorem actual_cofinal_complex_digamma_partial_fractions_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (source (var 0) (var 2) (var 3) ⟶
        pointCN nameF (data (var 0) (var 1) (var 2) (var 3)) ⋏
        crossEquivalent cofinalF nameF (cofinalData (var 0) (var 1) (var 2) (var 3)) (data (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (.andI (regular _ _ _ _ Prf.hyp0) (cofinal_equivalent _ _ _ _ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianLogGammaEulerDigammaFractionsCofinal
