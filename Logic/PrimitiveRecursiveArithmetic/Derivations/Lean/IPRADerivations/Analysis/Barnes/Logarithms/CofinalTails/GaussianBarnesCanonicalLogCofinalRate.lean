import IPRADerivations.Analysis.Barnes.Logarithms.CofinalTails.GaussianBarnesCanonicalLogIntervalRate
import IPRADerivations.Analysis.Barnes.Logarithms.CofinalTails.GaussianBarnesCanonicalLogCofinal
import IPRADerivations.Analysis.Names.Rates.Moduli.GaussianNamedLipschitzRate

/-!
# The exact tail rate of the original cofinal Barnes logarithm

Compare the fixed finite sum and the cofinal sampler at one shared
rounding clock. If the cofinal endpoint is earlier, its own corrected
cutoff already bounds the omitted rows. The diagonal estimate therefore
removes all rounding slack and retains the exact finite tail radius.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalLogCofinalRate

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianBarnesCanonicalLogSchedule (initial endpoint length initial_length initial_positive initial_radius)
open GaussianBarnesCanonicalLogIntervalRate (ordered_difference)
open GaussianBarnesCanonicalLogRow (boundNumerator)
open GaussianBarnesCanonicalLogTail (tailDenominator tail_denominator_positive)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianExponentialReference (unit_monotone)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedLipschitzRate (diagonalEnvelope diagonalNumerator diagonalDenominator)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "F" => GaussianBarnesCanonicalFiniteLog.nameF
local notation "G" => GaussianBarnesCanonicalLogCofinal.nameF
local notation "Fdata" => GaussianBarnesCanonicalFiniteLog.data
local notation "Gdata" => GaussianBarnesCanonicalLogCofinal.data
local notation "Fs" => GaussianBarnesCanonicalFiniteLog.sample
local notation "Gs" => GaussianBarnesCanonicalLogCofinal.sample
local notation "Fc" => GaussianBarnesCanonicalFiniteLog.clock
local notation "Gc" => GaussianBarnesCanonicalLogSchedule.clock
local notation "Fgain" => GaussianBarnesCanonicalFiniteLog.gain
local notation "Ggain" => GaussianBarnesCanonicalLogSchedule.gain
local notation "source" => GaussianBarnesCanonicalLogCofinal.source
local notation "rowSource" => GaussianBarnesCanonicalLogTail.source
local notation "value" => GaussianBarnesCanonicalLogRoundedTail.value
local notation "roundUnit" => DyadicComplexLogarithm.unit

theorem initial_source (z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] rowSource z R B (initial R) :=
  .andI h.andE₁ (.andI (initial_positive R) (.andI h.andE₂ (initial_radius R)))

private theorem common_gain (p R : PTm n) :
    Γ ⊢[PRAAx] le (Fgain (initial R) (length p R)) (Ggain p R) := by
  let b := length p R
  let E := endpoint p R
  have eq := initial_length (Γ := Γ) p R
  have shorter : Γ ⊢[PRAAx] le b E := le_congr (.eqRefl b) eq (le_add_left b (initial R))
  have weight : Γ ⊢[PRAAx] num 5*(initial R+b) ≐ num 5*E := congrMul (.eqRefl _) eq
  exact le_congr (.eqRefl _) (by
    change Γ ⊢[PRAAx] E*(num 5*E) ≐ num 5*E*E
    ipra_ring)
    (le_mul_mono shorter (le_congr (.eqRefl _) weight (le_refl _)))

theorem cofinal_clock_budget (p R v : PTm n) (late : Γ ⊢[PRAAx] le (Gc p R) v) :
    Γ ⊢[PRAAx] le (Fgain (initial R) (length p R)*unit p) (roundUnit v) :=
  le_trans (le_mul_mono (common_gain p R) (unit_monotone (le_add_right p (num 4))))
    (le_trans (GaussianBarnesCanonicalLogSchedule.clock_budget p R) (unit_monotone (add_le_add_right (num 4) late)))

private theorem early_endpoint_budget (p R : PTm n) :
    Γ ⊢[PRAAx] le (boundNumerator R*unit p) (tailDenominator (initial R+length p R)) := by
  have move : Γ ⊢[PRAAx] one*tailDenominator (endpoint p R) ≐ tailDenominator (initial R+length p R) :=
    (one_mul _).eqTrans (congrMul (.eqRefl (num 3)) (initial_length p R).eqSymm)
  exact le_congr (.eqRefl _) move
    (le_trans (le_mul_mono (le_refl (boundNumerator R)) (unit_monotone (le_add_right p (num 4))))
      (GaussianBarnesCanonicalLogSchedule.suffix_budget p R))

private theorem common_difference (p v z R B r : PTm n) (h : Γ ⊢[PRAAx] source z R B)
    (hf : Γ ⊢[PRAAx] le (Fgain (initial R) r*unit p) (roundUnit v))
    (hg : Γ ⊢[PRAAx] le (Fgain (initial R) (length p R)*unit p) (roundUnit v)) :
    let W := tailDenominator (initial R+r)
    Γ ⊢[PRAAx] distanceBounded (value v z R B (initial R) r) (value v z R B (initial R) (length p R))
      (boundNumerator R*unit p+two*W) (W*unit p) := by
  let a := initial R
  let b := length p R
  let W := tailDenominator (a+r)
  let V := tailDenominator (a+b)
  let U := unit p
  let D := boundNumerator R
  have h0 := initial_source z R B h
  have hW := tail_denominator_positive (Γ := Γ) (a+r) (le_trans (initial_positive R) (le_add_right _ _))
  have hV := tail_denominator_positive (Γ := Γ) (a+b) (le_trans (initial_positive R) (le_add_right _ _))
  have hU := unit_positive (Γ := Γ) p
  have hWU := positive_product W U hW hU
  have hVU := positive_product V U hV hU
  refine .orE (le_total r b) ?_ ?_
  · have comparison := ordered_difference p v z R B a r b h0.wk Prf.hyp0 hg.wk
    exact distance_radius_mono _ _ _ _ _ _ hWU.wk hWU.wk
      (le_of_eq_add (d := W*(W*U)) (by ipra_ring))
      (distance_symmetric _ _ _ _ hWU.wk comparison)
  · have comparison := ordered_difference p v z R B a b r h0.wk Prf.hyp0 hf.wk
    have first : le b r :: Γ ⊢[PRAAx] le (D*U+V) (V+V) :=
      add_le_add₂ (early_endpoint_budget (Γ := le b r :: Γ) p R) (le_refl V)
    have small : le b r :: Γ ⊢[PRAAx]
        distanceBounded (value v z R B a r) (value v z R B a b) two U :=
      distance_radius_mono _ _ _ _ _ _ hVU.wk hU.wk
        (le_congr (.eqRefl _) (by ipra_ring) (mul_le_mul_right U first)) comparison
    exact distance_radius_mono _ _ _ _ _ _ hU.wk hWU.wk
      (le_of_eq_add (d := D*U*U) (by ipra_ring)) small

theorem diagonal_observation (p z R B r : PTm n) (h : Γ ⊢[PRAAx] source z R B) :
    let W := tailDenominator (initial R+r)
    Γ ⊢[PRAAx] distanceBounded (Fs p z R B (initial R) r) (Gs p z R B)
      (diagonalNumerator (boundNumerator R) W (num 4) p) (diagonalDenominator W p) := by
  let a := initial R
  let b := length p R
  let f := Fc p a r
  let g := Gc p R
  let v := f+g
  let W := tailDenominator (a+r)
  let U := unit p
  let D := boundNumerator R
  let x := Fs p z R B a r
  let y := Gs p z R B
  let P := value v z R B a r
  let Q := value v z R B a b
  have h0 := initial_source z R B h
  have hW := tail_denominator_positive (Γ := Γ) (a+r) (le_trans (initial_positive R) (le_add_right _ _))
  have hU := unit_positive (Γ := Γ) p
  have hWU := positive_product W U hW hU
  have first := GaussianBarnesCanonicalFiniteLog.later_rounding p v z R B a r h0 (le_add_right f g)
  have raw := GaussianBarnesCanonicalLogRoundedTail.ordered_distance g v z R B a b h0 (le_add_left g f)
  have last : Γ ⊢[PRAAx] distanceBounded Q y one U :=
    distance_radius_mono _ _ _ _ _ _ (GaussianLocalLogarithmName.unit_positive g) hU
      (le_congr (.eqRefl _) (one_mul _).eqSymm (cofinal_clock_budget p R g (le_refl g))) raw
  have middle := common_difference p v z R B r h
    (GaussianBarnesCanonicalFiniteLog.clock_budget _ p a r v (le_refl _) (le_add_right f g))
    (cofinal_clock_budget p R v (le_add_left g f))
  have scale : Γ ⊢[PRAAx] le (one*(W*U)) (W*U) :=
    le_congr (one_mul _).eqSymm (.eqRefl _) (le_refl _)
  have left := distance_radius_mono x P one U W (W*U) hU hWU scale
    (distance_symmetric _ _ _ _ hU first)
  have right := distance_radius_mono Q y one U W (W*U) hU hWU scale last
  exact distance_congr (.eqRefl _) (.eqRefl _) (by dsimp only [diagonalNumerator,D,W,U]; ipra_ring) (.eqRefl _)
    (distance_triangle_same x P y W ((D*U+two*W)+W) (W*U) hWU left
      (distance_triangle_same P Q y (D*U+two*W) W (W*U) hWU middle right))

theorem finite_tail_rate (z R B r : PTm n) (h : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] independentRate F G (Fdata z R B (initial R) r) (Gdata z R B)
      (boundNumerator R) (tailDenominator (initial R+r)) := by
  apply GaussianNamedLipschitzRate.independent_rate F G _ _ _ _ (num 4)
    (tail_denominator_positive (initial R+r) (le_trans (initial_positive R) (le_add_right _ _)))
    (GaussianBarnesCanonicalFiniteLog.regular _ _ _ _ _ (initial_source z R B h))
    (GaussianBarnesCanonicalLogCofinal.regular z R B h)
  refine .allI ?_
  let s (v : PTm n) := Syn.shift v
  let Δ := Γ.map Fm.shift
  let a := initial (s R)
  have hs : Δ ⊢[PRAAx] source (s z) (s R) (s B) := by simpa [Δ,s,Fm.shift,Syn.shift] using h.shift
  simpa only [diagonalEnvelope,GaussianBarnesCanonicalFiniteLog.subst_data,GaussianBarnesCanonicalLogCofinal.subst_data,
    GaussianBarnesCanonicalLogSchedule.subst_initial,GaussianBarnesCanonicalLogRow.subst_boundNumerator,
    GaussianBarnesCanonicalLogTail.subst_tailDenominator,PTm.subst_add,Syn.shift,s,a,PTm.subst_num] using
    distance_congr (GaussianBarnesCanonicalFiniteLog.sample_at (var 0) (s z) (s R) (s B) a (s r)).eqSymm
      (GaussianBarnesCanonicalLogCofinal.sample_at (var 0) (s z) (s R) (s B)).eqSymm (.eqRefl _) (.eqRefl _)
      (diagonal_observation (var 0) (s z) (s R) (s B) (s r) hs)

theorem actual_Barnes_finite_to_cofinal_log_tail_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (let z := var 0
     let R := var 1
     let B := var 2
     let r := var 3
     source z R B ⟶ independentRate F G (Fdata z R B (initial R) r) (Gdata z R B)
       (boundNumerator R) (tailDenominator (initial R+r))) :=
  closeUniv 4 (.impI (finite_tail_rate _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalLogCofinalRate
