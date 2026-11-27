import IPRADerivations.Analysis.Barnes.Taylor.Grids.Cofinal.GaussianBarnesCanonicalActualTaylorDiskGridLimit
import IPRADerivations.Analysis.Barnes.Taylor.Grids.Cofinal.GaussianBarnesCanonicalCofinalGridRadiusComparison
import IPRADerivations.Analysis.Barnes.Taylor.Coefficients.GaussianBarnesCanonicalTaylorDerivativeChart
import IPRADerivations.Analysis.Barnes.Taylor.Coefficients.GaussianBarnesCanonicalTaylorDerivativeOrderInvariance

/-!
# The original leading Barnes Taylor derivative on two disks

A common positive integer refinement gives one test step for both
normalized grids. Transport the two derivative names across the
refinement and use the original grid limits. A finite slack query removes
the error left by the auxiliary precision.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalTaylorDerivativeRadius

open_ipra
open ComplexLogarithmRemainder (bounded_mono bounded_scale normSq normSq_one oneCode scale)
open GaussianBarnesCanonicalActualTaylorDiskGridLimit (observationClock stepClock value)
open GaussianBarnesCanonicalCofinalTaylorGridObservations (deadline)
open GaussianBarnesCanonicalHigherRows (previous)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaEncodingRescaling (fraction_rescale)
open GaussianL1 (norm1 norm1_one normSq_le_norm1_square)
open GaussianNameEquivalence (crossEquivalent cross_at cross_trans)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (ofGaussian positive_product)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalSlackRemoval (slack slack_removal_at)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "F" => GaussianBarnesCanonicalTaylorProductDerivativeName.nameF
local notation "fd" => GaussianBarnesCanonicalTaylorProductDerivativeName.data

def refinement (p R S M : PTm n) : PTm n :=
  unit (stepClock p R M)*unit (stepClock p S M)+previous M

private theorem fit_one_step (B E K : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] le K E) : Γ ⊢[PRAAx] le (norm1 oneCode*K) (E*B) :=
  le_congr ((congrMul norm1_one (.eqRefl K)).eqTrans (one_mul K)).eqSymm (.eqRefl _)
    (le_trans h (le_congr (one_mul E) (mul_comm _ _) (mul_le_mul_right E hB)))

theorem refinement_admission (p R S B M : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    let E := refinement p R S M
    Γ ⊢[PRAAx] le one E ⋏
      le (norm1 oneCode*unit (stepClock p R M)) (E*B) ⋏
      le (norm1 oneCode*unit (stepClock p S M)) (E*B) ⋏
      le (previous M*norm1 oneCode) (E*B) := by
  let U := unit (stepClock p R M)
  let V := unit (stepClock p S M)
  let J := previous M
  let E := refinement p R S M
  have hu := unit_positive (Γ := Γ) (stepClock p R M)
  have hv := unit_positive (Γ := Γ) (stepClock p S M)
  have u : Γ ⊢[PRAAx] le U (U*V) :=
    le_congr (one_mul U) (mul_comm _ _) (mul_le_mul_right U hv)
  have v : Γ ⊢[PRAAx] le V (U*V) :=
    le_congr (one_mul V) (.eqRefl _) (mul_le_mul_right V hu)
  have up : Γ ⊢[PRAAx] le (U*V) E := le_add_right _ J
  have width := le_congr (mul_comm (norm1 oneCode) J) (.eqRefl _)
    (fit_one_step B E J hB (le_add_left J (U*V)))
  exact .andI (le_trans (positive_product _ _ hu hv) up)
    (.andI (fit_one_step B E U hB (le_trans u up)) (.andI (fit_one_step B E V hB (le_trans v up)) width))

private theorem widen (z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] source z (R+one) B :=
  .andI h.andE₁ (bounded_mono h.andE₂ (le_of_eq_add (d := B) (by ipra_ring)))

private theorem scale_source (z R B E : PTm n) (h : Γ ⊢[PRAAx] source z R B)
    (hE : Γ ⊢[PRAAx] le one E) : Γ ⊢[PRAAx] source (scale E z) R (E*B) :=
  .andI (positive_product _ _ hE h.andE₁) (le_congr (.eqRefl _) (by ipra_ring) (bounded_scale E h.andE₂))

theorem comparison_slack (p t u z R S B M : PTm n) (hR : Γ ⊢[PRAAx] source z R B)
    (hS : Γ ⊢[PRAAx] source z S B) :
    Γ ⊢[PRAAx] slack
      (qsub (ap2 F t (fd z (R+one) B M (previous M))) (ap2 F u (fd z (S+one) B M (previous M))))
      (unit t+unit u) (unit t*unit u) (num 7) p := by
  let e := previous M
  let E := refinement p R S M
  let Z := scale E z
  let D := E*B
  let L := deadline p D e
  let O := observationClock p D M
  let q := L+O
  let T := unit t
  let U := unit u
  let P := unit p
  let K := (T*U)*P
  let x := ap2 F t (fd z (R+one) B M e)
  let a := ap2 F p (fd Z (R+one) D M e)
  let y := value q Z oneCode R D M
  let w := value q Z oneCode S D M
  let b := ap2 F p (fd Z (S+one) D M e)
  let v := ap2 F u (fd z (S+one) B M e)
  have fit := refinement_admission p R S B M hR.andE₁
  have sr : Γ ⊢[PRAAx] source Z R D := scale_source z R B E hR fit.andE₁
  have ss : Γ ⊢[PRAAx] source Z S D := scale_source z S B E hS fit.andE₁
  have hz : Γ ⊢[PRAAx] ofGaussian z B ≐ ofGaussian Z D := (fraction_rescale z B E hR.andE₁ fit.andE₁).eqSymm
  have hn : Γ ⊢[PRAAx] le one (normSq oneCode) := le_congr (.eqRefl _) normSq_one.eqSymm (le_refl one)
  have hp := unit_positive (Γ := Γ) p
  have ht := unit_positive (Γ := Γ) t
  have hu := unit_positive (Γ := Γ) u
  have hk : Γ ⊢[PRAAx] le one K := positive_product _ _ (positive_product _ _ ht hu) hp
  have pp := positive_product _ _ hp hp
  have eq₁ := GaussianBarnesCanonicalTaylorDerivativeChart.cofinal_cross
    z Z (R+one) B D M e (widen z R B hR) (widen Z R D sr) (le_refl e) hz
  have eq₂ := GaussianBarnesCanonicalTaylorDerivativeChart.cofinal_cross
    Z z (S+one) D B M e (widen Z S D ss) (widen z S B hS) (le_refl e) hz.eqSymm
  have edge₁ : Γ ⊢[PRAAx] distanceBounded x a ((T+P)*U) K :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ ht hp) hk (le_of_eq_add (d := zero) (by dsimp only [K,T,U,P]; ipra_ring))
      (cross_at F F _ _ t p eq₁)
  have edge₂ : Γ ⊢[PRAAx] distanceBounded b v ((P+U)*T) K :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hp hu) hk (le_of_eq_add (d := zero) (by dsimp only [K,T,U,P]; ipra_ring))
      (cross_at F F _ _ p u eq₂)
  have near₁ : Γ ⊢[PRAAx] distanceBounded a y (two*(T*U)) K :=
    distance_radius_mono _ _ _ _ _ _ pp hk (le_of_eq_add (d := zero) (by dsimp only [K,T,U,P]; ipra_ring))
      (distance_symmetric _ _ _ _ pp (GaussianBarnesCanonicalActualTaylorDiskGridLimit.rate p Z oneCode R D M q p
        sr hn fit.andE₂.andE₁ (le_add_left O L)))
  have near₂ : Γ ⊢[PRAAx] distanceBounded w b (two*(T*U)) K :=
    distance_radius_mono _ _ _ _ _ _ pp hk (le_of_eq_add (d := zero) (by dsimp only [K,T,U,P]; ipra_ring))
      (GaussianBarnesCanonicalActualTaylorDiskGridLimit.rate p Z oneCode S D M q p
        ss hn fit.andE₂.andE₂.andE₁ (le_add_left O L))
  have grid : Γ ⊢[PRAAx] distanceBounded y w (T*U) K :=
    distance_radius_mono _ _ _ _ _ _ hp hk (le_of_eq_add (d := zero) (by dsimp only [K,T,U,P]; ipra_ring))
      (GaussianBarnesCanonicalCofinalGridRadiusComparison.scheduled_bound p q Z oneCode R S D (norm1 oneCode) e
        sr ss (normSq_le_norm1_square oneCode) fit.andE₂.andE₂.andE₂ hn (le_add_right L O))
  have first := distance_triangle_same _ _ _ _ _ _ hk edge₁ near₁
  have middle := distance_triangle_same _ _ _ _ _ _ hk first grid
  have last := distance_triangle_same _ _ _ _ _ _ hk middle near₂
  change Γ ⊢[PRAAx] distanceBounded x v ((T+U)*P+num 7*(T*U)) K
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hk last edge₂)

theorem comparison_at (t u z R S B M : PTm n) (hR : Γ ⊢[PRAAx] source z R B)
    (hS : Γ ⊢[PRAAx] source z S B) :
    Γ ⊢[PRAAx] distanceBounded (ap2 F t (fd z (R+one) B M (previous M))) (ap2 F u (fd z (S+one) B M (previous M)))
      (unit t+unit u) (unit t*unit u) :=
  slack_removal_at _ _ _ (num 7) (positive_product _ _ (unit_positive t) (unit_positive u))
    (comparison_slack _ t u z R S B M hR hS)

theorem leading_cross (z R S B M : PTm n) (hR : Γ ⊢[PRAAx] source z R B)
    (hS : Γ ⊢[PRAAx] source z S B) :
    Γ ⊢[PRAAx] crossEquivalent F F (fd z (R+one) B M (previous M)) (fd z (S+one) B M (previous M)) := by
  refine .allI (.allI ?_)
  let sh (x : PTm n) := Syn.shift (Syn.shift x)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  have hR' : Δ ⊢[PRAAx] source (sh z) (sh R) (sh B) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hR.shift.shift
  have hS' : Δ ⊢[PRAAx] source (sh z) (sh S) (sh B) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hS.shift.shift
  simpa [Δ,sh,Syn.shift,one,GaussianBarnesCanonicalTaylorProductDerivativeName.data,
    GaussianBarnesCanonicalTaylorProductDerivativeName.coefficientData] using
    comparison_at (var 1) (var 0) (sh z) (sh R) (sh S) (sh B) (sh M) hR' hS'

theorem actual_Barnes_leading_factorial_Taylor_disk_overlap_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (let z := var 0
     let R := var 1
     let S := var 2
     let B := var 3
     let M := var 4
     source z R B ⟶ source z S B ⟶
       crossEquivalent F F (fd z (R+one) B M (previous M)) (fd z (S+one) B M (previous M))) :=
  closeUniv 5 (.impI (.impI (leading_cross _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem retained_cross (z R S B M e : PTm n) (hR : Γ ⊢[PRAAx] source z R B)
    (hS : Γ ⊢[PRAAx] source z S B) (h₂ : Γ ⊢[PRAAx] le two e)
    (he : Γ ⊢[PRAAx] le e (previous M)) :
    Γ ⊢[PRAAx] crossEquivalent F F (fd z (R+one) B M e) (fd z (S+one) B M e) := by
  let N := monus e two
  have size : Γ ⊢[PRAAx] previous N ≐ e :=
    (show Γ ⊢[PRAAx] previous N ≐ two+N by unfold previous; ipra_ring).eqTrans (eq_add_of_le h₂).eqSymm
  have retain : Γ ⊢[PRAAx] le e (previous N) := le_congr (.eqRefl _) size.eqSymm (le_refl e)
  have dataEq (A : PTm n) : Γ ⊢[PRAAx] fd z A B N (previous N) ≐ fd z A B N e := by
    ipra_congr (fd (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) with
      [.eqRefl z, .eqRefl A, .eqRefl B, .eqRefl N, size] using
      [GaussianBarnesCanonicalTaylorProductDerivativeName.data,GaussianBarnesCanonicalTaylorProductDerivativeName.coefficientData]
  have middle : Γ ⊢[PRAAx] crossEquivalent F F (fd z (R+one) B N e) (fd z (S+one) B N e) :=
    GaussianGammaCompactCutoffAlignment.cross_data_congr F F _ _ _ _
      (dataEq (R+one)) (dataEq (S+one)) (leading_cross z R S B N hR hS)
  have first := GaussianBarnesCanonicalTaylorDerivativeOrderInvariance.cofinal_cross
    z (R+one) B M N e (widen z R B hR) he retain
  have last := GaussianBarnesCanonicalTaylorDerivativeOrderInvariance.cofinal_cross
    z (S+one) B N M e (widen z S B hS) retain he
  exact cross_trans _ _ _ _ _ _ first (cross_trans _ _ _ _ _ _ middle last)

theorem actual_Barnes_retained_factorial_Taylor_disk_overlap_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (let z := var 0
     let R := var 1
     let S := var 2
     let B := var 3
     let M := var 4
     let e := var 5
     (source z R B ⋏ source z S B ⋏ le two e ⋏ le e (previous M)) ⟶
       crossEquivalent F F (fd z (R+one) B M e) (fd z (S+one) B M e)) :=
  closeUniv 6 (.impI (retained_cross _ _ _ _ _ _ Prf.hyp0.andE₁
    Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalTaylorDerivativeRadius
