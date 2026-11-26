import IPRADerivations.Analysis.Integration.CompactGrids.GaussianCompactRiemannThreeSplit
import IPRADerivations.Analysis.Beta.Partitions.GaussianBetaIntegralCutoffPartition
import IPRADerivations.Analysis.Beta.CompactKernels.GaussianBetaKernelCompactModulus
import IPRADerivations.Analysis.Integration.CompactGrids.GaussianCompactIntervalRescaling

/-!
# Actual original beta quadrature split at the original eta/top cutoffs

The full beta evaluator is the unchanged original one. A common rational
step aligns all three intervals. Original finite additivity retains its
observation errors, and the genuine encoding rate returns the middle
piece to the original earlier eta denominator. Every local beta modulus
and endpoint guard follows from the numerical/native source alone.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBetaIntegralThreeSplit

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (qadd positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalSyntheticDivision (qadd_congr)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianCompactRiemannName (quadrature)
open GaussianBetaKernelGridComparison (evaluatorF sampleDataBeta)
open GaussianGammaIntegralCutoffs (etaDen top cells)
open GaussianGammaCompactQuadratureBoundary (width)
open GaussianGammaCompactCutoffGeometry (ratio lowerWidth middleWidth)
open GaussianBetaIntegralCutoffPartition (denominator upperWidth totalWidth lowerCells middleCells upperCells totalCells)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def source (z R B k deep A N K : PTm n) : Fm PTm n :=
  GaussianGammaEulerCompactQuadrature.source z R B ⋏
    (GaussianBetaIntegralCutoffPartition.source k deep A R N ⋏ le one K)
def full (s z B k deep A R N K : PTm n) : PTm n :=
  quadrature evaluatorF s (totalCells k deep A R N K) one (totalWidth k deep A R N) (denominator deep A R) (sampleDataBeta z B N)
def lower (s z B k deep A R N K : PTm n) : PTm n :=
  quadrature evaluatorF s (lowerCells k deep A K) one (lowerWidth k deep A) (denominator deep A R) (sampleDataBeta z B N)
def middle (s z B k deep A R N K : PTm n) : PTm n :=
  quadrature evaluatorF s (middleCells k deep A R K) one (width k A R) (etaDen k A R) (sampleDataBeta z B N)
def encodedMiddle (s z B k deep A R N K : PTm n) : PTm n :=
  quadrature evaluatorF s (middleCells k deep A R K) (ratio k deep A) (middleWidth k deep A R) (denominator deep A R) (sampleDataBeta z B N)
def upper (s z B k deep A R N K : PTm n) : PTm n :=
  quadrature evaluatorF s (upperCells k deep A R N K) (denominator deep A R*top k A R) (upperWidth k deep A R N) (denominator deep A R) (sampleDataBeta z B N)
def pieces (s z B k deep A R N K : PTm n) : PTm n :=
  qadd (qadd (lower s z B k deep A R N K) (middle s z B k deep A R N K)) (upper s z B k deep A R N K)
def encodedPieces (s z B k deep A R N K : PTm n) : PTm n :=
  qadd (qadd (lower s z B k deep A R N K) (encodedMiddle s z B k deep A R N K)) (upper s z B k deep A R N K)
def splitNumerator (k deep A R N : PTm n) : PTm n :=
  two*totalWidth k deep A R N+two*(lowerWidth k deep A+middleWidth k deep A R)+two*middleWidth k deep A R

theorem quadrature_congr (F : PR 3) {p q M V a b C D E G x y : PTm n}
    (hp : Γ ⊢[PRAAx] p ≐ q) (hM : Γ ⊢[PRAAx] M ≐ V) (ha : Γ ⊢[PRAAx] a ≐ b)
    (hC : Γ ⊢[PRAAx] C ≐ D) (hE : Γ ⊢[PRAAx] E ≐ G) (hx : Γ ⊢[PRAAx] x ≐ y) :
    Γ ⊢[PRAAx] quadrature F p M a C E x ≐ quadrature F q V b D G y := by
  simpa only [GaussianCompactRiemannName.subst_quadrature,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.cons_val_succ,Matrix.head_cons,Matrix.tail_cons,
    (show (![p,M,a,C,E,x] : Fin 6 → PTm n) 5 = x from rfl),
    (show (![q,V,b,D,G,y] : Fin 6 → PTm n) 5 = y from rfl)] using
    Prf.eqCongr (Ax := PRAAx) (Γ := Γ) (quadrature F (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6)
      (σ := ![p,M,a,C,E,x]) (σ' := ![q,V,b,D,G,y])
        (fun i => by fin_cases i; exact hp; exact hM; exact ha; exact hC; exact hE; exact hx)

theorem full_beta_source (z R B k deep A N K : PTm n) (h : Γ ⊢[PRAAx] source z R B k deep A N K) : Γ ⊢[PRAAx]
    GaussianBetaKernelCompactModulus.compactSource z R B (denominator deep A R) N one (totalWidth k deep A R N) N := by
  have hp := h.andE₂.andE₁
  have hN := GaussianBetaIntegralCutoffPartition.degree_positive k deep A R N hp
  have endPoint := GaussianBetaIntegralCutoffPartition.total_endpoint k deep A R N hp
  exact .andI (.andI h.andE₁.andE₁ (.andI (GaussianBetaIntegralCutoffPartition.denominator_positive _ _ _) h.andE₁.andE₂))
    (.andI (.andI hN (le_refl N)) (.andI (le_refl one) (le_congr endPoint.eqSymm (.eqRefl _) (le_refl _))))

theorem middle_beta_source (z R B k deep A N K : PTm n) (h : Γ ⊢[PRAAx] source z R B k deep A N K) : Γ ⊢[PRAAx]
    GaussianBetaKernelCompactModulus.compactSource z R B (etaDen k A R) (top k A R) one (width k A R) N :=
  .andI (.andI h.andE₁.andE₁ (.andI (GaussianGammaIntegralCutoffs.eta_den_positive _ _ _) h.andE₁.andE₂))
    (.andI (.andI (GaussianBetaIntegralCutoffPartition.degree_positive _ _ _ _ _ h.andE₂.andE₁)
      (le_of_lt h.andE₂.andE₁.andE₂.andE₂)) (.andI (le_refl one)
        (le_congr (GaussianGammaCompactQuadratureBoundary.exact_right_endpoint _ _ _).eqSymm (.eqRefl _) (le_refl _))))

theorem original_same_denominator_split (s z R B k deep A N K : PTm n) (h : Γ ⊢[PRAAx] source z R B k deep A N K) : Γ ⊢[PRAAx]
    distanceBounded (full s z B k deep A R N K) (encodedPieces s z B k deep A R N K)
      (two*totalWidth k deep A R N+two*(lowerWidth k deep A+middleWidth k deep A R)) (denominator deep A R*unit s) := by
  let D := denominator deep A R
  let C1 := lowerWidth k deep A
  let C2 := middleWidth k deep A R
  let C3 := upperWidth k deep A R N
  let L := GaussianBetaKernelCompactModulus.lipschitz R D N
  let x := sampleDataBeta z B N
  have hp := h.andE₂.andE₁
  have hs : Γ ⊢[PRAAx] GaussianCompactRiemannThreeSplit.input evaluatorF one C1 C2 C3 D K L x :=
    .andI (le_refl one) (.andI (GaussianBetaIntegralCutoffPartition.lower_positive _ _ _ _ _ hp)
      (.andI (GaussianBetaIntegralCutoffPartition.middle_positive _ _ _ _)
        (.andI (GaussianBetaIntegralCutoffPartition.upper_positive _ _ _ _ _ hp)
          (.andI (GaussianBetaIntegralCutoffPartition.denominator_positive _ _ _) (.andI h.andE₂.andE₂
            (GaussianBetaKernelCompactModulus.sampled_modulus _ _ _ _ _ _ _ _ (full_beta_source z R B k deep A N K h)))))))
  have old := GaussianCompactRiemannThreeSplit.original_three_piece_split evaluatorF s one C1 C2 C3 D K L x hs
  exact distance_congr (.eqRefl _)
    (qadd_congr (qadd_congr (.eqRefl _) (quadrature_congr evaluatorF (.eqRefl _) (.eqRefl _)
      (GaussianBetaIntegralCutoffPartition.lower_endpoint _ _ _) (.eqRefl _) (.eqRefl _) (.eqRefl _)))
        (quadrature_congr evaluatorF (.eqRefl _) (.eqRefl _)
          (GaussianBetaIntegralCutoffPartition.middle_endpoint _ _ _ _ (le_of_lt hp.andE₂.andE₁)) (.eqRefl _) (.eqRefl _) (.eqRefl _)))
      (.eqRefl _) (.eqRefl _) old

theorem original_middle_encoding_error (s z R B k deep A N K : PTm n) (h : Γ ⊢[PRAAx] source z R B k deep A N K) : Γ ⊢[PRAAx]
    distanceBounded (encodedMiddle s z B k deep A R N K) (middle s z B k deep A R N K)
      (two*middleWidth k deep A R) (denominator deep A R*unit s) := by
  let J := ratio k deep A
  let E := etaDen k A R
  let D := denominator deep A R
  let C := width k A R
  let M := middleCells k deep A R K
  let L := GaussianBetaKernelCompactModulus.lipschitz R E (top k A R)
  let x := sampleDataBeta z B N
  have he := GaussianGammaIntegralCutoffs.eta_den_positive (Γ := Γ) k A R
  have hd := GaussianBetaIntegralCutoffPartition.denominator_positive (Γ := Γ) deep A R
  have hp := unit_positive (Γ := Γ) s
  have hm := positive_product (Γ := Γ) _ _ (GaussianBetaIntegralCutoffPartition.middle_positive k deep A R) h.andE₂.andE₂
  have input : Γ ⊢[PRAAx] GaussianCompactIntervalRescaling.input evaluatorF J one C E L (top k A R) x :=
    .andI (GaussianGammaCompactCutoffGeometry.ratio_positive _ _ _)
      (GaussianBetaKernelCompactModulus.compact_input _ _ _ _ _ _ _ _ (middle_beta_source z R B k deep A N K h))
  have old := GaussianCompactIntervalRescaling.quadrature_distance evaluatorF s M J one C E L (top k A R) x input hm
  have renamed := distance_congr (.eqRefl _)
    (quadrature_congr evaluatorF (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
      (GaussianBetaIntegralCutoffPartition.exact_denominator_refinement _ _ _ _ (le_of_lt h.andE₂.andE₁.andE₂.andE₁)).eqSymm (.eqRefl _))
        (.eqRefl _) (.eqRefl _) old
  have compare : Γ ⊢[PRAAx] le ((C*two)*(D*unit s)) ((two*middleWidth k deep A R)*(E*unit s)) := by
    have e := natEq (GaussianBetaIntegralCutoffPartition.exact_denominator_refinement (Γ := Γ) k deep A R (le_of_lt h.andE₂.andE₁.andE₂.andE₁))
    apply le_of_eq_add (d := zero)
    unfold middleWidth
    apply deriveNat
    dsimp only [D,E,C]
    ipra_simps
    rw [e]
    ring
  exact distance_symmetric _ _ _ _ (positive_product _ _ hd hp)
    (distance_radius_mono _ _ _ _ _ _ (positive_product _ _ he hp) (positive_product _ _ hd hp) compare renamed)

theorem original_beta_three_piece_split (s z R B k deep A N K : PTm n) (h : Γ ⊢[PRAAx] source z R B k deep A N K) : Γ ⊢[PRAAx]
    distanceBounded (full s z B k deep A R N K) (pieces s z B k deep A R N K)
      (splitNumerator k deep A R N) (denominator deep A R*unit s) := by
  let D := denominator deep A R*unit s
  have hd := positive_product (Γ := Γ) _ _ (GaussianBetaIntegralCutoffPartition.denominator_positive deep A R) (unit_positive s)
  have low := GaussianRationalPowerDifference.distance_refl_zero (lower s z B k deep A R N K) D hd
  have high := GaussianRationalPowerDifference.distance_refl_zero (upper s z B k deep A R N K) D hd
  have second := GaussianNameArithmetic.sum_distance _ _ _ _ _ _ _ hd
    (GaussianNameArithmetic.sum_distance _ _ _ _ _ _ _ hd low (original_middle_encoding_error s z R B k deep A N K h)) high
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold splitNumerator; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hd (original_same_denominator_split s z R B k deep A N K h) second)

theorem original_deep_eta_to_N_beta_three_quadrature_split_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
      (source (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⟶
        distanceBounded (full (var 0) (var 1) (var 3) (var 4) (var 5) (var 6) (var 2) (var 7) (var 8))
          (pieces (var 0) (var 1) (var 3) (var 4) (var 5) (var 6) (var 2) (var 7) (var 8))
          (splitNumerator (var 4) (var 5) (var 6) (var 2) (var 7)) (denominator (var 5) (var 6) (var 2)*unit (var 0))) :=
  closeUniv 9 (.impI (original_beta_three_piece_split _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBetaIntegralThreeSplit
