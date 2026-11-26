import IPRADerivations.Analysis.Stirling.Binet.Laplace.GaussianBinetLaplaceWeightedShiftRow
import IPRADerivations.Analysis.Stirling.Binet.Laplace.GaussianBinetLaplaceDifferenceGrid

/-!
# Read the original difference of the two Binet samples at each grid tag

The shared compact grid keeps the original evaluators at every cell.
Their rational sample difference agrees with the product of the
original exponential and named weighted integral, up to the original
normalization and observation errors.
-/

set_option autoImplicit false
set_option maxHeartbeats 550000

namespace LeanProofs.IPRA.Analysis.GaussianBinetLaplaceWeightedGridReadback

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBinetLaplaceIntegrand (input cofinalF cofinalData cofinal_regular)
open GaussianBinetLaplaceIntegrandShift (differenceF differenceDataWithRadius)
open GaussianBinetLaplaceStrip (evaluatorF evaluator_at fixedData tagNumerator tag_inside)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianCompactRiemannName (grid grid_inside sampleBody sampleData sample_body_at)
open GaussianNameEquivalence (cross_to_diagonal diagonal_at)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_triangle_same)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalSyntheticDivision (qsub_congr)
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "F" => evaluatorF GaussianBinetLaplaceStrip.Kernel.cofinal
local notation "W" => GaussianBinetLaplaceWeightedShiftRow.nameF
local notation "wd" => GaussianBinetLaplaceWeightedShiftRow.data
local notation "domain" => GaussianLogGammaEulerResidualDomain.source

theorem sample_difference (q X Y D sign R S T a b : PTm n)
    (h : Γ ⊢[PRAAx] input X Y D sign R T a b) (hs : Γ ⊢[PRAAx] input (X+D) Y D sign S T a b) :
    Γ ⊢[PRAAx] distanceBounded
      (qsub (ap2 cofinalF q (cofinalData X Y D sign R T a b)) (ap2 cofinalF q (cofinalData (X+D) Y D sign S T a b)))
      (ap2 W q (wd X Y D sign R T a b)) (num 8) (unit q) := by
  let x := cofinalData X Y D sign R T a b
  let y := cofinalData (X+D) Y D sign S T a b
  have norm := GaussianNamedDifference.sample_error cofinalF cofinalF x y q
    (cofinal_regular X Y D sign R T a b h) (cofinal_regular (X+D) Y D sign S T a b hs)
  have cross := GaussianBinetLaplaceWeightedShiftRow.original_row_with_radius X Y D sign R S T a b h hs
  have actual := diagonal_at differenceF W (differenceDataWithRadius X Y D sign R S T a b)
    (wd X Y D sign R T a b) q (cross_to_diagonal _ _ _ _ cross)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ (unit_positive q)
      (distance_symmetric _ _ _ _ (unit_positive q) norm) actual)

private theorem integrand_data_congr (X Y D sign R T a a' b b' : PTm n)
    (ha : Γ ⊢[PRAAx] a ≐ a') (hb : Γ ⊢[PRAAx] b ≐ b') :
    Γ ⊢[PRAAx] cofinalData X Y D sign R T a b ≐ cofinalData X Y D sign R T a' b' := by
  have left : Γ ⊢[PRAAx] cofinalData X Y D sign R T a b ≐ cofinalData X Y D sign R T a' b := by
    simpa only [GaussianBinetLaplaceIntegrand.subst_cofinalData, Syn.inst_zero, Syn.subst_inst_shift, Syn.subst_var] using
      Prf.eqCongr1 (cofinalData (Syn.shift X) (Syn.shift Y) (Syn.shift D) (Syn.shift sign) (Syn.shift R)
        (Syn.shift T) (var 0) (Syn.shift b)) ha
  have right : Γ ⊢[PRAAx] cofinalData X Y D sign R T a' b ≐ cofinalData X Y D sign R T a' b' := by
    simpa only [GaussianBinetLaplaceIntegrand.subst_cofinalData, Syn.inst_zero, Syn.subst_inst_shift, Syn.subst_var] using
      Prf.eqCongr1 (cofinalData (Syn.shift X) (Syn.shift Y) (Syn.shift D) (Syn.shift sign) (Syn.shift R)
        (Syn.shift T) (Syn.shift a') (var 0)) hb
  exact left.eqTrans right

theorem cell_samples (j q N X Y D sign R S T : PTm n) :
    Γ ⊢[PRAAx]
      (qsub (inst2 (sampleBody F) j (sampleData q N (one+zero) T one (fixedData X Y D sign R T zero)))
        (inst2 (sampleBody F) j (sampleData q N (one+zero) T one (fixedData (X+D) Y D sign S T zero)))) ≐
      qsub (ap2 cofinalF q (cofinalData X Y D sign R T (T*j) N))
        (ap2 cofinalF q (cofinalData (X+D) Y D sign S T (T*j) N)) := by
  let t := grid j N (one+zero) T one
  let a := tagNumerator t
  let b := sndT t
  let x := fixedData X Y D sign R T zero
  let y := fixedData (X+D) Y D sign S T zero
  have ea : Γ ⊢[PRAAx] a ≐ T*j :=
    (congrMonus ((fst_pair _ _).eqTrans (by ipra_ring)) ((snd_pair _ _).eqTrans (one_mul N))).eqTrans
      (add_monus _ _)
  have eb : Γ ⊢[PRAAx] b ≐ N := (snd_pair _ _).eqTrans (one_mul N)
  have u := (sample_body_at (Γ := Γ) F j q N (one+zero) T one x).eqTrans
    ((evaluator_at .cofinal q t X Y D sign R T zero).eqTrans
      (congrAp2 cofinalF (.eqRefl q) (integrand_data_congr X Y D sign R T a (T*j) b N ea eb)))
  have v := (sample_body_at (Γ := Γ) F j q N (one+zero) T one y).eqTrans
    ((evaluator_at .cofinal q t (X+D) Y D sign S T zero).eqTrans
      (congrAp2 cofinalF (.eqRefl q) (integrand_data_congr (X+D) Y D sign S T a (T*j) b N ea eb)))
  exact qsub_congr u v

theorem cell_at (j q N X Y D sign R S T : PTm n)
    (h : Γ ⊢[PRAAx] domain X Y D sign R) (hs : Γ ⊢[PRAAx] domain (X+D) Y D sign S)
    (hN : Γ ⊢[PRAAx] le one N) (hj : Γ ⊢[PRAAx] le j N) :
    Γ ⊢[PRAAx] distanceBounded
      (qsub (inst2 (sampleBody F) j (sampleData q N (one+zero) T one (fixedData X Y D sign R T zero)))
        (inst2 (sampleBody F) j (sampleData q N (one+zero) T one (fixedData (X+D) Y D sign S T zero))))
      (ap2 W q (wd X Y D sign R T (T*j) N)) (num 8) (unit q) := by
  have guard : Γ ⊢[PRAAx] le (T*j) (T*N) :=
    le_congr (mul_comm j T) (mul_comm N T) (mul_le_mul_right T hj)
  exact distance_congr (cell_samples j q N X Y D sign R S T).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (sample_difference q X Y D sign R S T (T*j) N (.andI h (.andI hN guard)) (.andI hs (.andI hN guard)))

end LeanProofs.IPRA.Analysis.GaussianBinetLaplaceWeightedGridReadback
