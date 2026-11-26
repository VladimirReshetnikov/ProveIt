import IPRADerivations.Analysis.Gamma.Zeta.Dirichlet.Square.GaussianGammaZetaDirichletSquareFinite
import IPRADerivations.Analysis.Gamma.Zeta.Dirichlet.GaussianGammaZetaDirichletCofinal
import IPRADerivations.Analysis.Stirling.Binet.Kernel.GaussianBinetBaselName

/-!
# The original cofinal Dirichlet name at two

The actual exponential Dirichlet prefix and the rational Basel prefix
agree at a common internal cutoff. Their respective tail estimates
then identify the two original names.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianGammaZetaDirichletSquareCofinal

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (oneCode)
open GaussianBinetBaselBinding (literalSum)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaZetaDirichletFiniteRate (prefixData)
open GaussianGammaZetaDirichletSquareFinite (original_finite_square)
open GaussianGammaZetaMellinDampedImproper (dirichletF)
open GaussianNameArithmetic (multiplyF multiplyData multiply_equivalent)
open GaussianNameEquivalence (crossEquivalent cross_at cross_to_diagonal cross_trans diagonal_refl)
open GaussianNameRingLaws (equivalent_of_envelope)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open RationalGaussianEmbedding (embed_at embedF)
open RationalReciprocalPowerTail (tail)
open RationalValueBounds (radius_of_upper upper_of_order)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "C" => GaussianGammaZetaDirichletCofinal.nameF
local notation "D" => GaussianGammaZetaDirichletCofinal.data
local notation "Z" => RationalGaussianNameEmbedding.nameF RationalReciprocalPowerName.zetaF
local notation "S" => GaussianEulerIntegralGammaIdentification.source
local notation "six" => fraction (num 6) one

private theorem rational_prefix_error (p N : PTm n) (h : Γ ⊢[PRAAx] le (RationalReciprocalPowerName.cutoff p) N) :
    Γ ⊢[PRAAx] distanceBounded (literalSum N) (ap2 Z p two) one (unit p) := by
  let M := RationalReciprocalPowerName.cutoff p
  let a := tail two zero M
  let b := tail two zero N
  have hM := RationalReciprocalPowerName.cutoff_positive (Γ := Γ) p
  have hp := unit_positive (Γ := Γ) p
  have ord := RationalReciprocalPowerName.later_order two zero M N (le_refl two) hM h
  have bound := RationalReciprocalPowerName.later_upper two zero M N (le_refl two) hM h
  have v := RationalGaussianNameEmbedding.distance_from_radius a b one M hM
    (radius_of_upper _ _ _ _ (upper_of_order _ _ _ _ ord) bound)
  have e := RationalReciprocalPowerName.zeta_sample_at (Γ := Γ) p two
  have read := (RationalGaussianNameEmbedding.sample_at (Γ := Γ) RationalReciprocalPowerName.zetaF p two).eqTrans
    ((embed_at _).eqSymm.eqTrans ((congrAp1 embedF e).eqTrans (embed_at a)))
  have narrow : Γ ⊢[PRAAx] le (one*unit p) (one*M) := by
    dsimp only [M,RationalReciprocalPowerName.cutoff,RationalReciprocalPowerName.unit,unit]
    ipra_le 3*Groth.ι (Q.mk Γ (pw two p))
  exact distance_congr (.eqRefl _) read.eqSymm (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ _ _ _ hM hp narrow (distance_symmetric _ _ _ _ hM v))

private theorem cofinal_prefix_error (p R A N : PTm n) (hz : Γ ⊢[PRAAx] S oneCode R one A)
    (hN : Γ ⊢[PRAAx] le (GaussianGammaZetaDirichletCofinal.cutoff A p) N) :
    Γ ⊢[PRAAx] distanceBounded (ap2 C p (D oneCode R one A)) (literalSum N) (num 4) (unit p) := by
  let x := prefixData N oneCode R one A
  let y := literalSum N
  let u := unit p
  have hu := unit_positive (Γ := Γ) p
  have hD := positive_product u u hu hu
  have initial := GaussianGammaZetaDirichletCofinal.late_observations p p N oneCode R one A hz hN
  have rows : Γ ⊢[PRAAx] crossEquivalent dirichletF constantF x y :=
    original_finite_square N (R+one) A
  have finite := cross_at dirichletF constantF x y p p rows
  have first := distance_radius_mono _ _ _ _ two u hD hu
    (le_of_eq_add (d := zero) (by dsimp only [u]; ipra_ring)) initial
  have second := distance_radius_mono _ _ _ _ two u hD hu
    (le_of_eq_add (d := zero) (by dsimp only [u]; ipra_ring))
    (distance_congr (.eqRefl _) (constant_at p y) (.eqRefl _) (.eqRefl _) finite)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hu first second)

theorem original_square_observations (p R A : PTm n) (hz : Γ ⊢[PRAAx] S oneCode R one A) :
    Γ ⊢[PRAAx] distanceBounded (ap2 C p (D oneCode R one A)) (ap2 Z p two) (num 5) (unit p) := by
  let M := GaussianGammaZetaDirichletCofinal.cutoff A p
  let N := RationalReciprocalPowerName.cutoff p
  have first := cofinal_prefix_error p R A (M+N) hz (le_add_right M N)
  have second := rational_prefix_error (Γ := Γ) p (M+N) (le_add_left N M)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ (unit_positive p) first second)

theorem original_square_zeta (R A : PTm n) (hz : Γ ⊢[PRAAx] S oneCode R one A) :
    Γ ⊢[PRAAx] crossEquivalent C Z (D oneCode R one A) two := by
  refine equivalent_of_envelope _ _ _ _ (num 5)
    (GaussianGammaZetaDirichletCofinal.regular oneCode R one A hz)
    (RationalGaussianNameEmbedding.name_regular RationalReciprocalPowerName.zetaF (two : PTm n)
      (RationalReciprocalPowerName.zeta_name_regular two (le_refl two))) (.allI ?_)
  have hs : Γ.map Fm.shift ⊢[PRAAx] S oneCode (Syn.shift R) one (Syn.shift A) := by
    simpa only [Fm.shift,Syn.shift,GaussianEulerIntegralGammaIdentification.subst_source,
      ComplexLogarithmRemainder.subst_oneCode,one,PTm.subst_succ,PTm.subst_zero] using hz.shift
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,Syn.shift,GaussianGammaZetaDirichletCofinal.data,
    ComplexLogarithmRemainder.subst_oneCode,GaussianGammaZetaMellinDampedImproper.subst_parameters,
    one,two,PTm.subst_succ,PTm.subst_zero,PTm.subst_num] using
    original_square_observations (var 0) (Syn.shift R) (Syn.shift A) hs

def sixDirichletF : PR 2 := multiplyF constantF C

def sixDirichletData (R A : PTm n) : PTm n :=
  multiplyData constantF C six (D oneCode R one A)

theorem original_dirichlet_Basel (R A : PTm n) (hz : Γ ⊢[PRAAx] S oneCode R one A) :
    Γ ⊢[PRAAx] crossEquivalent sixDirichletF GaussianBinetBaselName.piSquareF
      (sixDirichletData R A) GaussianBinetBaselName.piSquareData := by
  have e := original_square_zeta R A hz
  have prod := multiply_equivalent constantF constantF C Z six six (D oneCode R one A) two
    (constant_regular _) (constant_regular _) (GaussianGammaZetaDirichletCofinal.regular oneCode R one A hz)
    (RationalGaussianNameEmbedding.name_regular RationalReciprocalPowerName.zetaF (two : PTm n)
      (RationalReciprocalPowerName.zeta_name_regular two (le_refl two)))
    (diagonal_refl constantF _) (cross_to_diagonal _ _ _ _ e)
  exact cross_trans sixDirichletF GaussianBinetBaselName.sixZetaF GaussianBinetBaselName.piSquareF _ _ _
    prod GaussianBinetBaselName.original_Basel_identity

theorem actual_original_Dirichlet_Basel_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (S oneCode (var 0) one (var 1) ⟶
        crossEquivalent sixDirichletF GaussianBinetBaselName.piSquareF
          (sixDirichletData (var 0) (var 1)) GaussianBinetBaselName.piSquareData) :=
  closeUniv 2 (.impI (original_dirichlet_Basel _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaZetaDirichletSquareCofinal
