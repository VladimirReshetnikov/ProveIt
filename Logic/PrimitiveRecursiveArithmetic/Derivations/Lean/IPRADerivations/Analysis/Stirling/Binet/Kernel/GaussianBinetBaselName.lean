import IPRADerivations.Analysis.Stirling.Binet.Kernel.GaussianBinetBaselBinding
import IPRADerivations.Analysis.Stirling.Binet.Kernel.GaussianBinetKernelPi
import IPRADerivations.Analysis.Names.GaussianNameRingLaws
import IPRADerivations.Analysis.Names.Rates.Reciprocals.GaussianApproximateInverseDistance

/-!
# The Basel identity for the original zeta and π names

A late Basel grid compares with the original π grid through their common
Wallis approximant. The literal reciprocal-square tail then connects the
same finite Basel sum to the original cofinal zeta sampler at exponent two.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace LeanProofs.IPRA.Analysis.GaussianBinetBaselName

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep (pos_of_one_le)
open BaselUniform (cut)
open GaussianBinetBaselBinding (literalSum)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaHalfPiName (meshAt ordered_grid_error large_mesh_error)
open GaussianGammaHalfRisingFactorial (factorial_positive)
open GaussianGammaHalfWallisRate (piGrid)
open GaussianNameArithmetic (multiplyF multiplyData multiplyModulus multiply_fast product_distance)
open GaussianNameEquivalence (crossEquivalent)
open GaussianNameRingLaws (equivalent_of_envelope multiply_sample_error)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (positive_product qmul)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalSyntheticDivision (qmul_congr)
open Products (fact)
open RationalGaussianEmbedding (embed embed_at embedF)
open RationalReciprocalPowerTail (tail)
open RationalValueBounds (radius radius_of_upper upper_of_order)
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num pred)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "P" => GaussianGammaHalfPiName.nameF
local notation "Z" => RationalGaussianNameEmbedding.nameF RationalReciprocalPowerName.zetaF
local notation "piSample" => GaussianBinetKernelPi.sample
local notation "six" => fraction (num 6) one

def gridClock (p : PTm n) : PTm n := GaussianFastValueCut.exponent (meshAt p) p
def minimumCutoff (p : PTm n) : PTm n := cut (gridClock p)

private theorem grid_clock_late (p : PTm n) : Γ ⊢[PRAAx] le p (gridClock p) := le_add_right _ _

private theorem mesh_le_cutoff (p : PTm n) : Γ ⊢[PRAAx] le (meshAt p) (minimumCutoff p) := by
  let k := gridClock p
  have leU : Γ ⊢[PRAAx] le (meshAt p) (meshAt p*unit p) :=
    le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right (meshAt p) (unit_positive p))
  have h := GaussianFastValueCut.query_budget (Γ := Γ) (meshAt p) p
  have last : Γ ⊢[PRAAx] le (unit k) (cut k) :=
    GaussianExponentialReference.unit_monotone (le_of_eq_add (d := k+num 7) (by ipra_ring))
  exact le_trans leU (le_trans h last)

private theorem pi_grid_congr (M K L : PTm n) (e : Γ ⊢[PRAAx] M ≐ K) : Γ ⊢[PRAAx] piGrid M L ≐ piGrid K L :=
  GaussianCompactRiemannName.fraction_congr _ _ _ _
    (congrMul (.eqRefl _) (congrAp2 (sumF BaselQuadrature.Qb) e (congrPairT e (.eqRefl _)))) (.eqRefl _)

theorem grid_distance (p M L : PTm n) (hM : Γ ⊢[PRAAx] le (meshAt p) M)
    (hL : Γ ⊢[PRAAx] le (two*(M*M)) L) : Γ ⊢[PRAAx] distanceBounded (piGrid M L) (piSample p) one (unit p) := by
  let U := unit p
  have hU := unit_positive (Γ := Γ) p
  have hD := positive_product _ _ (le_succ_self one) hU
  have h : Γ ⊢[PRAAx] le one M := le_trans (zero_lt_succ _) hM
  have e : Γ ⊢[PRAAx] M ≐ succ (pred M) := pos_of_one_le h
  have hGrid : Γ ⊢[PRAAx] GaussianGammaHalfWallisRate.gridSource (pred M) L :=
    le_congr (congrMul (.eqRefl _) (congrMul e e)) (.eqRefl _) hL
  have a := large_mesh_error p (pred M) L (le_congr (.eqRefl _) e hM) hGrid
  have b := ordered_grid_error (Γ := Γ) p p (le_refl _)
  have raw := distance_triangle_same _ _ _ one one (two*U) hD (distance_symmetric _ _ _ _ hD a) b
  exact distance_congr (pi_grid_congr _ _ _ e.eqSymm) (GaussianGammaHalfPiName.sample_at p zero).eqSymm
    (.eqRefl _) (.eqRefl _) (distance_radius_mono _ _ _ _ _ _ hD hU
      (le_of_eq_add (d := zero) (by ipra_ring)) raw)

private theorem grid_bound (M L : PTm n) (hM : Γ ⊢[PRAAx] le one M)
    (hL : Γ ⊢[PRAAx] le (two*(M*M)) L) : Γ ⊢[PRAAx] bounded (piGrid M L) (num 4) one := by
  have e : Γ ⊢[PRAAx] M ≐ succ (pred M) := pos_of_one_le hM
  have raw := BaselRiemann.Q_le (M₀ := pred M) (le_congr (congrMul (.eqRefl _) (congrMul e e)) (.eqRefl _) hL)
  have q := congrAp2 (sumF BaselQuadrature.Qb) e.eqSymm (congrPairT e.eqSymm (.eqRefl L))
  have bound := le_congr q (.eqRefl _) raw
  exact GaussianEulerExponentCompactBounds.fraction_bound _ _ (num 4) (factorial_positive L)
    (le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right (num 4) bound))

/-- Every sufficiently late literal cutoff approximates the square of
the actual original π observation with the same explicit dyadic error. -/
theorem finite_vs_named_pi (p m : PTm n) (hm : Γ ⊢[PRAAx] le (minimumCutoff p) m) : Γ ⊢[PRAAx]
    distanceBounded (qmul six (literalSum m)) (qmul (piSample p) (piSample p)) (num 10) (unit p) := by
  let N := minimumCutoff p
  let M := N*N
  let H := succ (two*N)
  let Q := two*(M*M)
  let L := m+H+Q
  have hmL : Γ ⊢[PRAAx] le m L := le_trans (le_add_right m H) (le_add_right (m+H) Q)
  have hL : Γ ⊢[PRAAx] le H L := le_trans (le_add_left H m) (le_add_right (m+H) Q)
  have hQ : Γ ⊢[PRAAx] le Q L := le_add_left Q (m+H)
  have hN : Γ ⊢[PRAAx] le one N := unit_positive _
  have hM : Γ ⊢[PRAAx] le one M := positive_product N N hN hN
  have grow : Γ ⊢[PRAAx] le N M := le_congr (by ipra_ring) (.eqRefl _) (mul_le_mul_right N hN)
  have hMesh := le_trans (mesh_le_cutoff p) grow
  have hu := unit_positive (Γ := Γ) p
  have base := GaussianBinetBaselBinding.finite_Basel_distance (gridClock p) m L hm hL hQ hmL
  have a := distance_radius_mono _ _ _ _ one (unit p) (unit_positive _) hu
    (le_congr (by ipra_ring) (by ipra_ring) (GaussianExponentialReference.unit_monotone (grid_clock_late p))) base
  have near := grid_distance p M L hMesh hQ
  have b := product_distance (piGrid M L) (piSample p) (piGrid M L) (piSample p) one one (unit p)
    (num 4) (num 5) hu near near (grid_bound M L hM hQ) (GaussianBinetKernelPi.sample_bound p)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hu a b)

private theorem literal_gap (p m : PTm n) (h : Γ ⊢[PRAAx] le (RationalReciprocalPowerName.cutoff p) m) :
    Γ ⊢[PRAAx] distanceBounded (ap2 Z p two) (literalSum m) one (unit p) := by
  let N := RationalReciprocalPowerName.cutoff p
  let x := tail two zero N
  let y := tail two zero m
  have hn := RationalReciprocalPowerName.cutoff_positive (Γ := Γ) p
  have hu := unit_positive (Γ := Γ) p
  have ord := RationalReciprocalPowerName.later_order two zero N m (le_refl two) hn h
  have r : Γ ⊢[PRAAx] radius x y one N := radius_of_upper _ _ _ _
    (upper_of_order _ _ _ _ ord) (RationalReciprocalPowerName.later_upper two zero N m (le_refl two) hn h)
  have d := RationalGaussianNameEmbedding.distance_from_radius x y one N hn r
  have e := RationalReciprocalPowerName.zeta_sample_at (Γ := Γ) p two
  have ee := (embed_at (ap2 RationalReciprocalPowerName.zetaF p two)).eqSymm.eqTrans
    ((congrAp1 embedF e).eqTrans (embed_at x))
  have measure : Γ ⊢[PRAAx] le (one*unit p) (one*N) := by
    dsimp only [N,RationalReciprocalPowerName.cutoff,RationalReciprocalPowerName.unit,unit]
    ipra_le 3*Groth.ι (Q.mk Γ (pw two p))
  exact distance_congr ((RationalGaussianNameEmbedding.sample_at RationalReciprocalPowerName.zetaF p two).eqTrans ee).eqSymm
    (.eqRefl _) (.eqRefl _) (.eqRefl _) (distance_radius_mono _ _ _ _ _ _ hn hu measure d)

theorem raw_observations (p : PTm n) : Γ ⊢[PRAAx]
    distanceBounded (qmul six (ap2 Z p two)) (qmul (piSample p) (piSample p)) (num 16) (unit p) := by
  let N := RationalReciprocalPowerName.cutoff p
  let M := minimumCutoff p+N
  have hu := unit_positive (Γ := Γ) p
  have d := literal_gap (Γ := Γ) p M (le_add_left N (minimumCutoff p))
  have sixBound : Γ ⊢[PRAAx] bounded (six : PTm n) (num 6) one :=
    GaussianEulerExponentCompactBounds.fraction_bound _ _ _ (le_refl one) (by ipra_le 0)
  have a := GaussianApproximateInverseDistance.multiply_distance six _ _ (num 6) one (unit p) hu sixBound d
  have b := finite_vs_named_pi (Γ := Γ) p M (le_add_right (minimumCutoff p) N)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hu a b)

def sixZetaF : PR 2 := multiplyF constantF Z
def sixZetaData : PTm n := multiplyData constantF Z six two
def piSquareF : PR 2 := multiplyF P P
def piSquareData : PTm n := multiplyData P P zero zero

private def namedBudget : PTm n :=
  (multiplyModulus constantF Z six two+one)+num 16+(multiplyModulus P P zero zero+one)

private theorem diagonal (p : PTm n) : Γ ⊢[PRAAx] distanceBounded
    (ap2 sixZetaF p sixZetaData) (ap2 piSquareF p piSquareData) namedBudget (unit p) := by
  have hp := unit_positive (Γ := Γ) p
  have hr := RationalGaussianNameEmbedding.name_regular (Γ := Γ) RationalReciprocalPowerName.zetaF (two : PTm n)
    (RationalReciprocalPowerName.zeta_name_regular two (le_refl two))
  have hPi := GaussianGammaHalfPiName.name_regular (Γ := Γ) (zero : PTm n)
  have a := multiply_sample_error constantF Z six two p (constant_regular _) hr
  have a' := distance_congr (.eqRefl _) (qmul_congr (constant_at p six) (.eqRefl _)) (.eqRefl _) (.eqRefl _) a
  have b := raw_observations (Γ := Γ) p
  have c := distance_symmetric _ _ _ _ hp (multiply_sample_error P P zero zero p hPi hPi)
  exact distance_triangle_same _ _ _ _ _ _ hp (distance_triangle_same _ _ _ _ _ _ hp a' b) c

theorem original_Basel_identity : Γ ⊢[PRAAx] crossEquivalent sixZetaF piSquareF (sixZetaData : PTm n) piSquareData := by
  have hr := RationalGaussianNameEmbedding.name_regular (Γ := Γ) RationalReciprocalPowerName.zetaF (two : PTm n)
    (RationalReciprocalPowerName.zeta_name_regular two (le_refl two))
  have hPi := GaussianGammaHalfPiName.name_regular (Γ := Γ) (zero : PTm n)
  refine equivalent_of_envelope _ _ _ _ namedBudget
    (multiply_fast constantF Z six two (constant_regular _) hr) (multiply_fast P P zero zero hPi hPi) (.allI ?_)
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal, sixZetaData, piSquareData, namedBudget,
    GaussianNameArithmetic.subst_multiplyData, GaussianNameArithmetic.subst_multiplyModulus,
    GaussianPositiveRationalLogarithm.subst_fraction, PTm.subst_add, PTm.subst_num, Syn.shift, one, two,
    ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] using diagonal (Γ := Γ.map Fm.shift) (var 0)

theorem actual_original_Basel_identity_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] crossEquivalent sixZetaF piSquareF sixZetaData piSquareData :=
  original_Basel_identity

end LeanProofs.IPRA.Analysis.GaussianBinetBaselName
