import IPRADerivations.Analysis.Gamma.Digamma.GaussianDigammaFirstBernoulliPrefix
import IPRADerivations.Analysis.Gamma.Digamma.GaussianGammaDigammaElementaryBounds
import IPRADerivations.Analysis.Stirling.GaussianStirlingGlobalBounds

/-!
# The first improper Bernoulli remainder for the original digamma

The actual weighted prefix at an independently refined mesh
approximates log(x)−1/(2x)−ψ(x) with an explicit dyadic error.
The cutoff is the repository's shared cofinal Stirling cutoff.
-/

set_option autoImplicit false
set_option maxHeartbeats 2400000

namespace LeanProofs.IPRA.Analysis.GaussianDigammaFirstBernoulliImproper

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianDigammaFirstBernoulliPrefix (budget prefix_error)
open GaussianDigammaFirstBernoulliReference (harmonicPrefix)
open GaussianDigammaFirstBernoulliTelescope (meshTarget)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaDigammaFiniteSum (index row_source reciprocalSum reciprocalBody)
open GaussianGammaDigammaHarmonicCells (halfReciprocal)
open GaussianGammaDigammaHarmonicPrefix (endpointPair)
open GaussianGammaFiniteApproximantName (logF log_regular)
open GaussianHarmonicLogarithmName (sample sample_at)
open GaussianHarmonicLogarithmProduct (mesh mesh_later)
open GaussianNamedDifference (difference_distance sample_error)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (qadd qzero ofGaussian_canonical positive_product)
open GaussianRationalInverseQuadraticAlgebra (subtract_sum)
open GaussianRationalMetric (qsub qnegative bounded distanceBounded)
open GaussianRationalPowerDifference (distance_refl_zero)
open GaussianRationalReconstruction (qsub_zero_right)
open GaussianRationalSyntheticDivision (qadd_congr qsub_congr qzero_add)
open GaussianReciprocalHorner (qadd_commutative)
open GaussianStirlingAllOrderPanelPartsOuterFold (panelPrefix)
open GaussianStirlingGammaLogarithm (source)
open GaussianStirlingGlobalBounds (steps)
open RationalGaussianEmbedding (embed)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "H" => GaussianHarmonicLogarithmName.nameF
local notation "hd" => GaussianHarmonicLogarithmName.data
local notation "DF" => GaussianGammaDigammaNative.nameF
local notation "dd" => GaussianGammaDigammaNative.data
local notation "UF" => GaussianGammaDigammaElementaryBounds.nameF
local notation "ud" => GaussianGammaDigammaElementaryBounds.upperData
local notation "EF" => GaussianGammaDigammaEulerDerivative.nameF
local notation "ed" => GaussianGammaDigammaEulerDerivative.data

def baseF : PR 2 := GaussianNamedDifference.nameF UF DF
def baseData (a b : PTm n) : PTm n := GaussianNamedDifference.data (ud a b) (dd a b)

def meshDemand (p a b : PTm n) : PTm n := (one+budget a b (steps p))*unit p

@[simp] theorem subst_baseData {m : ℕ} (σ : Fin n → PTm m) (a b : PTm n) :
    Syn.subst σ (baseData a b) = baseData (Syn.subst σ a) (Syn.subst σ b) := by simp [baseData]

@[simp] theorem subst_meshDemand {m : ℕ} (σ : Fin n → PTm m) (p a b : PTm n) :
    Syn.subst σ (meshDemand p a b) = meshDemand (Syn.subst σ p) (Syn.subst σ a) (Syn.subst σ b) := by
  simp [meshDemand,steps,GaussianStirlingIntegerLimit.index]

theorem base_regular (a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] pointCN baseF (baseData a b) :=
  GaussianNamedDifference.name_regular _ _ _ _
    (GaussianGammaDigammaElementaryBounds.endpoint_regular a b _ hs) (GaussianGammaDigammaNative.name_regular a b hs)

theorem steps_later (p : PTm n) : Γ ⊢[PRAAx] le (unit p) (steps p) :=
  le_trans (GaussianStirlingIntegerLimit.index_dominates_unit p) (le_succ_self _)

private theorem cutoff_distance (p a b N : PTm n) (hs : Γ ⊢[PRAAx] source a b)
    (hLater : Γ ⊢[PRAAx] le (unit p) N) :
    Γ ⊢[PRAAx] distanceBounded (ap2 DF p (dd a b)) (qsub (ap2 logF p N) (reciprocalSum a b (succ N)))
      (a+num 10) (unit p) := by
  let U := unit p
  let R := reciprocalSum a b (succ N)
  have hp := unit_positive (Γ := Γ) p
  have hN := le_trans hp hLater
  have actual := GaussianGammaDigammaEulerDerivative.original_rate a b N hs hN
  have diag := GaussianNamedInverseRate.diagonal_rate DF EF _ _ _ N p hN actual
  have smaller := distance_radius_mono _ _ _ _ (a+num 4) U (positive_product _ _ hN hp) hp
    (by
      unfold U GaussianGammaDigammaEulerDerivative.rateCoefficient
      ipra_le (𝔞 a+2)*𝔞 (unit p)*sl hLater) diag
  have raw := distance_congr (.eqRefl _) (qsub_congr (.eqRefl _) (constant_at p R)) (.eqRefl _) (.eqRefl _)
    (sample_error logF constantF N R p (log_regular N hN) (constant_regular R))
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ U hp smaller raw)

private theorem harmonic_balance (p a b N Q : PTm n) (hs : Γ ⊢[PRAAx] source a b)
    (hN : Γ ⊢[PRAAx] le (unit p) N) (hQ : Γ ⊢[PRAAx] le (unit p) Q) :
    Γ ⊢[PRAAx] distanceBounded (qsub (ap2 logF p N) (harmonicPrefix a b Q N))
      (sample p a b) (a+num 12) (unit p) := by
  let h := ap2 logF p N
  let u := index a b N
  let U := unit p
  have hp := unit_positive (Γ := Γ) p
  have hu := (row_source a b N hs).andE₁
  have raw := GaussianStirlingAllOrderFirstPanelCommonMesh.harmonic_observations u a Q (mesh p) p hu hs.andE₁ hQ (mesh_later p)
  have same := distance_congr (.eqRefl _) (sample_at p u a).eqSymm (.eqRefl _) (.eqRefl _) raw
  have h0 := difference_distance h h _ _ zero two U hp (distance_refl_zero _ _ hp) same
  have h1 := GaussianGammaDigammaHarmonicLogBalance.cutoff_balance_of_le p a b N hs hN
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ U hp h0 h1)

private theorem tail_half (p a b N : PTm n) (hs : Γ ⊢[PRAAx] source a b)
    (hN : Γ ⊢[PRAAx] le (unit p) N) :
    Γ ⊢[PRAAx] distanceBounded (halfReciprocal (index a b N) b) qzero one (unit p) := by
  let u := index a b N
  let D := two*u
  let v := halfReciprocal u b
  have hD := positive_product _ _ (le_succ_self one) (row_source a b N hs).andE₁
  have raw := GaussianRationalReciprocal.bound_congr (GaussianEulerDecayFactorBounds.fraction_is_radius_point b D hD).eqSymm
    (.eqRefl _) (.eqRefl _) (GaussianDominantPairAlgebra.radius_bounded b D hD)
  have small : Γ ⊢[PRAAx] bounded v one (unit p) :=
    bounded_radius_mono _ _ _ _ _ hD (unit_positive p) (by
      unfold index
      ipra_le 𝔞 b*sl hN+2*𝔞 a+𝔞 N*𝔞 b) raw
  exact GaussianRationalReciprocal.bound_congr (qsub_zero_right v (ofGaussian_canonical _ _ hD)).eqSymm
    (.eqRefl _) (.eqRefl _) small

private theorem sub_swap (x y z : PTm n) : Γ ⊢[PRAAx] qsub (qsub x y) z ≐ qsub (qsub x z) y :=
  (subtract_sum x y z).eqTrans ((qsub_congr (.eqRefl _) (qadd_commutative y z)).eqTrans (subtract_sum x z y).eqSymm)

private theorem cancel_common (x y z : PTm n) (hz : Γ ⊢[PRAAx] GaussianRationalHorner.canonical z) :
    Γ ⊢[PRAAx] qsub (qsub x y) (qsub x z) ≐ qsub z y := by
  have negs : Γ ⊢[PRAAx] qsub (qnegative y) (qnegative z) ≐ qsub z y :=
    (qadd_congr (.eqRefl _) (GaussianDeterminantSignTransport.negative_involution z hz)).eqTrans (qadd_commutative _ _)
  exact (GaussianNameArithmetic.sum_difference x x (qnegative y) (qnegative z)).eqTrans
    ((qadd_congr (GaussianCoefficientNormOrder.qsub_self x) negs).eqTrans
      (qzero_add _ (GaussianRationalMetric.qsub_canonical _ _)))

private theorem raw_telescope (p a b N Q : PTm n) :
    Γ ⊢[PRAAx] meshTarget a b Q N ≐
      qsub (qsub (qsub (qsub (ap2 logF p N) (harmonicPrefix a b Q N)) (halfReciprocal a b))
        (qsub (ap2 logF p N) (reciprocalSum a b (succ N)))) (halfReciprocal (index a b N) b) := by
  let L := ap2 logF p N
  let R := reciprocalSum a b (succ N)
  let Y := harmonicPrefix a b Q N
  let c := halfReciprocal a b
  let d := halfReciprocal (index a b N) b
  have hR : Γ ⊢[PRAAx] GaussianRationalHorner.canonical R :=
    GaussianRationalFiniteSum.sum_canonical reciprocalBody _ _
  have eOne := (sub_swap (Γ := Γ) (qsub L Y) c (qsub L R)).eqTrans
    (qsub_congr (cancel_common L Y R hR) (.eqRefl c))
  have more := (qsub_congr (sub_swap (Γ := Γ) R Y c) (.eqRefl d)).eqTrans (sub_swap (qsub R c) Y d)
  exact ((qsub_congr eOne (.eqRefl d)).eqTrans
    (more.eqTrans (qsub_congr (subtract_sum R c d) (.eqRefl Y)))).eqSymm

private theorem named_sample (p a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] distanceBounded (ap2 baseF p (baseData a b))
      (qsub (qsub (sample p a b) (halfReciprocal a b)) (ap2 DF p (dd a b))) (num 12) (unit p) := by
  let c := halfReciprocal a b
  let y := ap2 DF p (dd a b)
  let U := unit p
  have hp := unit_positive (Γ := Γ) p
  have hD := GaussianGammaDigammaNative.name_regular a b hs
  have b0 := sample_error UF DF (ud a b) (dd a b) p
    (GaussianGammaDigammaElementaryBounds.endpoint_regular a b c hs) hD
  have t := distance_congr (.eqRefl _) (qsub_congr (.eqRefl _) (constant_at p c)) (.eqRefl _) (.eqRefl _)
    (sample_error H constantF (hd a b) c p (GaussianHarmonicLogarithmName.name_regular a b hs) (constant_regular c))
  have b1 := difference_distance _ _ y y _ zero U hp t (distance_refl_zero y U hp)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ U hp b0 b1)

theorem original_base_rate (p a b Q : PTm n) (hs : Γ ⊢[PRAAx] source a b)
    (hm : Γ ⊢[PRAAx] le (meshDemand p a b) Q) :
    Γ ⊢[PRAAx] distanceBounded (embed (panelPrefix 0 2 a b (b*Q) (steps p)))
      (ap2 baseF p (baseData a b)) (two*a+num 36) (unit p) := by
  let N := steps p
  let U := unit p
  let L := ap2 logF p N
  let Y := harmonicPrefix a b Q N
  let X := sample p a b
  let c := halfReciprocal a b
  let d := halfReciprocal (index a b N) b
  let F := qsub (qsub (qsub L Y) c) (qsub L (reciprocalSum a b (succ N)))
  let G := qsub (qsub X c) (ap2 DF p (dd a b))
  have hp := unit_positive (Γ := Γ) p
  have hn := steps_later (Γ := Γ) p
  have hq : Γ ⊢[PRAAx] le U Q := le_trans (by unfold meshDemand; ipra_le 𝔞 (budget a b N)*𝔞 U) hm
  have hQ := le_trans hp hq
  have hRate : Γ ⊢[PRAAx] le (budget a b N*U) (one*Q) := by
    have bnd : Γ ⊢[PRAAx] le (budget a b N*U) (meshDemand p a b) := by unfold meshDemand; ipra_le 𝔞 U
    exact le_congr (.eqRefl _) (one_mul Q).eqSymm (le_trans bnd hm)
  have panelDist := distance_radius_mono _ _ _ _ one U hQ hp hRate (prefix_error a b Q N hs hQ)
  have hlog := harmonic_balance p a b N Q hs hn hq
  have offset := difference_distance _ _ c c _ zero U hp hlog (distance_refl_zero c U hp)
  have cut := distance_symmetric _ _ _ _ hp (cutoff_distance p a b N hs hn)
  have d0 : Γ ⊢[PRAAx] distanceBounded F G ((a+num 12+zero)+(a+num 10)) U :=
    difference_distance _ _ _ _ _ _ _ hp offset cut
  have d1 := difference_distance F G d qzero _ one U hp d0 (tail_half p a b N hs hn)
  have h1 := distance_congr (raw_telescope p a b N Q).eqSymm (qsub_zero_right G (GaussianRationalMetric.qsub_canonical _ _))
    (.eqRefl _) (.eqRefl _) d1
  have h2 := distance_triangle_same _ _ _ _ _ U hp panelDist h1
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ U hp h2 (distance_symmetric _ _ _ _ hp (named_sample p a b hs)))

theorem actual_original_first_digamma_improper_rate_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (source (var 1) (var 2) ⟶ le (meshDemand (var 0) (var 1) (var 2)) (var 3) ⟶
        distanceBounded (embed (panelPrefix 0 2 (var 1) (var 2) ((var 2)*(var 3)) (steps (var 0))))
          (ap2 baseF (var 0) (baseData (var 1) (var 2))) (two*(var 1)+num 36) (unit (var 0))) :=
  closeUniv 4 (.impI (.impI (original_base_rate _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianDigammaFirstBernoulliImproper
