import IPRADerivations.Analysis.Barnes.Logarithms.CofinalTails.GaussianBarnesCanonicalCombinedRemainder
import IPRADerivations.Analysis.Gamma.EulerProducts.CanonicalProducts.GaussianGammaCanonicalTailExponential
import IPRADerivations.Analysis.Names.Rates.GaussianNamedRateRadius

/-!
# Independent rates for the Barnes shift remainder and its exponential

The logarithmic bound is uniform in the cutoff and encoded denominator.
The original exponential uses one certified disk and tends to one with
an explicit numerator over the same cutoff.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalCombinedRemainderRate

open_ipra
open GaussianBarnesCanonicalCombinedRemainder (nameF data regular sample_error)
open GaussianBarnesCanonicalTerminalRemainder (source)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNameEquivalence (crossEquivalent cross_refl)
open GaussianNamedInverseRate (independentRate)
open GaussianRationalHorner (positive_product qzero)
open GaussianRationalMetric (bounded)
open GaussianRationalSyntheticDivision (qone)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "E" => GaussianRadiusExponentialName.nameF
local notation "ed" => GaussianRadiusExponentialName.data

def coefficient (R M : PTm n) : PTm n := R*R+M+one
def observationCost (M : PTm n) : PTm n := num 17*M+num 18
def radius (R M : PTm n) : PTm n := coefficient R M+observationCost M
def expData (c M w R B K : PTm n) : PTm n := ed (radius R M) (data c w R B K)

@[simp] theorem subst_coefficient {m : ℕ} (σ : Fin n → PTm m) (R M : PTm n) :
    Syn.subst σ (coefficient R M) = coefficient (Syn.subst σ R) (Syn.subst σ M) := by simp [coefficient,one]

@[simp] theorem subst_observationCost {m : ℕ} (σ : Fin n → PTm m) (M : PTm n) :
    Syn.subst σ (observationCost M) = observationCost (Syn.subst σ M) := by simp [observationCost]

theorem logarithm_rate (c M w R B K : PTm n) (h : Γ ⊢[PRAAx] source w R B K) (hc : Γ ⊢[PRAAx] bounded c M one) :
    Γ ⊢[PRAAx] independentRate nameF constantF (data c w R B K) qzero (coefficient R M) K := by
  apply GaussianNamedLipschitzRate.independent_rate _ _ _ _ _ _ (observationCost M) h.andE₂.andE₁
    (regular c w R B K h) (constant_regular _)
  refine .allI ?_
  let Δ := Γ.map Fm.shift
  let sh (t : PTm n) := Syn.shift t
  have hs : Δ ⊢[PRAAx] source (sh w) (sh R) (sh B) (sh K) := by simpa [Fm.shift,Syn.shift,Δ,sh] using h.shift
  have cs : Δ ⊢[PRAAx] bounded (sh c) (sh M) one := by simpa [Fm.shift,Syn.shift,Δ,sh,one] using hc.shift
  have obs := sample_error (var 0) (sh c) (sh M) (sh w) (sh R) (sh B) (sh K) hs cs
  simpa only [GaussianNamedLipschitzRate.diagonalEnvelope,GaussianNamedLipschitzRate.diagonalNumerator,
    GaussianNamedLipschitzRate.diagonalDenominator,subst_coefficient,subst_observationCost,
    GaussianBarnesCanonicalCombinedRemainder.subst_data,GaussianRationalHorner.subst_qzero,
    coefficient,observationCost,PTm.subst_add,PTm.subst_mul,PTm.subst_num,one,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift,Δ,sh] using
      GaussianRationalDistanceOrder.distance_congr (.eqRefl _) (constant_at (var 0) qzero).eqSymm (.eqRefl _) (.eqRefl _) obs

theorem sample_bound (p c M w R B K : PTm n) (h : Γ ⊢[PRAAx] source w R B K) (hc : Γ ⊢[PRAAx] bounded c M one) :
    Γ ⊢[PRAAx] bounded (ap2 nameF p (data c w R B K)) (radius R M) one := by
  let A := coefficient R M
  let C := observationCost M
  let U := unit p
  have hK := h.andE₂.andE₁
  have hU := unit_positive (Γ := Γ) p
  have hn := positive_product K U hK hU
  have clear : Γ ⊢[PRAAx] le ((A*U+C*K)*one) ((A+C)*(K*U)) := by
    ipra_le 𝔞 A*𝔞 U*sl hK+𝔞 C*𝔞 K*sl hU
  exact (GaussianReconstructionRoots.distance_zero_iff _ _ _ (le_refl one)).iffMp
    (GaussianRationalDistanceOrder.distance_radius_mono _ _ _ _ (radius R M) one hn (le_refl one) clear
      (sample_error p c M w R B K h hc))

theorem exponential_input (c M w R B K : PTm n) (h : Γ ⊢[PRAAx] source w R B K)
    (hc : Γ ⊢[PRAAx] bounded c M one) : Γ ⊢[PRAAx] GaussianRadiusExponentialName.input nameF (radius R M) (data c w R B K) := by
  refine .andI (regular c w R B K h) (.allI ?_)
  let Δ := Γ.map Fm.shift
  let sh (t : PTm n) := Syn.shift t
  have hs : Δ ⊢[PRAAx] source (sh w) (sh R) (sh B) (sh K) := by simpa [Fm.shift,Syn.shift,Δ,sh] using h.shift
  have cs : Δ ⊢[PRAAx] bounded (sh c) (sh M) one := by simpa [Fm.shift,Syn.shift,Δ,sh,one] using hc.shift
  simpa [GaussianRadiusExponentialName.boundedSamples,radius,Syn.shift,Δ,sh] using
    sample_bound (var 0) (sh c) (sh M) (sh w) (sh R) (sh B) (sh K) hs cs

private theorem exponential_zero_samples (R : PTm n) (h : Γ ⊢[PRAAx] GaussianRadiusExponentialName.input constantF R qzero) :
    Γ ⊢[PRAAx] crossEquivalent (E constantF) constantF (ed R qzero) qone := by
  apply GaussianNameConjugation.equal_samples_cross _ _ _ _
    (GaussianRadiusExponentialName.name_regular _ _ _ h) (constant_regular _)
  refine .allI ?_
  let Δ := Γ.map Fm.shift
  let T := Syn.shift R
  let p : PTm (n+1) := var 0
  let i := GaussianRadiusExponentialName.inputPrecision T p
  let j := GaussianRadiusExponentialName.index T p
  have e := (GaussianRadiusExponentialName.sample_at (Γ := Δ) constantF T p qzero).eqTrans
    (GaussianNameConjugation.scalar_sum_congr j (constant_at i qzero))
  simpa only [GaussianNameConjugation.pointwiseEqual,GaussianRadiusExponentialName.subst_data,
    GaussianRationalHorner.subst_qzero,GaussianRationalSyntheticDivision.subst_qone,
    GaussianRadiusExponentialName.sample,Syn.shift,Δ,T,p] using
    e.eqTrans ((GaussianGammaCanonicalTailExponential.scalar_zero_point j).eqTrans (constant_at p qone).eqSymm)

theorem exponential_rate (c M w R B K : PTm n) (h : Γ ⊢[PRAAx] source w R B K) (hc : Γ ⊢[PRAAx] bounded c M one) :
    Γ ⊢[PRAAx] independentRate (E nameF) constantF (expData c M w R B K) qone
      (GaussianRadiusExponentialLipschitzRate.factor (radius R M)*coefficient R M) K := by
  let A := radius R M
  let x := data c w R B K
  have hK := h.andE₂.andE₁
  have ix := exponential_input c M w R B K h hc
  have iz := GaussianSignedNameExponentialOrder.constant_input (Γ := Γ) qzero A (GaussianMonicResidualRadius.zero_bounded _ _ (le_refl one))
  have join : Γ ⊢[PRAAx] GaussianRadiusExponentialLipschitzRate.input nameF constantF A x qzero (coefficient R M) K :=
    .andI hK (.andI ix (.andI iz (logarithm_rate c M w R B K h hc)))
  have e := GaussianRadiusExponentialLipschitzRate.independent_rate nameF constantF A x qzero (coefficient R M) K join
  have xr := GaussianRadiusExponentialName.name_regular nameF A x ix
  exact GaussianNamedRateTransport.transport (E nameF) (E constantF) (E nameF) constantF (ed A x) (ed A qzero)
    (ed A x) qone (GaussianRadiusExponentialLipschitzRate.factor A*coefficient R M) K hK e
    (cross_refl _ _ xr) (GaussianNameEquivalence.cross_symm _ _ _ _ (exponential_zero_samples A iz))

theorem actual_Barnes_exponential_remainder_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (let c := var 0
     let M := var 1
     let w := var 2
     let R := var 3
     let B := var 4
     let K := var 5
     source w R B K ⟶ bounded c M one ⟶ independentRate (E nameF) constantF (expData c M w R B K) qone
       (GaussianRadiusExponentialLipschitzRate.factor (radius R M)*coefficient R M) K) :=
  closeUniv 6 (.impI (.impI (exponential_rate _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalCombinedRemainderRate
