import IPRADerivations.Analysis.Gamma.EulerProducts.Weierstrass.GaussianGammaWeierstrassApproximant
import IPRADerivations.Analysis.Gamma.EulerProducts.Weierstrass.GaussianGammaWeierstrassConvergence
import IPRADerivations.Analysis.Names.Rates.Transport.GaussianNamedRateTransport

/-!
# The original C11 Weierstrass limit

The C11 rate holds for the literal factor-by-factor program at any
numerical truncation satisfying the source guards. The cofinal sampler
chooses a truncation at least the requested index and evaluates that
same program at one additional bit. Its actual output is a regular name
of the original C7 reciprocal, including where the polynomial head
vanishes.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaWeierstrassLimit

open_ipra
open GaussianGammaWeierstrassApproximant (literalF literalData original_finite_identity)
open GaussianGammaWeierstrassConvergence (source local_source rate data)
open GaussianGammaFiniteApproximantName (pF pData)
open GaussianNamedInverseRate (rateNumerator rateDenominator independentRate)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalHorner (positive_product)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianEuclideanDistanceName (pointCN)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

theorem folded_rate (z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B N) : Γ ⊢[PRAAx]
    independentRate pF GaussianGammaC7Name.nameF (pData z B N) (GaussianGammaC7Name.data z R B) (rate R) N := by
  refine .allI (.allI ?_)
  let z' := Syn.shift (Syn.shift z)
  let r := Syn.shift (Syn.shift R)
  let b := Syn.shift (Syn.shift B)
  let m := Syn.shift (Syn.shift N)
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] source z' r b m := by
    simpa [z',r,b,m,Fm.shift,Syn.shift] using h.shift.shift
  have f := GaussianGammaWeierstrassConvergence.observation_error (var 1) (var 0) z' r b m hs
  have same : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx]
      distanceBounded (ap2 pF (var 1) (pData z' b m)) (GaussianGammaC7Name.sample (var 0) z' r b)
        (rateNumerator (rate r) m (var 1) (var 0)) (rateDenominator m (var 1) (var 0)) := f
  simpa only [independentRate,Syn.shift,GaussianGammaC7Name.sample,GaussianGammaFoldedC9Bound.subst_pData,
    GaussianGammaC7Name.subst_data,GaussianGammaWeierstrassConvergence.subst_rate,z',r,b,m] using same

theorem literal_observation_rate (p q z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B N) : Γ ⊢[PRAAx]
    distanceBounded (ap2 literalF p (literalData z R B N)) (GaussianGammaC7Name.sample q z R B)
      (rateNumerator (rate R) N p q) (rateDenominator N p q) :=
  GaussianNamedRateTransport.observation_error pF GaussianGammaC7Name.nameF literalF GaussianGammaC7Name.nameF
    (pData z B N) (GaussianGammaC7Name.data z R B) (literalData z R B N)
    (GaussianGammaC7Name.data z R B) (rate R) N p q (local_source z R B N h).andE₂.andE₁
    (folded_rate z R B N h) (original_finite_identity z R B N h.andE₁)
    (cross_refl _ _ (GaussianGammaC7Name.name_regular z R B h.andE₁))

def cutoff (p R : PTm n) : PTm n := GaussianGammaWeierstrassConvergence.cutoff p R+p

ipra_subst cutoff

theorem cutoff_guards (p R : PTm n) : Γ ⊢[PRAAx]
    le p (cutoff p R) ⋏ (le (two*R) (cutoff p R) ⋏
      (le (R*R) (cutoff p R) ⋏ le (rate R*unit (succ p)) (cutoff p R))) := by
  have old := GaussianGammaWeierstrassConvergence.cutoff_guards (Γ := Γ) p R
  have up : Γ ⊢[PRAAx] le (GaussianGammaWeierstrassConvergence.cutoff p R) (cutoff p R) := le_add_right _ _
  exact .andI (le_add_left _ _) (.andI (le_trans old.andE₁ up)
    (.andI (le_trans old.andE₂.andE₁ up) (le_trans old.andE₂.andE₂ up)))

def observation (p z R B : PTm n) : PTm n := ap2 literalF (succ p) (literalData z R B (cutoff p R))
def nameF : PR 2 := PTm.toPR (observation (var 0) (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1))) : PTm 2)
def sample (p z R B : PTm n) : PTm n := ap2 nameF p (data z R B)

ipra_subst observation [literalData, GaussianGammaWeierstrassFiniteName.nameData, GaussianGammaWeierstrassApproximant.positiveExpData, GaussianGammaFiniteApproximantName.exponentialInputData, GaussianGammaWeierstrassApproximant.positiveExponentData]

theorem observation_congr {p p' z z' R R' B B' : PTm n}
    (hp : Γ ⊢[PRAAx] p ≐ p') (hz : Γ ⊢[PRAAx] z ≐ z') (hR : Γ ⊢[PRAAx] R ≐ R') (hB : Γ ⊢[PRAAx] B ≐ B') :
    Γ ⊢[PRAAx] observation p z R B ≐ observation p' z' R' B' := by
  ipra_congr (observation (var 0) (var 1) (var 2) (var 3) : PTm 4) with [hp, hz, hR, hB]

theorem sample_at (p z R B : PTm n) : Γ ⊢[PRAAx] sample p z R B ≐ observation p z R B := by
  let x := data z R B
  have e : Γ ⊢[PRAAx] sample p z R B ≐ observation p (fstT x) (fstT (sndT x)) (sndT (sndT x)) := by
    simpa [sample,nameF,ap2] using toPR_eq (Γ := Γ)
      (observation (var 0) (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1))) : PTm 2) ![p,x]
  have tail : Γ ⊢[PRAAx] sndT x ≐ pairT R B := snd_pair _ _
  exact e.eqTrans (observation_congr (.eqRefl _) (fst_pair _ _) tail.fstE
    tail.sndE)

theorem cofinal_observation_rate (p q z R B : PTm n) (h : Γ ⊢[PRAAx] GaussianGammaCanonicalExponent.source z R B) :
    Γ ⊢[PRAAx] distanceBounded (sample p z R B) (GaussianGammaC7Name.sample q z R B)
      (unit p+unit q) (unit p*unit q) := by
  let N := cutoff p R
  have guards := cutoff_guards (Γ := Γ) p R
  have hs : Γ ⊢[PRAAx] source z R B N := .andI h (.andI guards.andE₂.andE₁ guards.andE₂.andE₂.andE₁)
  have hN := (local_source z R B N hs).andE₂.andE₁
  have compare : Γ ⊢[PRAAx] le (rateNumerator (rate R) N (succ p) q*(unit p*unit q))
      ((unit p+unit q)*rateDenominator N (succ p) q) := by
    have e := natEq (pw_succ (Γ := Γ) two p)
    have hb : Γ ⊢[PRAAx] le (rate R*unit (succ p)) N := guards.andE₂.andE₂.andE₂
    ipra_le 𝔞 (unit p)*𝔞 (unit q)*𝔞 (unit q)*sl hb using
      unfold rateNumerator rateDenominator unit
      ipra_simps
      rw [e]
      ring
  exact distance_congr (sample_at p z R B).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ _ _ _ (GaussianNamedInverseRate.denominator_positive N (succ p) q hN)
      (positive_product _ _ (unit_positive p) (unit_positive q)) compare
      (literal_observation_rate (succ p) q z R B N hs))

theorem limit_equivalence (z R B : PTm n) (h : Γ ⊢[PRAAx] GaussianGammaCanonicalExponent.source z R B) :
    Γ ⊢[PRAAx] crossEquivalent nameF GaussianGammaC7Name.nameF (data z R B) (GaussianGammaC7Name.data z R B) := by
  refine .allI (.allI ?_)
  let z' := Syn.shift (Syn.shift z)
  let R' := Syn.shift (Syn.shift R)
  let B' := Syn.shift (Syn.shift B)
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] GaussianGammaCanonicalExponent.source z' R' B' := by
    simpa [Fm.shift,Syn.shift,z',R',B'] using h.shift.shift
  simpa only [crossEquivalent,sample,GaussianGammaC7Name.sample,Syn.shift,GaussianGammaWeierstrassConvergence.subst_data,
    GaussianGammaC7Name.subst_data,unit,GaussianEuclideanPointDistance.unit,z',R',B'] using
    cofinal_observation_rate (var 1) (var 0) z' R' B' hs

theorem limit_regular (z R B : PTm n) (h : Γ ⊢[PRAAx] GaussianGammaCanonicalExponent.source z R B) :
    Γ ⊢[PRAAx] pointCN nameF (data z R B) := by
  have e := limit_equivalence z R B h
  exact cross_trans _ _ _ _ _ _ e (cross_symm _ _ _ _ e)

theorem original_literal_C11_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source (var 2) (var 3) (var 4) (var 5) ⟶
      distanceBounded (ap2 literalF (var 0) (literalData (var 2) (var 3) (var 4) (var 5)))
        (GaussianGammaC7Name.sample (var 1) (var 2) (var 3) (var 4)) (rateNumerator (rate (var 3)) (var 5) (var 0) (var 1))
        (rateDenominator (var 5) (var 0) (var 1))) :=
  closeUniv 6 (.impI (literal_observation_rate _ _ _ _ _ _ Prf.hyp0))

theorem original_literal_C11_cofinal_cutoff_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le (var 0) (cutoff (var 0) (var 1)) ⋏ (le (two*var 1) (cutoff (var 0) (var 1)) ⋏
      (le (var 1*var 1) (cutoff (var 0) (var 1)) ⋏ le (rate (var 1)*unit (succ (var 0))) (cutoff (var 0) (var 1))))) :=
  closeUniv 2 (cutoff_guards _ _)

theorem actual_literal_C11_cofinal_sampler_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (sample (var 0) (var 1) (var 2) (var 3) ≐ observation (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (sample_at _ _ _ _)

theorem original_literal_C11_weierstrass_limit_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (GaussianGammaCanonicalExponent.source (var 0) (var 1) (var 2) ⟶ crossEquivalent nameF GaussianGammaC7Name.nameF
      (data (var 0) (var 1) (var 2)) (GaussianGammaC7Name.data (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (limit_equivalence _ _ _ Prf.hyp0))

theorem original_literal_C11_regular_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (GaussianGammaCanonicalExponent.source (var 0) (var 1) (var 2) ⟶ pointCN nameF (data (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (limit_regular _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaWeierstrassLimit
