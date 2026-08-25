import GowersSzemeredi.Proofs16BaseCaseExtraction
import GowersSzemeredi.Proofs16BaseCaseSingleGraph

/-!
# Finite-family assembly for the repaired Lemma 16.3

This module assembles the extracted finite family of Freiman graphs.  The only
remaining input is the repaired finite-union closure, isolated as
`ProperUnionClosure`; the Section 16 union theorem is intended to discharge it
when the repaired catalogue is integrated.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi.BaseCase

lemma properMultiplyLinear_downward {N k : Nat} [NeZero N]
    {gamma r : Real} {Gamma Gamma' : Finset (Point N k × ZMod N)}
    (hsub : Gamma' ⊆ Gamma) (hGamma : ProperMultiplyLinear gamma r Gamma) :
    ProperMultiplyLinear gamma r Gamma' := by
  intro eta heta hetaOne P hP
  obtain ⟨M, q, H, Q, mu, hHsub, hHcard, hpart, hQproper, hq,
      hwidth, hmu, hcover⟩ := hGamma eta heta hetaOne P hP
  refine ⟨M, q, H, Q, mu, hHsub, hHcard, hpart, hQproper, hq,
    hwidth, hmu, ?_⟩
  intro j x hxQ hxH y hxy
  exact hcover j x hxQ hxH y (hsub hxy)

lemma lemma163Alpha_le_gammaInvSq {gamma theta : Real}
    (hgamma : 0 < gamma) (hgammaOne : gamma ≤ 1)
    (htheta : 0 < theta) (hthetaOne : theta ≤ 1) :
    lemma163Alpha gamma theta ≤ gamma ^ (-(2 : Int)) := by
  have ha : 0 ≤ gamma * theta := by positivity
  have haOne : gamma * theta ≤ 1 := by
    calc
      gamma * theta ≤ 1 * 1 :=
        mul_le_mul hgammaOne hthetaOne htheta.le (by norm_num)
      _ = 1 := by norm_num
  have halphaOne : lemma163Alpha gamma theta ≤ 1 := by
    unfold lemma163Alpha
    have hpow : (gamma * theta) ^ (10000 : Nat) ≤ 1 := pow_le_one₀ ha haOne
    have htwo : (2 : Real) ^ (-(2000 : Real)) ≤ 1 := by
      calc
        (2 : Real) ^ (-(2000 : Real)) ≤ (2 : Real) ^ (0 : Real) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 1 := by simp
    calc
      (2 : Real) ^ (-(2000 : Real)) * (gamma * theta) ^ (10000 : Nat) ≤
          1 * 1 := mul_le_mul htwo hpow (by positivity) (by norm_num)
      _ = 1 := by norm_num
  have hone : (1 : Real) ≤ gamma ^ (-(2 : Int)) := by
    rw [zpow_neg]
    have hsq : gamma ^ (2 : Nat) ≤ 1 := pow_le_one₀ hgamma.le hgammaOne
    exact (one_le_inv₀ (by positivity)).2 hsq
  exact halphaOne.trans hone

lemma properMultiplyLinear_empty_base {N : Nat} [NeZero N]
    (gamma theta : Real) (hgamma : 0 < gamma) (hgammaOne : gamma ≤ 1)
    (htheta : 0 < theta) (hthetaOne : theta ≤ 1) :
    ProperMultiplyLinear gamma (lemma163Iteration gamma theta)
      (∅ : Finset (Point N 1 × ZMod N)) := by
  have hqBound : ((1 : Nat) : Real) * lemma163Alpha gamma theta ≤
      gamma ^ (-(2 : Int)) := by
    simpa using lemma163Alpha_le_gammaInvSq hgamma hgammaOne htheta hthetaOne
  intro eta heta hetaOne P hP
  have hb := lemma163_local_bounds hgamma hgammaOne htheta hthetaOne heta hetaOne
    (q := 1) (by norm_num) hqBound
  have hwOne : lemma163LocalExponent gamma theta eta 1 ≤ 1 := by
    have h := lemma163_exponent_le_corollary_half hgamma hgammaOne htheta
      hthetaOne heta hetaOne (q := 1) (by norm_num) hqBound
    have ha : lemma163CorollaryExponent eta / 2 ≤ 1 := by
      unfold lemma163CorollaryExponent
      have hetaSq : eta ^ (2 : Nat) ≤ 1 := pow_le_one₀ heta.le hetaOne
      have hp : (2 : Real) ^ (-(14 : Real)) ≤ 1 := by
        calc
          (2 : Real) ^ (-(14 : Real)) ≤ (2 : Real) ^ (0 : Real) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
          _ = 1 := by simp
      nlinarith
    exact h.trans ha
  have hwidth : (P.width : Real) ^ lemma163LocalExponent gamma theta eta 1 ≤
      P.width := by
    by_cases hzero : P.width = 0
    · simpa only [hzero, Nat.cast_zero, Real.zero_rpow hb.1.ne'] using
        (le_rfl : (0 : Real) ≤ 0)
    · exact Real.rpow_le_self_of_one_le (by exact_mod_cast
        (Nat.one_le_iff_ne_zero.mpr hzero)) hwOne
  refine ⟨1, 0, P.carrier, (fun _ : Fin 1 => P), (fun _ i => Fin.elim0 i),
    Finset.Subset.rfl, ?_, ?_, (by simpa using hP), ?_, ?_, ?_, ?_⟩
  · have hc : (0 : Real) ≤ P.carrier.card := by positivity
    nlinarith
  · constructor
    · intro x
      simp
    · intro i j hij
      exact ((bne_iff_ne.mp hij) (Subsingleton.elim i j)).elim
  · have hnonneg : (0 : Real) ≤ lemma163LocalGraphBound gamma theta eta 1 :=
      (by positivity : (0 : Real) ≤
        (2 : Real) ^ (512 : Nat) * eta ^ (-(2 : Int))).trans hb.2.2
    simpa only [Nat.cast_zero, lemma163LocalGraphBound,
      lemma163StageIteration, Nat.cast_one, div_one] using hnonneg
  · simpa [lemma163LocalExponent, lemma163StageIteration] using hwidth
  · intro j i
    exact Fin.elim0 i
  · intro j x hxQ hxH y hxy
    simp at hxy

/-- The repaired finite-union closure needed by the base-case assembly. -/
def ProperUnionClosure : Prop :=
  ∀ (N d r : Nat) [NeZero N] (gamma s : Real)
      (Gamma : Fin r → Finset (Point N d × ZMod N)),
    0 < r → 1 ≤ s → (∀ i, ProperMultiplyLinear gamma s (Gamma i)) →
    ProperMultiplyLinear gamma ((r : Real) * s) (section16FinsetUnion Gamma)

/-- Repaired one-dimensional theorem, conditional only on finite-union
closure. -/
theorem proper_lemma_16_3_of_unionClosure
    (hunion : ProperUnionClosure) : ProperTheorem162At 1 := by
  intro gamma theta hgamma hgammaOne htheta hthetaOne
  refine ⟨0, ?_⟩
  intro N _ hprime hN Gamma hGamma hrelation
  have hGamma' : (Gamma.card : Real) ≤ gamma ^ (-(2 : Int)) * N := by
    simpa using hGamma
  let E := section16_extract_base_family gamma theta hgamma hgammaOne htheta
    hthetaOne hprime.out Gamma hGamma' hrelation
  refine ⟨E.J, ?_, ?_⟩
  · simpa using E.Jcard
  by_cases hq : E.q = 0
  · have hcoverEmpty : restrictRelation Gamma E.J ⊆
        (∅ : Finset (Point N 1 × ZMod N)) := by
      intro z hz
      have hzUnion := E.cover hz
      rw [section16FinsetUnion, Finset.mem_biUnion] at hzUnion
      obtain ⟨i, -, -⟩ := hzUnion
      have hi0 : (i : Nat) < 0 := by
        simpa [hq] using i.isLt
      omega
    exact properMultiplyLinear_downward hcoverEmpty
      (properMultiplyLinear_empty_base gamma theta hgamma hgammaOne htheta hthetaOne)
  have hqPos : 0 < E.q := Nat.pos_of_ne_zero hq
  let s := lemma163StageIteration gamma theta E.q
  have hs : (1 : Real) ≤ s := by
    exact (one_le_pow₀ (by norm_num : (1 : Real) ≤ 2)).trans
      (lemma163_stage_large hgamma hgammaOne htheta hthetaOne hqPos E.count)
  let G : Fin E.q → Finset (Point N 1 × ZMod N) :=
    fun i => partialGraph (E.B i) (E.phi i)
  have hG : ∀ i, ProperMultiplyLinear gamma s (G i) := by
    intro i
    exact section16_freiman_graph_multiplyLinear gamma theta hgamma hgammaOne
      htheta hthetaOne hqPos E.count hprime.out (E.B i) (E.phi i) (E.freiman i)
  have hUnion := hunion N 1 E.q gamma s G hqPos hs hG
  have hiteration : (E.q : Real) * s = lemma163Iteration gamma theta := by
    have hqReal : (E.q : Real) ≠ 0 := by exact_mod_cast hq
    dsimp only [s, lemma163StageIteration]
    field_simp [hqReal]
  rw [hiteration] at hUnion
  exact properMultiplyLinear_downward E.cover hUnion

end LeanProofs.GowersSzemeredi.BaseCase
