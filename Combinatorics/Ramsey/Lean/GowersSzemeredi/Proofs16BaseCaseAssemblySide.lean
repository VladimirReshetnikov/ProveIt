import GowersSzemeredi.Proofs16BaseCaseAssembly
import GowersSzemeredi.Proofs16BaseCaseSingleGraph

/-! Declarations of `Proofs16BaseCaseAssembly` that the final route does not use and that
need modules outside it (moved here so that those modules can leave the route). -/

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi.BaseCase

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
  · have _ : (0 : Real) ≤ P.carrier.card := by positivity
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
  · intro j x _ _ y hxy
    simp at hxy

/-- Repaired one-dimensional theorem, conditional only on finite-union
closure. -/
theorem proper_lemma_16_3_of_unionClosure
    (hunion : ProperUnionClosure) : ProperTheorem162At 1 := by
  intro gamma theta hgamma hgammaOne htheta hthetaOne
  refine ⟨0, ?_⟩
  intro N _ hprime _ Gamma hGamma hrelation
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
