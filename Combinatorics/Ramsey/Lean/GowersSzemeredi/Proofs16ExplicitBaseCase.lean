import GowersSzemeredi.Proofs16BaseCaseEndpoint
import GowersSzemeredi.Proofs16ExplicitFaces

/-! Lemma 16.3 (Theorem 16.2 in dimension one) holds at every modulus.

The proof of `BaseCase.proper_lemma_16_3_of_unionClosure` uses the
threshold `0`. It is repeated here as `Theorem162AtBounded 1 (fun _ _ => 0)`,
so consumers see that the one-dimensional input imposes no modulus
threshold. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open BaseCase

/-- Theorem 16.2 in dimension one, for every prime modulus. -/
theorem lemma_16_3_bounded : Theorem162AtBounded 1 (fun _ _ => 0) := by
  intro gamma theta hgamma hgammaOne htheta hthetaOne
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
  have hUnion := properUnionClosure_holds N 1 E.q gamma s G hqPos hs hG
  have hiteration : (E.q : Real) * s = lemma163Iteration gamma theta := by
    have hqReal : (E.q : Real) ≠ 0 := by exact_mod_cast hq
    dsimp only [s, lemma163StageIteration]
    field_simp [hqReal]
  rw [hiteration] at hUnion
  exact properMultiplyLinear_downward E.cover hUnion

end LeanProofs.GowersSzemeredi
