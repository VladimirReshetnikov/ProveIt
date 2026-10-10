import GowersSzemeredi.Proofs16EightExtensionMassBudget
import GowersSzemeredi.Proofs16SourceAgreementVertices

/-! Reserve enough missing-vertex mass for both quadruple purification and
removing vertices without original source alternatives. The extra accuracy
still has a constant-to-the-rank denominator and a cubic density factor. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem joint_source_core_loss_budget {N : Nat} [NeZero N]
    (Q : CenteredProgression N) (hQ : Q.Proper) {delta eta : Real}
    (hdelta : 0 < delta) (hmass : delta*N ≤ (Q.carrier.card : Real))
    (heta : eta ≤ delta^3/(4096*(4194304 : Real)^Q.rank)) :
    2*(eta*(N : Real)^3/((progressionGoodPairThreshold Q : Real)+1))/
      ((progressionPurificationVertexThreshold Q : Real)+1) + eta*(4096 : Real)^Q.rank/delta^2*N ≤
        delta*N/(16*(1024 : Real)^Q.rank) := by
  have hn : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hpow : (65536 : Real)^Q.rank ≤ (4194304 : Real)^Q.rank :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have hfour : 4*eta ≤ delta^3/(1024*(65536 : Real)^Q.rank) := by
    have h := mul_le_mul_of_nonneg_left heta (by norm_num : (0 : Real) ≤ 4)
    have heq : 4*(delta^3/(4096*(4194304 : Real)^Q.rank)) = delta^3/(1024*(4194304 : Real)^Q.rank) := by ring
    rw [heq] at h
    exact h.trans (div_le_div_of_nonneg_left (by positivity) (by positivity)
      (mul_le_mul_of_nonneg_left hpow (by norm_num)))
  have hquad := progression_eight_extension_loss_budget Q hQ hdelta hmass hfour
  have hquadbound : 2*(eta*(N : Real)^3/((progressionGoodPairThreshold Q : Real)+1))/
      ((progressionPurificationVertexThreshold Q : Real)+1) ≤ delta*N/(64*(1024 : Real)^Q.rank) := by
    have heq : 2*((4*eta)*(N : Real)^3/((progressionGoodPairThreshold Q : Real)+1))/
        ((progressionPurificationVertexThreshold Q : Real)+1) =
      4*(2*(eta*(N : Real)^3/((progressionGoodPairThreshold Q : Real)+1))/
        ((progressionPurificationVertexThreshold Q : Real)+1)) := by ring
    have hr : delta*N/(16*(1024 : Real)^Q.rank) = 4*(delta*N/(64*(1024 : Real)^Q.rank)) := by ring
    rw [heq,hr] at hquad
    linarith
  have hvertex : eta*(4096 : Real)^Q.rank/delta^2*N ≤ delta*N/(4096*(1024 : Real)^Q.rank) := by
    have hfactor : 0 ≤ (4096 : Real)^Q.rank/delta^2*N := by positivity
    have h := mul_le_mul_of_nonneg_right heta hfactor
    have heq : (delta^3/(4096*(4194304 : Real)^Q.rank))*((4096 : Real)^Q.rank/delta^2*N) =
        delta*N/(4096*(1024 : Real)^Q.rank) := by
      have hp : (4194304 : Real)^Q.rank = (4096 : Real)^Q.rank*(1024 : Real)^Q.rank := by
        rw [←mul_pow]
        norm_num
      rw [hp]
      field_simp <;> ring
    rw [heq] at h
    convert h using 1 <;> first | rfl | ring
  have hpos : 0 < delta*N/(1024 : Real)^Q.rank := by positivity
  have h64 : delta*N/(64*(1024 : Real)^Q.rank) = (delta*N/(1024 : Real)^Q.rank)/64 := by ring
  have h4096 : delta*N/(4096*(1024 : Real)^Q.rank) = (delta*N/(1024 : Real)^Q.rank)/4096 := by ring
  have h16 : delta*N/(16*(1024 : Real)^Q.rank) = (delta*N/(1024 : Real)^Q.rank)/16 := by ring
  rw [h64] at hquadbound
  rw [h4096] at hvertex
  rw [h16]
  linarith

end LeanProofs.GowersSzemeredi
