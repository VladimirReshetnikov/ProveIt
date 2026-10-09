import GowersSzemeredi.Proofs16MixedBohrDifferenceMap
import GowersSzemeredi.Proofs16BohrProgressionRetention

/-! Mixed configuration differences can be recentered into one proper
progression while preserving a common normalized Freiman map. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem mixed_configurations_common_progression_map {N : Nat} [NeZero N]
    (A B : Finset (ZMod N)) (f : Fin 4 → ZMod N → ZMod N)
    (Q : Finset (Fin 4 → ZMod N))
    (hQ : Q ⊆ mixedColumnQuadruples Finset.univ f)
    (hA : ∀ q ∈ Q, q 0 ∈ A) (hB : ∀ q ∈ Q, q 1 ∈ B)
    (hf : IsFreimanLinearOn A (f 0)) (hg : FreimanHom 8 B (f 1))
    {delta : Real} (hdelta : 0 < delta) (hcount : delta*(N : Real)^3 ≤ Q.card) :
    ∃ (Gamma : Finset (ZMod N)) (P : OAI.Erdos3.BohrProgression.CyclicCenteredGAP N)
      (psi : ZMod N → ZMod N) (a c : ZMod N) (R : Finset (Fin 4 → ZMod N)),
      (Gamma.card : Real) ≤ 16*delta^(-(2 : Real)) ∧
      P.rank ≤ commonDifferenceRank delta+1 ∧ P.Proper ∧
      P.carrier ⊆ bohr Gamma (commonDifferenceRadius delta/4) ∧
      commonDifferenceProgressionDensity delta*N ≤ (P.carrier.card : Real) ∧
      FreimanHom 2 (bohr Gamma (commonDifferenceRadius delta)) psi ∧ psi 0 = 0 ∧
      R ⊆ Q ∧ commonDifferenceProgressionRetention delta*(N : Real)^3 ≤ R.card ∧
      ∀ q ∈ R, q 0-q 1-a ∈ P.carrier ∧ f 0 (q 0)-f 1 (q 1) = c+psi (q 0-q 1-a) := by
  obtain ⟨Gamma,psi,a,c,R,hGamma,hpsi,hzero,hRQ,hR,hvalue⟩ :=
    mixed_configurations_common_bohr_map A B f Q hQ hA hB hf hg hdelta hcount
  have hG : Gamma.card ≤ commonDifferenceRank delta :=
    (Nat.cast_le (α := Real)).mp (hGamma.trans (Nat.le_ceil _))
  have hn : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  obtain ⟨P,t,R',hPrank,hPproper,hPsub,hPmass,hR'R,hR',_,hnew⟩ :=
    bohr_freiman_progression_retention R (fun q => q 0-q 1-a) Gamma psi
      (commonDifferenceRadius_pos hdelta) hG
      (mul_pos (commonDifferenceBohrDensity_pos hdelta) (pow_pos hn 3)) hR
      (fun q hq => (hvalue q hq).1) hpsi hzero
  refine ⟨Gamma,P,psi,a+t,c+psi t,R',hGamma,hPrank,hPproper,hPsub,hPmass,
    hpsi,hzero,hR'R.trans hRQ,?_,?_⟩
  · simpa only [commonDifferenceProgressionRetention,commonDifferenceProgressionDensity,mul_assoc] using hR'
  · intro q hq
    obtain ⟨hindex,hlinear⟩ := hnew q hq
    have hv := (hvalue q (hR'R hq)).2
    rw [show q 0-q 1-(a+t) = (q 0-q 1-a)-t by ring]
    refine ⟨hindex,?_⟩
    rw [hv,hlinear]
    ring

end LeanProofs.GowersSzemeredi
