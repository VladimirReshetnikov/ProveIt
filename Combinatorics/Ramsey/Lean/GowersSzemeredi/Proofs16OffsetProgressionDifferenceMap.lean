import GowersSzemeredi.Proofs16OffsetBohrDifferenceMap
import GowersSzemeredi.Proofs16BohrProgressionRetention

/-! The common map for an indexed offset equation localizes to a proper
progression, retaining its additive constant and original configurations. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def offsetDifferenceProgressionRetention (delta : Real) : Real :=
  commonDifferenceProgressionDensity (delta^2)*offsetDifferenceBohrDensity delta

theorem offsetDifferenceProgressionRetention_pos {delta : Real} (hd : 0 < delta) :
    0 < offsetDifferenceProgressionRetention delta :=
  mul_pos (commonDifferenceProgressionDensity_pos (delta^2)) (offsetDifferenceBohrDensity_pos hd)

theorem offset_equation_common_progression_map {N : Nat} [NeZero N] {I : Type*}
    [Fintype I] [DecidableEq I] (Q : Finset (I × ZMod N)) (a v : I → ZMod N)
    (A B : Finset (ZMod N)) (f g : ZMod N → ZMod N) (M : Nat)
    (hM : 0 < M) (ha : ∀ z, (Finset.univ.filter fun i => a i = z).card ≤ M)
    (hA : ∀ p ∈ Q, p.2+a p.1 ∈ A) (hB : ∀ p ∈ Q, p.2 ∈ B)
    (hval : ∀ p ∈ Q, f (p.2+a p.1)-g p.2 = v p.1)
    (hf : IsFreimanLinearOn A f) (hg : FreimanHom 8 B g)
    {delta : Real} (hd : 0 < delta) (hQ : delta*M*(N : Real)^2 ≤ Q.card) :
    ∃ (Gamma : Finset (ZMod N)) (P : OAI.Erdos3.BohrProgression.CyclicCenteredGAP N)
      (psi : ZMod N → ZMod N) (b c : ZMod N) (R : Finset (I × ZMod N)),
      (Gamma.card : Real) ≤ 16*(delta^2)^(-(2 : Real)) ∧
      P.rank ≤ commonDifferenceRank (delta^2)+1 ∧ P.Proper ∧
      P.carrier ⊆ bohr Gamma (commonDifferenceRadius (delta^2)/4) ∧
      commonDifferenceProgressionDensity (delta^2)*N ≤ (P.carrier.card : Real) ∧
      FreimanHom 2 (bohr Gamma (commonDifferenceRadius (delta^2))) psi ∧ psi 0 = 0 ∧
      R ⊆ Q ∧ offsetDifferenceProgressionRetention delta*M*(N : Real)^2 ≤ R.card ∧
      ∀ p ∈ R, a p.1-b ∈ P.carrier ∧ f (p.2+a p.1)-g p.2 = c+psi (a p.1-b) := by
  obtain ⟨Gamma,psi,b,c,R,hGamma,hpsi,hzero,hRQ,hR,hvalue⟩ :=
    offset_equation_common_bohr_map Q a v A B f g M hM ha hA hB hval hf hg hd hQ
  have hG : Gamma.card ≤ commonDifferenceRank (delta^2) :=
    (Nat.cast_le (α := Real)).mp (hGamma.trans (Nat.le_ceil _))
  have hn : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hm : (0 : Real) < M := by exact_mod_cast hM
  have hmass : 0 < offsetDifferenceBohrDensity delta*M*(N : Real)^2 := by
    have := offsetDifferenceBohrDensity_pos hd
    positivity
  obtain ⟨P,t,R',hPrank,hPproper,hPsub,hPmass,hR'R,hR',_,hnew⟩ :=
    bohr_freiman_progression_retention R (fun p => a p.1-b) Gamma psi
      (commonDifferenceRadius_pos (pow_pos hd 2)) hG hmass hR
      (fun p hp => (hvalue p hp).1) hpsi hzero
  refine ⟨Gamma,P,psi,b+t,c+psi t,R',hGamma,hPrank,hPproper,hPsub,hPmass,
    hpsi,hzero,hR'R.trans hRQ,?_,?_⟩
  · simpa only [offsetDifferenceProgressionRetention,commonDifferenceProgressionDensity,mul_assoc] using hR'
  · intro p hp
    obtain ⟨hindex,hlinear⟩ := hnew p hp
    have hv := (hvalue p (hR'R hp)).2
    rw [show a p.1-(b+t) = (a p.1-b)-t by ring]
    refine ⟨hindex,?_⟩
    rw [hv,hlinear]
    ring

end LeanProofs.GowersSzemeredi
