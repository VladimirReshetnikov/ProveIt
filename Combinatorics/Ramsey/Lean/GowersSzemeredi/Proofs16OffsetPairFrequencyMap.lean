import GowersSzemeredi.Proofs16OffsetProgressionDifferenceMap
import GowersSzemeredi.Proofs16PairSelectionState

/-! Package the common offset-difference map with its translated proper
progression domain and the same controls used by pair-frequency selection. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem offset_equation_pair_frequency_map {N : Nat} [NeZero N] {I : Type*}
    [Fintype I] [DecidableEq I] (Q : Finset (I × ZMod N)) (a v : I → ZMod N)
    (A B : Finset (ZMod N)) (f g : ZMod N → ZMod N) (M : Nat)
    (hM : 0 < M) (ha : ∀ z, (Finset.univ.filter fun i => a i = z).card ≤ M)
    (hA : ∀ p ∈ Q, p.2+a p.1 ∈ A) (hB : ∀ p ∈ Q, p.2 ∈ B)
    (hval : ∀ p ∈ Q, f (p.2+a p.1)-g p.2 = v p.1)
    (hf : IsFreimanLinearOn A f) (hg : FreimanHom 8 B g)
    {delta : Real} (hd : 0 < delta) (hQ : delta*M*(N : Real)^2 ≤ Q.card) :
    ∃ (theta : PairFrequencyMap N) (R : Finset (I × ZMod N)),
      theta.Controlled (delta^2) ∧ R ⊆ Q ∧
      offsetDifferenceProgressionRetention delta*M*(N : Real)^2 ≤ R.card ∧
      ∀ p ∈ R, a p.1 ∈ theta.domain ∧ theta.toFun (a p.1) = f (p.2+a p.1)-g p.2 := by
  obtain ⟨Gamma,P,psi,b,c,R,_,hPrank,hPproper,hPsub,hPmass,hpsi,_,hRQ,hR,hvalue⟩ :=
    offset_equation_common_progression_map Q a v A B f g M hM ha hA hB hval hf hg hd hQ
  have hpsiP : FreimanHom 2 P.carrier psi := IsAddFreimanHom.subset
    (hPsub.trans (bohr_mono_radius Gamma (by
      have := commonDifferenceRadius_pos (pow_pos hd 2)
      linarith))) hpsi (Set.mapsTo_univ _ _)
  refine ⟨⟨P,b,fun x => c+psi (x-b)⟩,R,⟨hPrank,hPproper,hPmass,
    freiman_translate_graph P.carrier psi b c hpsiP⟩,hRQ,hR,?_⟩
  intro p hp
  exact ⟨(mem_translatedFreimanDomain P.carrier b _).mpr (hvalue p hp).1,(hvalue p hp).2.symm⟩

end LeanProofs.GowersSzemeredi
