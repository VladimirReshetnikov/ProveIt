import GowersSzemeredi.Proofs16MixedBohrDifferenceMap
import GowersSzemeredi.Proofs16EscapingFreimanFamily

/-! Actual containment failures yield one normalized Freiman map on a
controlled Bohr neighborhood, with escaping values on a dense retained family. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem failed_containments_common_bohr_map {N d : Nat} [NeZero N] [Fact N.Prime]
    (B : Finset (Fin 4 → ZMod N)) (T : ZMod N → Finset (ZMod N))
    (D : (Fin 4 → ZMod N) → Finset (ZMod N)) {r sigma delta : Real}
    (hr : 0 < r) (hr4 : r < 4) (hdelta : 0 < delta)
    (hB : delta*(N : Real)^3 ≤ B.card) (hadd : ∀ q ∈ B, q 0-q 1 = q 2-q 3)
    (hT : ∀ x, (T x).card ≤ d)
    (hs : ∀ q ∈ B, ((D q).card : Real)*sigma ≤ 1/(4*Real.pi))
    (hfail : ∀ q ∈ B, ¬ bohr (D q) sigma ⊆
      bohrQuarterSum (T (q 0) ∪ T (q 1)) (T (q 2) ∪ T (q 3)) r) :
    let epsilon := escapingFreimanDensity delta d r
    ∃ (f : Fin 4 → ZMod N → ZMod N) (Gamma : Finset (ZMod N))
      (psi : ZMod N → ZMod N) (a c : ZMod N) (Q : Finset (Fin 4 → ZMod N)),
      (∀ i x, f i x ∈ boundedFrequencySpan (fun b : T x => (b : ZMod N))
        (bohrExtensionCutoff (2*d) r)) ∧
      (Gamma.card : Real) ≤ 16*epsilon^(-(2 : Real)) ∧
      FreimanHom 2 (bohr Gamma (commonDifferenceRadius epsilon)) psi ∧ psi 0 = 0 ∧
      Q ⊆ B ∧ commonDifferenceBohrDensity epsilon*(N : Real)^3 ≤ Q.card ∧
      ∀ q ∈ Q, q 0-q 1-a ∈ bohr Gamma (commonDifferenceRadius epsilon/2) ∧
        c+psi (q 0-q 1-a) = f 0 (q 0)-f 1 (q 1) ∧
        c+psi (q 0-q 1-a) = f 2 (q 2)-f 3 (q 3) ∧
        c+psi (q 0-q 1-a) ∉ boundedFrequencySpan (fun b : D q => (b : ZMod N)) 1 := by
  obtain ⟨f,E,R,hf,hRB,hE,_,hconfig,hR⟩ :=
    failed_containments_freiman_family B T D hr hr4 hdelta hB hadd hT hs hfail
  have hRsub : R ⊆ mixedColumnQuadruples Finset.univ f := by
    intro q hq
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,Finset.mem_univ _,
      hadd q (hRB hq),(hconfig q hq).2.1⟩
  have hf0 : IsFreimanLinearOn (E 0) (f 0) := (hE 0).2.isFreimanLinearOn (by decide)
  obtain ⟨Gamma,psi,a,c,Q,hGamma,hpsi,hzero,hQR,hQ,hvalue⟩ :=
    mixed_configurations_common_bohr_map (E 0) (E 1) f R hRsub
      (fun q hq => (hconfig q hq).1 0) (fun q hq => (hconfig q hq).1 1)
      hf0 (hE 1).2 (escapingFreimanDensity_pos hdelta d r) hR
  refine ⟨f,Gamma,psi,a,c,Q,hf,hGamma,hpsi,hzero,hQR.trans hRB,hQ,?_⟩
  intro q hq
  obtain ⟨hindex,hval⟩ := hvalue q hq
  obtain ⟨_,heq,hescape⟩ := hconfig q (hQR hq)
  exact ⟨hindex,hval.symm,hval.symm.trans heq,hval ▸ hescape⟩

end LeanProofs.GowersSzemeredi
