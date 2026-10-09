import GowersSzemeredi.Proofs16CommonDifferenceRetention
import GowersSzemeredi.Proofs16EscapingFreimanFamily

/-! Failed Bohr containments yield a single Freiman map on translated
column differences, retaining the original escaping-frequency witnesses. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem failed_containments_common_difference_map {N d : Nat} [NeZero N] [Fact N.Prime]
    (B : Finset (Fin 4 → ZMod N)) (T : ZMod N → Finset (ZMod N))
    (D : (Fin 4 → ZMod N) → Finset (ZMod N)) {r sigma delta : Real}
    (hr : 0 < r) (hr4 : r < 4) (hdelta : 0 < delta)
    (hB : delta*(N : Real)^3 ≤ B.card) (hadd : ∀ q ∈ B, q 0-q 1 = q 2-q 3)
    (hT : ∀ x, (T x).card ≤ d)
    (hs : ∀ q ∈ B, ((D q).card : Real)*sigma ≤ 1/(4*Real.pi))
    (hfail : ∀ q ∈ B, ¬ bohr (D q) sigma ⊆
      bohrQuarterSum (T (q 0) ∪ T (q 1)) (T (q 2) ∪ T (q 3)) r) :
    ∃ (f : Fin 4 → ZMod N → ZMod N) (S : Finset (ZMod N))
      (theta : ZMod N → ZMod N) (a c : ZMod N) (Q : Finset (Fin 4 → ZMod N)),
      (∀ i x, f i x ∈ boundedFrequencySpan (fun b : T x => (b : ZMod N))
        (bohrExtensionCutoff (2*d) r)) ∧
      S ⊆ B.image (fun q => q 1) ∧ FreimanHom 8 S (f 1) ∧
      escapingFreimanDensity delta d r*N ≤ (S.card : Real) ∧
      IsFreimanLinearOn (fourfoldGraphDomain S) theta ∧ Q ⊆ B ∧
      (escapingFreimanDensity delta d r)^3*(N : Real)^3 ≤ Q.card ∧
      (∀ p : Fin 4 → ZMod N, (∀ i, p i ∈ S) →
        theta (fourfoldGraphIndex p) = fourfoldGraphIndex (f 1 ∘ p)) ∧
      ∀ q ∈ Q, q 0-q 1-a ∈ fourfoldGraphDomain S ∧
        c+theta (q 0-q 1-a) = f 0 (q 0)-f 1 (q 1) ∧
        c+theta (q 0-q 1-a) = f 2 (q 2)-f 3 (q 3) ∧
        c+theta (q 0-q 1-a) ∉ boundedFrequencySpan (fun b : D q => (b : ZMod N)) 1 := by
  obtain ⟨f,E,R,hf,hRB,hE,_,hconfig,hR⟩ :=
    failed_containments_freiman_family B T D hr hr4 hdelta hB hadd hT hs hfail
  have hRsub : R ⊆ mixedColumnQuadruples Finset.univ f := by
    intro q hq
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,Finset.mem_univ _,
      hadd q (hRB hq),(hconfig q hq).2.1⟩
  have hf0 : IsFreimanLinearOn (E 0) (f 0) := fun _ _ _ _ hx hy hz hw he =>
    (IsAddFreimanHom.mono (by decide : 2 ≤ 8) (hE 0).2).add_eq_add hx hy hz hw he
  obtain ⟨S,hSE,hS,theta,a,c,Q,htheta,hQR,hQ,hrepr,hvalue⟩ :=
    mixed_configurations_common_difference_map (E 0) (E 1) f R hRsub
      (fun q hq => (hconfig q hq).1 0) (fun q hq => (hconfig q hq).1 1)
      hf0 (hE 1).2 (escapingFreimanDensity_pos hdelta d r) hR
  refine ⟨f,S,theta,a,c,Q,hf,hSE.trans (hE 1).1,
    IsAddFreimanHom.subset hSE (hE 1).2 (Set.mapsTo_univ _ _),
    hS,htheta,hQR.trans hRB,hQ,hrepr,?_⟩
  intro q hq
  obtain ⟨hindex,hval⟩ := hvalue q hq
  obtain ⟨_,heq,hescape⟩ := hconfig q (hQR hq)
  exact ⟨hindex,hval.symm,hval.symm.trans heq,hval ▸ hescape⟩

end LeanProofs.GowersSzemeredi
