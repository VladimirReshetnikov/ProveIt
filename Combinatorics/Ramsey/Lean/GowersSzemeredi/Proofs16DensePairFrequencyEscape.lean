import GowersSzemeredi.Proofs16TranslatedFreimanGraph
import GowersSzemeredi.Proofs16PairProjectionDensity
import GowersSzemeredi.Proofs16SpanGeneratorInclusion

/-! A dense family of failed containments gives one Freiman map on a
translated proper progression that escapes the selected spans on many pairs. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem failed_containments_dense_pair_escape {N d : Nat} [NeZero N] [Fact N.Prime]
    (B : Finset (Fin 4 → ZMod N)) (T : ZMod N → Finset (ZMod N))
    (D : (Fin 4 → ZMod N) → Finset (ZMod N))
    (F : (ZMod N × ZMod N) → Finset (ZMod N)) {r sigma delta : Real}
    (hr : 0 < r) (hr4 : r < 4) (hdelta : 0 < delta)
    (hB : delta*(N : Real)^3 ≤ B.card) (hadd : ∀ q ∈ B, q 0-q 1 = q 2-q 3)
    (hT : ∀ x, (T x).card ≤ d)
    (hs : ∀ q ∈ B, ((D q).card : Real)*sigma ≤ 1/(4*Real.pi))
    (hFD : ∀ q ∈ B, F (q 0,q 1) ⊆ D q)
    (hfail : ∀ q ∈ B, ¬ bohr (D q) sigma ⊆
      bohrQuarterSum (T (q 0) ∪ T (q 1)) (T (q 2) ∪ T (q 3)) r) :
    let epsilon := escapingFreimanDensity delta d r
    ∃ (P : OAI.Erdos3.BohrProgression.CyclicCenteredGAP N) (a : ZMod N)
      (theta : ZMod N → ZMod N) (E : Finset (ZMod N × ZMod N)),
      P.rank ≤ commonDifferenceRank epsilon+1 ∧ P.Proper ∧
      commonDifferenceProgressionDensity epsilon*N ≤ (P.carrier.card : Real) ∧
      FreimanHom 2 (translatedFreimanDomain P.carrier a) theta ∧
      E ⊆ B.image (fun q => (q 0,q 1)) ∧
      commonDifferenceProgressionRetention epsilon*(N : Real)^2 ≤ E.card ∧
      ∀ p ∈ E, p.1-p.2 ∈ translatedFreimanDomain P.carrier a ∧
        theta (p.1-p.2) ∈ boundedFrequencySpan (fun b : ↥(T p.1 ∪ T p.2) => (b : ZMod N))
          (2*bohrExtensionCutoff (2*d) r) ∧
        theta (p.1-p.2) ∉ boundedFrequencySpan (fun b : F p => (b : ZMod N)) 1 := by
  obtain ⟨f,Gamma,P,psi,a,c,Q,hf,_,hPrank,hPproper,hPsub,hPmass,hpsi,_,hQB,hQ,hvalue⟩ :=
    failed_containments_common_progression_map B T D hr hr4 hdelta hB hadd hT hs hfail
  let E := Q.image fun q => (q 0,q 1)
  have hpsiP : FreimanHom 2 P.carrier psi := IsAddFreimanHom.subset
    (hPsub.trans (bohr_mono_radius Gamma (by
      have := commonDifferenceRadius_pos (escapingFreimanDensity_pos hdelta d r)
      linarith))) hpsi (Set.mapsTo_univ _ _)
  refine ⟨P,a,fun x => c+psi (x-a),E,hPrank,hPproper,hPmass,
    freiman_translate_graph P.carrier psi a c hpsiP,Finset.image_subset_image hQB,?_,?_⟩
  · exact additive_quadruples_pair_density Q E (fun q hq => hadd q (hQB hq))
      (fun q hq => Finset.mem_image.mpr ⟨q,hq,rfl⟩) hQ
  · intro p hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hindex,hval,_,hescape⟩ := hvalue q hq
    refine ⟨(mem_translatedFreimanDomain P.carrier a _).mpr hindex,?_,?_⟩
    · dsimp only
      rw [hval]
      have h := sub_mem_union_boundedFrequencySpan (T (q 0)) (T (q 1)) _ _ (hf 0 (q 0)) (hf 1 (q 1))
      simpa only [two_mul] using h
    · intro he
      exact hescape (boundedFrequencySpan_mono_generators _ _ 1 (hFD q (hQB hq)) he)

end LeanProofs.GowersSzemeredi
