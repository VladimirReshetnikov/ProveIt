import GowersSzemeredi.Proofs16MixedFreimanFamily
import GowersSzemeredi.Proofs16EscapingFrequencySelection

/-! Actual failed Bohr containments yield four Freiman frequency pieces
and a dense family still witnessing equal escaping frequency differences. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def escapingFreimanDensity (delta : Real) (d : Nat) (r : Real) : Real :=
  mixedConfigurationDensity (delta/(2*bohrExtensionCutoff (2*d) r+1 : Nat)^(4*d)) 4

theorem escapingFreimanDensity_pos {delta : Real} (hdelta : 0 < delta) (d : Nat) (r : Real) :
    0 < escapingFreimanDensity delta d r := by
  apply mixedConfigurationDensity_pos
  exact div_pos hdelta (by positivity)

/-- The selected maps become order-eight Freiman maps on coordinate
sets while retaining configurations with frequency differences outside
the prescribed unit spans. -/
theorem failed_containments_freiman_family {N d : Nat} [NeZero N] [Fact N.Prime]
    (B : Finset (Fin 4 → ZMod N)) (T : ZMod N → Finset (ZMod N))
    (D : (Fin 4 → ZMod N) → Finset (ZMod N)) {r sigma delta : Real}
    (hr : 0 < r) (hr4 : r < 4) (hdelta : 0 < delta)
    (hB : delta*(N : Real)^3 ≤ B.card) (hadd : ∀ q ∈ B, q 0-q 1 = q 2-q 3)
    (hT : ∀ x, (T x).card ≤ d)
    (hs : ∀ q ∈ B, ((D q).card : Real)*sigma ≤ 1/(4*Real.pi))
    (hfail : ∀ q ∈ B, ¬ bohr (D q) sigma ⊆
      bohrQuarterSum (T (q 0) ∪ T (q 1)) (T (q 2) ∪ T (q 3)) r) :
    let R := bohrExtensionCutoff (2*d) r
    ∃ (f : Fin 4 → ZMod N → ZMod N) (E : Fin 4 → Finset (ZMod N))
      (Q : Finset (Fin 4 → ZMod N)),
      (∀ i x, f i x ∈ boundedFrequencySpan (fun a : T x => (a : ZMod N)) R) ∧
      Q ⊆ B ∧ (∀ i, E i ⊆ B.image (fun q => q i) ∧ FreimanHom 8 (E i) (f i)) ∧
      (∀ i, escapingFreimanDensity delta d r*N ≤ ((E i).card : Real)) ∧
      (∀ q ∈ Q, (∀ i, q i ∈ E i) ∧
        f 0 (q 0)-f 1 (q 1) = f 2 (q 2)-f 3 (q 3) ∧
        f 0 (q 0)-f 1 (q 1) ∉ boundedFrequencySpan (fun a : D q => (a : ZMod N)) 1) ∧
      escapingFreimanDensity delta d r*(N : Real)^3 ≤ Q.card := by
  let R := bohrExtensionCutoff (2*d) r
  let K := (2*R+1)^(4*d)
  obtain ⟨f,hf,hcount⟩ := exists_escaping_frequency_selection B id T D hr hr4 hT hs hfail
  let C := B.filter fun q => f 0 (q 0)-f 1 (q 1) = f 2 (q 2)-f 3 (q 3) ∧
    f 0 (q 0)-f 1 (q 1) ∉ boundedFrequencySpan (fun a : D q => (a : ZMod N)) 1
  have hcount' : B.card ≤ K*C.card := by
    convert hcount using 1
    dsimp [K,R,C]
    congr 2
  have hK : (0 : Real) < K := by dsimp [K]; positivity
  have hC : (delta/K)*(N : Real)^3 ≤ C.card := by
    have hRcount : (B.card : Real) ≤ (K : Real)*C.card := by exact_mod_cast hcount'
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hK).mpr
    simpa only [mul_comm (K : Real)] using hB.trans hRcount
  have hCsub : C ⊆ mixedColumnQuadruples Finset.univ f := by
    intro q hq
    obtain ⟨hqB,hval,_⟩ := Finset.mem_filter.mp hq
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,Finset.mem_univ _,hadd q hqB,hval⟩
  obtain ⟨E,Q,hQC,hE,hsize,hcoord,hQ⟩ := mixed_configurations_freiman_family f C hCsub (div_pos hdelta hK) hC
  have hsize' : ∀ i, escapingFreimanDensity delta d r*N ≤ ((E i).card : Real) := by
    simpa only [escapingFreimanDensity,K,R,Nat.cast_pow] using hsize
  have hQ' : escapingFreimanDensity delta d r*(N : Real)^3 ≤ Q.card := by
    simpa only [escapingFreimanDensity,K,R,Nat.cast_pow] using hQ
  refine ⟨f,E,Q,hf,hQC.trans (Finset.filter_subset _ _),?_,hsize',?_,hQ'⟩
  · intro i
    exact ⟨(hE i).1.trans (Finset.image_subset_image (Finset.filter_subset _ _)),(hE i).2⟩
  · intro q hq
    exact ⟨hcoord q hq,(Finset.mem_filter.mp (hQC hq)).2⟩

end LeanProofs.GowersSzemeredi
