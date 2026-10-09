import GowersSzemeredi.Proofs16HigherFrequencyEscape
import GowersSzemeredi.Proofs16IndexedSelection

/-! Choose sixteen frequency maps which realize many failed Bohr containments.
The choices are independent across colors, even at repeated column indices. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- Every indexed failed containment prescribes an escaping frequency
arrangement. Sixteen maps realize at least a `(2R+1)^(-16d)` fraction of them. -/
theorem exists_higher_escaping_frequency_selection {N d : Nat} [NeZero N] [Fact N.Prime]
    {I : Type*} (B : Finset I) (pos : I → Fin 16 → ZMod N)
    (T : ZMod N → Finset (ZMod N)) (D : I → Finset (ZMod N)) (L : Nat)
    {r sigma : Real} (hr : 0 < r) (hr4 : r < 4)
    (hT : ∀ x, (T x).card ≤ d)
    (hs : ∀ t ∈ B, ((D t).card : Real)*L*sigma ≤ 1/(4*Real.pi))
    (hfail : ∀ t ∈ B, ¬ bohr (D t) sigma ⊆
      bohrQuarterSum (higherLeftFrequencies T (pos t)) (higherRightFrequencies T (pos t)) r) :
    let R := bohrExtensionCutoff (8*d) r
    ∃ f : Fin 16 → ZMod N → ZMod N,
      (∀ i x, f i x ∈ boundedFrequencySpan (fun a : T x => (a : ZMod N)) R) ∧
      B.card ≤ (2*R+1)^(16*d) *
        (B.filter fun t => HigherFrequencyEquation (fun i => f i (pos t i)) ∧
          higherLeftFrequencyValue (fun i => f i (pos t i)) ∉ boundedFrequencySpan (fun a : D t => (a : ZMod N)) L).card := by
  let R := bohrExtensionCutoff (8*d) r
  let U (x : ZMod N) := boundedFrequencySpan (fun a : T x => (a : ZMod N)) R
  have hex : ∀ t ∈ B, ∃ v : Fin 16 → ZMod N,
      (∀ i, v i ∈ U (pos t i)) ∧ HigherFrequencyEquation v ∧
      higherLeftFrequencyValue v ∉ boundedFrequencySpan (fun a : D t => (a : ZMod N)) L := by
    intro t ht
    exact higher_column_frequency_escape T (D t) (pos t) L hr hr4 (fun i => hT (pos t i)) (hs t ht) (hfail t ht)
  let val (t : I) : Fin 16 → ZMod N := if ht : t ∈ B then Classical.choose (hex t ht) else 0
  have hval (t : I) (ht : t ∈ B) :
      (∀ i, val t i ∈ U (pos t i)) ∧ HigherFrequencyEquation (val t) ∧
      higherLeftFrequencyValue (val t) ∉ boundedFrequencySpan (fun a : D t => (a : ZMod N)) L := by
    simpa only [val,dif_pos ht] using Classical.choose_spec (hex t ht)
  have hU : ∀ x, (U x).card ≤ (2*R+1)^d := by
    intro x
    exact (boundedFrequencySpan_card_le (fun a : T x => (a : ZMod N)) R).trans
      (Nat.pow_le_pow_right (by omega) (by simpa only [Fintype.card_coe] using hT x))
  obtain ⟨f,hf,hcount⟩ := exists_good_colored_selection (K := (2*R+1)^d) U
    (fun x => ⟨0,zero_mem_boundedFrequencySpan _ _⟩) (by have h := pow_pos (by omega : 0 < 2*R+1) d; omega) hU B pos val
    (fun t ht => (hval t ht).1)
  refine ⟨f,hf,?_⟩
  have hsub : (B.filter fun t => ∀ i, f i (pos t i) = val t i) ⊆
      B.filter fun t => HigherFrequencyEquation (fun i => f i (pos t i)) ∧
        higherLeftFrequencyValue (fun i => f i (pos t i)) ∉ boundedFrequencySpan (fun a : D t => (a : ZMod N)) L := by
    intro t ht
    obtain ⟨htB,he⟩ := Finset.mem_filter.mp ht
    exact Finset.mem_filter.mpr ⟨htB,by simpa only [he] using (hval t htB).2⟩
  have hcount' : B.card ≤ ((2*R+1)^d)^16 *
      (B.filter fun t => ∀ i, f i (pos t i) = val t i).card := by
    convert hcount using 1
    congr 2
    ext t
    simp
  have h := hcount'.trans (Nat.mul_le_mul_left _ (Finset.card_le_card hsub))
  simpa only [← pow_mul,Nat.mul_comm d 16] using h

end LeanProofs.GowersSzemeredi
