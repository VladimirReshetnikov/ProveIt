import GowersSzemeredi.Proofs16BoundedSpanAlgebra
import Mathlib.Combinatorics.Additive.Dissociation

/-! Count distinct subset sums of a dissociated set inside a bounded
frequency span. All subset sums lie in one enlarged coefficient box. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem add_mem_boundedFrequencySpan {N : Nat} [NeZero N]
    (K : Finset (ZMod N)) (R S : Nat) {x y : ZMod N}
    (hx : x ∈ boundedFrequencySpan (fun k : K => (k : ZMod N)) R)
    (hy : y ∈ boundedFrequencySpan (fun k : K => (k : ZMod N)) S) :
    x + y ∈ boundedFrequencySpan (fun k : K => (k : ZMod N)) (R + S) := by
  obtain ⟨f, hf, rfl⟩ := (mem_boundedFrequencySpan_iff K R x).mp hx
  obtain ⟨g, hg, rfl⟩ := (mem_boundedFrequencySpan_iff K S y).mp hy
  apply (mem_boundedFrequencySpan_iff K (R + S) _).mpr
  refine ⟨fun k => f k + g k, fun k hk => ?_, ?_⟩
  · exact (centeredAbs_add_le _ _).trans (Nat.add_le_add (hf k hk) (hg k hk))
  · simp only [add_mul, Finset.sum_add_distrib]

theorem sum_mem_boundedFrequencySpan {N : Nat} [NeZero N]
    {ι : Type*} (K : Finset (ZMod N)) (R : Nat) (s : Finset ι) (f : ι → ZMod N)
    (hf : ∀ i ∈ s, f i ∈ boundedFrequencySpan (fun k : K => (k : ZMod N)) R) :
    (∑ i ∈ s, f i) ∈ boundedFrequencySpan (fun k : K => (k : ZMod N)) (s.card * R) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero_mem_boundedFrequencySpan (fun k : K => (k : ZMod N)) 0
  | @insert i s hi ih =>
    have hsum := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    have hadd := add_mem_boundedFrequencySpan K R (s.card * R) (hf i (Finset.mem_insert_self _ _)) hsum
    simpa only [Finset.sum_insert hi, Finset.card_insert_of_notMem hi, Nat.add_mul,
      Nat.one_mul, Nat.add_comm] using hadd

/-- Dissociation makes all 2^|D| subset sums distinct. A coefficient-box
count bounds their number uniformly in the ambient modulus. -/
theorem dissociated_boundedSpan_count {N : Nat} [NeZero N]
    (K D : Finset (ZMod N)) (R : Nat)
    (hD : D ⊆ boundedFrequencySpan (fun k : K => (k : ZMod N)) R)
    (hdiss : AddDissociated (D : Set (ZMod N))) :
    2 ^ D.card ≤ (2 * (D.card * R) + 1) ^ K.card := by
  have hinj : Set.InjOn (fun s : Finset (ZMod N) => ∑ x ∈ s, x) (D.powerset : Set (Finset (ZMod N))) := by
    intro s hs t ht heq
    exact hdiss (fun x hx => (Finset.mem_powerset.mp hs) hx)
      (fun x hx => (Finset.mem_powerset.mp ht) hx) heq
  have hsub : (D.powerset.image fun s => ∑ x ∈ s, x) ⊆
      boundedFrequencySpan (fun k : K => (k : ZMod N)) (D.card * R) := by
    intro x hx
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hx
    have hsD := Finset.mem_powerset.mp hs
    exact boundedFrequencySpan_mono _ (Nat.mul_le_mul_right R (Finset.card_le_card hsD))
      (sum_mem_boundedFrequencySpan K R s id (fun i hi => hD (hsD hi)))
  calc 2 ^ D.card = D.powerset.card := (Finset.card_powerset D).symm
    _ = (D.powerset.image fun s => ∑ x ∈ s, x).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (boundedFrequencySpan (fun k : K => (k : ZMod N)) (D.card * R)).card := Finset.card_le_card hsub
    _ ≤ (2 * (D.card * R) + 1) ^ K.card := by simpa using boundedFrequencySpan_card_le (fun k : K => (k : ZMod N)) (D.card * R)

end LeanProofs.GowersSzemeredi
