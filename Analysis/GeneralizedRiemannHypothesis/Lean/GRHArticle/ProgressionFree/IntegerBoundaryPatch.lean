import GRHArticle.ProgressionFree.IntegerBoundaryExchangeTail
import GRHArticle.ProgressionFree.IntegerNaturalDensityApproximation
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# Extending a 5-smooth exchange to larger smooth sets

Keep the old set outside the 5-smooth numbers, insert the new template, and
delete the last term of every integral progression that could cross the
boundary from a newly inserted first term.
-/

namespace GRHArticle.ProgressionFree

open scoped Classical BigOperators

private abbrev S := Nat.smoothNumbers 6
private noncomputable abbrev W := integerExchangeReciprocalWeight

/-- The possible last terms charged to the newly inserted first terms. -/
def integerBoundaryEndpoints (D : Set ℕ) : Set ℕ :=
  {n | ∃ b ∈ D, ∃ r ∉ Nat.smoothNumbers 6, n = b*r*r}

/-- Replace the small smooth part of the template and remove the charged endpoints. -/
def integerBoundaryPatch (E B : Set ℕ) : Set ℕ :=
  (B ∪ (E \ Nat.smoothNumbers 6)) \ integerBoundaryEndpoints (B \ E)

private theorem patch_subset {E B : Set ℕ} {Y : ℕ} (hY : 5 ≤ Y)
    (hE : E ⊆ Nat.smoothNumbers (Y+1)) (hB : B ⊆ S) :
    integerBoundaryPatch E B ⊆ Nat.smoothNumbers (Y+1) :=
  fun _ h ↦ h.1.elim (fun hb ↦ Nat.smoothNumbers_mono (by omega : 6 ≤ Y+1) (hB hb))
    (fun he ↦ hE he.1)

/-- The corrected template is admissible for integral ratios at every prime cutoff. -/
theorem integerBoundaryPatch_admissible {E B : Set ℕ} {Y : ℕ} (hY : 5 ≤ Y)
    (hE : E ⊆ Nat.smoothNumbers (Y+1)) (hB : B ⊆ Nat.smoothNumbers 6)
    (he : IntegerPrefixAdmissible false E) (hb : IntegerPrefixAdmissible true B) :
    IntegerPrefixAdmissible true (integerBoundaryPatch E B) := by
  have hpos : ∀ a ∈ integerBoundaryPatch E B, 0 < a :=
    fun _ h ↦ Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_smoothNumbers (patch_subset hY hE hB h))
  apply (integerPrefixAdmissible_integral_iff hpos).mpr
  intro a r hr ha hm hl
  have old {x} (hx : x ∈ integerBoundaryPatch E B) (hs : x ∉ S) : x ∈ E :=
    hx.1.elim (fun h ↦ (hs (hB h)).elim) And.left
  have new {x} (hx : x ∈ integerBoundaryPatch E B) (hs : x ∈ S) : x ∈ B :=
    hx.1.elim id (fun h ↦ (h.2 hs).elim)
  have impossible (h₁ : a ∈ E) (h₂ : a*r ∈ E) (h₃ : a*r*r ∈ E) : False := by
    have hp := hpos a ha
    exact he h₁ h₂ h₃
      (by simpa using Nat.mul_lt_mul_of_pos_left hr hp)
      (by simpa using Nat.mul_lt_mul_of_pos_left hr (Nat.mul_pos hp (by omega)))
      (by ring) (by simp)
  by_cases hs : r ∈ S
  · by_cases h : a ∈ S
    · have h₂ := Nat.mul_mem_smoothNumbers h hs
      have h₃ := Nat.mul_mem_smoothNumbers h₂ hs
      exact (integerPrefixAdmissible_integral_iff (fun _ hx ↦ Nat.pos_of_ne_zero
        (Nat.ne_zero_of_mem_smoothNumbers (hB hx)))).mp hb a r hr (new ha h) (new hm h₂) (new hl h₃)
    · exact impossible (old ha h) (old hm (fun hh ↦ h (Nat.mem_smoothNumbers_of_dvd hh (dvd_mul_right a r))))
        (old hl (fun hh ↦ h (Nat.mem_smoothNumbers_of_dvd hh ((dvd_mul_right a r).trans (dvd_mul_right (a*r) r)))))
  · have h₂ : a*r ∉ S := fun h ↦ hs (Nat.mem_smoothNumbers_of_dvd h (dvd_mul_left r a))
    have h₃ : a*r*r ∉ S := fun h ↦ hs (Nat.mem_smoothNumbers_of_dvd h (dvd_mul_left r (a*r)))
    by_cases h : a ∈ E
    · exact impossible h (old hm h₂) (old hl h₃)
    · have hB' := ha.1.elim id (fun ⟨hm,_⟩ ↦ (h hm).elim)
      exact hl.2 ⟨a,⟨hB',h⟩,r,hs,rfl⟩

private theorem weight_partition {Y : ℕ} (A T : Set ℕ) (hA : A ⊆ Nat.smoothNumbers (Y+1)) :
    W (A ∩ T) + W (A \ T) = W A := by
  let w (n : ℕ) := (n:ℝ)⁻¹
  have hs {D : Set ℕ} (h : D ⊆ A) : Summable (D.indicator w) :=
    summable_subtype_iff_indicator.mp (smoothSubset_reciprocal_summable (h.trans hA))
  have weight (D : Set ℕ) : W D = ∑' n, D.indicator w n := _root_.tsum_subtype D w
  rw [weight,weight,weight]
  rw [← (hs (Set.inter_subset_left (s := A) (t := T))).tsum_add (hs Set.sdiff_subset)]
  apply tsum_congr
  intro n
  by_cases ha : n ∈ A <;> by_cases ht : n ∈ T <;> simp [ha,ht]

private theorem weight_endpoints_le {D R : Set ℕ} {Y : ℕ} (hD : D ⊆ S)
    (hR : R ⊆ Nat.smoothNumbers (Y+1)) (hEnds : R ⊆ integerBoundaryEndpoints D) :
    W R ≤ integerExchangeCharge * W D := by
  let P := D × ↥(Sᶜ : Set ℕ)
  have witnesses (n : R) : ∃ z : P, n.val = z.1.val*z.2.val*z.2.val := by
    obtain ⟨b,hb,r,hr,h⟩ := hEnds n.property
    exact ⟨(⟨b,hb⟩,⟨r,hr⟩),h⟩
  choose pick hp using witnesses
  have hi : Function.Injective pick := fun a b he ↦ Subtype.ext ((hp a).trans (he ▸ (hp b).symm))
  let f (b : D) := (b.val:ℝ)⁻¹
  let g (r : ↥(Sᶜ : Set ℕ)) := 1/(r.val:ℝ)^2
  have hf : Summable f := smoothSubset_reciprocal_summable (Y := 5) hD
  have hg : Summable g := summable_integerExchangeBoundaryTail
  have hfg := hf.mul_of_nonneg hg (fun b ↦ by dsimp [f]; positivity) (fun r ↦ by dsimp [g]; positivity)
  have hm := Summable.tsum_le_tsum_of_inj pick hi
    (fun (z : P) _ ↦ show 0 ≤ f z.1 * g z.2 by dsimp [f,g]; positivity)
    (fun n ↦ show (n.val:ℝ)⁻¹ ≤ f (pick n).1 * g (pick n).2 by
      rw [hp n]
      dsimp [f,g]
      push_cast
      simp only [mul_inv_rev,one_div,←inv_pow]
      apply le_of_eq
      ring)
    (smoothSubset_reciprocal_summable hR) hfg
  rw [← hf.tsum_mul_tsum hg hfg] at hm
  exact hm.trans ((mul_le_mul_of_nonneg_left integerExchangeBoundaryTail_lt.le
    (tsum_nonneg (fun b ↦ by dsimp [f]; positivity))).trans_eq (mul_comm _ _))

/-- The exchange gain on the initial smooth set survives at every larger
prime cutoff, provided the initial finite exchange pays its boundary charge. -/
theorem integerBoundaryPatch_weight {E B : Set ℕ} {Y : ℕ} (hY : 5 ≤ Y)
    (hE : E ⊆ Nat.smoothNumbers (Y+1)) (hB : B ⊆ Nat.smoothNumbers 6)
    (g : ℝ) (hgain : g ≤ W B - W (E ∩ S) - integerExchangeCharge * W (B \ (E ∩ S))) :
    W E + g ≤ W (integerBoundaryPatch E B) := by
  let U := B ∪ (E \ S)
  let D := integerBoundaryEndpoints (B \ E)
  have hU : U ⊆ Nat.smoothNumbers (Y+1) := fun _ hn ↦ hn.elim
    (fun hb ↦ Nat.smoothNumbers_mono (by omega : 6 ≤ Y+1) (hB hb)) (fun he ↦ hE he.1)
  have hn : B \ (E ∩ S) = B \ E := by
    ext n
    exact ⟨fun h ↦ ⟨h.1,fun he ↦ h.2 ⟨he,hB h.1⟩⟩,fun h ↦ ⟨h.1,fun he ↦ h.2 he.1⟩⟩
  rw [hn] at hgain
  have hin : U ∩ S = B := by
    ext n
    exact ⟨fun h ↦ h.1.elim id (fun he ↦ (he.2 h.2).elim),fun h ↦ ⟨Or.inl h,hB h⟩⟩
  have hout : U \ S = E \ S := by
    ext n
    exact ⟨fun h ↦ h.1.elim (fun hb ↦ (h.2 (hB hb)).elim) id,fun h ↦ ⟨Or.inr h,h.2⟩⟩
  have hu := weight_partition U S hU
  rw [hin,hout] at hu
  have he := weight_partition E S hE
  have hrem := weight_endpoints_le (D := B \ E) (R := U ∩ D) (fun _ h ↦ hB h.1)
    (fun _ h ↦ hU h.1) (fun _ h ↦ h.2)
  have hsplit := weight_partition U D hU
  change W E + g ≤ W (U \ D)
  linarith only [hgain,hu,he,hrem,hsplit]

end GRHArticle.ProgressionFree
