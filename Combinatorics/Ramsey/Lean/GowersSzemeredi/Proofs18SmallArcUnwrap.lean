import GowersSzemeredi.Proofs18NaturalWrapSplit
import GowersSzemeredi.Proofs13CommonStepCover

/-! A carrier-injective modular progression in a short arc has at most two
ordinary progression pieces in the standard representatives. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Unwrap a short-arc progression after translating its arc to zero. -/
theorem ModAP.exists_short_arc_natAP {N d : Nat} [NeZero N]
    (P : ModAP N) (hP : P.IsProper) (hdiam : diameterAtMost P.carrier d)
    (hshort : 2 * (d + 1) < N) :
    ∃ a : ZMod N, ∃ Q : NatAP, Q.IsProper ∧ Q.length = P.length ∧
      Q.carrier ⊆ Finset.range (d + 1) ∧
      P.carrier = Q.carrier.image (fun x : Nat => a + (x : ZMod N)) := by
  obtain ⟨a, ha⟩ := hdiam
  have hRc : (P.translateBy (-a)).carrier = P.carrier.image (fun x => -a + x) := by
    rw [ModAP.translateBy_carrier, translateFinset]
  obtain ⟨Q, hQ, hlen, hQc, hQsub⟩ := (P.translateBy (-a)).exists_natAP_of_short_interval
    (P.translateBy_isProper (-a) hP) hshort (by
      rw [hRc]
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨i, hi, rfl⟩ := mem_modInterval_index a y d (ha hy)
      exact Finset.mem_image.mpr ⟨⟨i, by omega⟩, Finset.mem_univ _, by simp⟩)
  refine ⟨a, Q, hQ, hlen, hQsub, ?_⟩
  rw [hQc, hRc, Finset.image_image, Finset.image_image]
  simp only [Function.comp_def, ZMod.natCast_zmod_val, add_neg_cancel_left, Finset.image_id']

/-- A short-arc modular progression has exactly the natural representatives
of a disjoint union of two ordinary progressions. -/
theorem ModAP.exists_two_natAPs_of_small_diameter {N d : Nat} [NeZero N]
    (P : ModAP N) (hP : P.IsProper) (hdiam : diameterAtMost P.carrier d)
    (hshort : 2 * (d + 1) < N) :
    ∃ Q R : NatAP, Q.IsProper ∧ R.IsProper ∧ Disjoint Q.carrier R.carrier ∧
      Q.carrier ∪ R.carrier = P.carrier.image ZMod.val := by
  obtain ⟨a, T, hT, _, hTsub, hcarrier⟩ := P.exists_short_arc_natAP hP hdiam hshort
  have hTN : T.carrier ⊆ Finset.range N := hTsub.trans (Finset.range_mono (by omega))
  obtain ⟨Q, R, hQ, hR, hdis, hc⟩ := T.exists_modular_translate_split hT N a.val a.val_lt hTN
  refine ⟨Q, R, hQ, hR, hdis, ?_⟩
  rw [hc, hcarrier, Finset.image_image]
  apply Finset.image_congr
  intro x _
  change (a.val + x) % N = (a + (x : ZMod N)).val
  have heq : a + (x : ZMod N) = ((a.val + x : Nat) : ZMod N) := by simp
  rw [heq, ZMod.val_natCast]

/-- Clipping a short-arc modular progression to an interval has at most two
ordinary pieces, with exact coverage including the crossing cells. -/
theorem ModAP.exists_two_natAPs_inter_interval {N d L : Nat} [NeZero N]
    (P : ModAP N) (hP : P.IsProper) (hdiam : diameterAtMost P.carrier d)
    (hshort : 2 * (d + 1) < N) :
    ∃ Q R : NatAP, Q.IsProper ∧ R.IsProper ∧ Disjoint Q.carrier R.carrier ∧
      Q.carrier ∪ R.carrier = (P.carrier.image ZMod.val) ∩ Finset.range L := by
  obtain ⟨Q₀, R₀, hQ₀, hR₀, hdis, hc⟩ := P.exists_two_natAPs_of_small_diameter hP hdiam hshort
  obtain ⟨Q, hQ, hQc⟩ := Q₀.exists_inter_Ico hQ₀ 0 L
  obtain ⟨R, hR, hRc⟩ := R₀.exists_inter_Ico hR₀ 0 L
  refine ⟨Q, R, hQ, hR, ?_, ?_⟩
  · rw [hQc, hRc]
    exact hdis.mono Finset.inter_subset_left Finset.inter_subset_left
  · rw [hQc, hRc, ← Finset.union_inter_distrib_right, hc, ← Finset.range_eq_Ico]

end LeanProofs.GowersSzemeredi
