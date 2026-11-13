import Trace73ModelSigns

/-! Exact equivalence with explicit shift sign and center bounds. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace73RestrictedIff
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75 Trace73ModelTransfer
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem restricted_iff (p : Fin 4 → ℕ) :
    (∃ v : Fin 10 → V, (∀ j, 0<v j) ∧ value75 (ports p) (castVal v) = 0 ∧
      0≤shift p v ∧ shift p v < ι (v 7)) ↔
    (∃ v : Fin 10 → V, (∀ j, 0<v j) ∧ Trace73Literal.graph73 (ports p) (castVal v) = 0 ∧
      0≤shift p v) := by
  constructor
  · rintro ⟨v,hv,hz,hs,hbound⟩
    obtain ⟨d,hd⟩ := nonneg_iff.mp hs
    have hdlt : d < v 7 := ι_lt_ι.mp (hd ▸ hbound)
    let w := Function.update v 7 (v 7-d)
    have hw : ∀ j, 0<w j := by
      intro j
      by_cases hj : j=7
      · subst j; simpa [w] using tsub_pos_of_lt hdlt
      · simpa [w,hj] using hv j
    have hlift : Trace73Center.lift (ports p) (castVal w) = castVal v := by
      funext j
      by_cases hj : j=7
      · subst j
        change (ι (v 7-d):DiffRing V)+shift p w = ι (v 7)
        rw [show shift p w = shift p v from shift_update p v _]
        rw [hd, ← map_add, tsub_add_cancel_of_le (le_of_lt hdlt)]
      · simp [Trace73Center.lift,castVal,w,hj]
    refine ⟨w,hw,?_,?_⟩
    · rw [← Trace73Literal.parent_substitution, hlift]; exact hz
    · simpa only [w,shift_update] using hs
  · rintro ⟨v,hv,hz,hs⟩
    obtain ⟨d,hd⟩ := nonneg_iff.mp hs
    let w := Function.update v 7 (v 7+d)
    have hw : ∀ j, 0<w j := by
      intro j
      by_cases hj : j=7
      · subst j; simpa [w] using lt_of_lt_of_le (hv 7) (le_add_of_nonneg_right (zero_le : 0≤d))
      · simpa [w,hj] using hv j
    have hlift : Trace73Center.lift (ports p) (castVal v) = castVal w := by
      funext j
      by_cases hj : j=7
      · subst j
        change (ι (v 7):DiffRing V)+shift p v = ι (v 7+d)
        rw [hd, map_add]
      · simp [Trace73Center.lift,castVal,w,hj]
    refine ⟨w,hw,?_,?_,?_⟩
    · rw [← hlift, Trace73Literal.parent_substitution]; exact hz
    · simpa only [w,shift_update] using hs
    · rw [show shift p w = shift p v from shift_update p v _,hd]
      have hlt : d < v 7 + d := by
        have h := add_lt_add_right (hv 7) d
        simpa using h
      apply ι_lt_ι.mpr
      simpa [w] using hlt

#print axioms Trace73RestrictedIff.restricted_iff
end Trace73RestrictedIff
