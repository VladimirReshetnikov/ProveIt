import DiophantineConsistency.AdaptiveGap85DivisibleGap
set_option autoImplicit false
/-! Abstract residue-preserving coordinate shifts; no zero existence is asserted. -/
namespace DiophantineConsistency.AdaptiveGap85ShiftResidue
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem move_residue (b F Fnew t : V) (hb : 0<b)
    (h : Fnew=F+b*t ∨ Fnew+b*t=F) : Fnew%b=F%b := by
  rcases h with hf | hr
  · rw [hf,mod_add_mul' _ _ hb]
  · have hh := congrArg (fun x : V => x%b) hr
    simpa only [mod_add_mul' _ _ hb] using hh

theorem move_preserves (b F Fnew t : V) (hb : 0<b)
    (h : Fnew=F+b*t ∨ Fnew+b*t=F) (hd : b∣F) : b∣Fnew := by
  apply mod_eq_zero_iff_dvd.mp
  rw [move_residue b F Fnew t hb h]
  exact mod_eq_zero_iff_dvd.mpr hd
def Step (b : V) (p r : V × V) : Prop :=
  (∃ t, r.1=p.1+b*t ∨ r.1+b*t=p.1) ∧
  (∃ t, r.2=p.2+b*t ∨ r.2+b*t=p.2)

theorem step_preserves (b : V) (p r : V × V) (hb : 0<b) (h : Step b p r)
    (hd : b∣p.1 ∨ b∣p.2) : b∣r.1 ∨ b∣r.2 := by
  rcases h with ⟨⟨t,ht⟩,⟨s,hs⟩⟩
  rcases hd with hF | hC
  · exact Or.inl (move_preserves b p.1 r.1 t hb ht hF)
  · exact Or.inr (move_preserves b p.2 r.2 s hb hs hC)

theorem orbit_preserves (b : V) (p r : V × V) (hb : 0<b)
    (h : Relation.ReflTransGen (Step b) p r) (hd : b∣p.1 ∨ b∣p.2) :
    b∣r.1 ∨ b∣r.2 := by
  induction h with
  | refl => exact hd
  | tail _ hs ih => exact step_preserves b _ _ hb hs ih

theorem orbit_blocks (b : V) (p r : V × V) (hb : 0<b)
    (h : Relation.ReflTransGen (Step b) p r) (hd : b∣p.1 ∨ b∣p.2)
    (hF : 0<r.1) (hC : 0<r.2) : ¬ r.1+r.2<1+b := by
  rcases orbit_preserves b p r hb h hd with hFdiv | hCdiv
  · exact AdaptiveGap85DivisibleGap.divisible_blocks b r.1 r.2 hF hC hFdiv
  · simpa only [add_comm r.1 r.2] using
      AdaptiveGap85DivisibleGap.divisible_blocks b r.2 r.1 hC hF hCdiv
end DiophantineConsistency.AdaptiveGap85ShiftResidue
