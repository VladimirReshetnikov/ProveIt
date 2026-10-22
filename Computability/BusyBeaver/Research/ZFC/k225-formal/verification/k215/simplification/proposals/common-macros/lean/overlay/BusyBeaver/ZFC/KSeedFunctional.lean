import BusyBeaver.ZFC.KSeed222

/-!
Functional seed relations need no repeated choice of an equal output.
This module is an additive proposal against ProveIt 6d9800d1ca67.
-/

namespace SetTheory.BusyBeaver.ZFC.KSeed222

universe u
variable {V : Type u} {mem Q : V → V → Prop} {A C : V}

/-- A seed container for a single-valued relation: retain every requested output,
record the origin of each member, and close under requests below members. -/
structure SeedClosure (mem Q : V → V → Prop) (A C : V) : Prop where
  root : ∀ y, Q A y → mem y C
  image : ∀ y, mem y C → ∃ x, Q x y
  step : ∀ y, mem y C → ∀ x, (∀ w, mem w x → mem w y) → ∀ z, Q x z → mem z C

/-- Exact, constructive normalization of the existing seed property. -/
theorem seedProp_iff_closure
    (hQ : ∀ x y z, Q x y → Q x z → y = z) :
    SeedProp mem Q A ↔ ∃ C, SeedClosure mem Q A C := by
  constructor
  · rintro ⟨C, hroot, hstep⟩
    refine ⟨C, ?_, ?_, ?_⟩
    · intro y hy
      obtain ⟨z, hz, hzC⟩ := hroot y hy
      exact hQ A z y hz hy ▸ hzC
    · intro y hy
      obtain ⟨x, hx, -⟩ := hstep y hy
      exact ⟨x, hx⟩
    · intro y hy x hxy z hz
      obtain ⟨_, _, hcl⟩ := hstep y hy
      obtain ⟨z', hz', hz'C⟩ := hcl x hxy z hz
      exact hQ x z' z hz' hz ▸ hz'C
  · rintro ⟨C, h⟩
    exact ⟨C, fun y hy => ⟨y, hy, h.root y hy⟩,
      fun y hy => let ⟨x, hx⟩ := h.image y hy
        ⟨x, hx, fun x' hsub z hz => ⟨z, hz, h.step y hy x' hsub z hz⟩⟩⟩

#print axioms seedProp_iff_closure

end SetTheory.BusyBeaver.ZFC.KSeed222
