module
public import M6PA.Theory
public import M6PA.Calibration.RelationalIsoCompositionEdge
@[expose] public section

/-! Two actual intermediate witnesses with capture-aware context inclusion. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND

def compositionEdgesEliminate {Γ : List Form} (g h x z u w : Nat) (q : Form)
    (hx : ND.Proof Γ (compositionEdge (.fvar g) (.fvar h) (.fvar x) (.fvar z)))
    (hu : ND.Proof Γ (compositionEdge (.fvar g) (.fvar h) (.fvar u) (.fvar w)))
    (k : ∀ {Δ : List Form}, (∀ p, p ∈ shifted (shifted Γ) → p ∈ Δ) →
      ND.Proof Δ (edge (.fvar (g+1+1)) (.fvar (x+1+1)) (.fvar 1)) →
      ND.Proof Δ (edge (.fvar (h+1+1)) (.fvar 1) (.fvar (z+1+1))) →
      ND.Proof Δ (edge (.fvar (g+1+1)) (.fvar (u+1+1)) (.fvar 0)) →
      ND.Proof Δ (edge (.fvar (h+1+1)) (.fvar 0) (.fvar (w+1+1))) →
      ND.Proof Δ q.shift.shift) : ND.Proof Γ q := by
  apply compositionEdgeEliminate g h x z _ hx
  intro Δ inc hxy hyz
  have hu' : ND.Proof Δ (compositionEdge (.fvar (g+1)) (.fvar (h+1)) (.fvar (u+1)) (.fvar (w+1))) := by
    convert ND.weaken (shiftProof hu) inc using 1 <;> compositionSyntax
  apply compositionEdgeEliminate (g+1) (h+1) (u+1) (w+1) _ hu'
  intro Θ inc' huv hvw
  have hxy' : ND.Proof Θ (edge (.fvar (g+1+1)) (.fvar (x+1+1)) (.fvar 1)) := by
    convert ND.weaken (shiftProof hxy) inc' using 1 <;> compositionSyntax
  have hyz' : ND.Proof Θ (edge (.fvar (h+1+1)) (.fvar 1) (.fvar (z+1+1))) := by
    convert ND.weaken (shiftProof hyz) inc' using 1 <;> compositionSyntax
  apply k (Δ := Θ) _ hxy' hyz' huv hvw
  intro p hp
  apply inc'
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hp
  exact List.mem_map.mpr ⟨r,inc r hr,rfl⟩

#print axioms compositionEdgesEliminate
end M6.PA.RelationalSource.PairGraph
