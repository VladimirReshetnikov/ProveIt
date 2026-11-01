import DiophantineConsistency.AdaptiveGap85ResidueFeasibility
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85SameCoordinates
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 AdaptiveGap85Literal AdaptiveGap85ResidueFeasibility
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Whenever Jβ divides X+K, no positive full zero preserving J and X can
have the reverse gap, regardless of the transformation used to seek it. -/
theorem divisible_coefficient_blocks_same_JX (p : Fin 4 → ℕ) (v w : Fin 13 → V)
    (hb : 0<(p 0:V)) (hw : ∀i,0<w i)
    (hz : InternalZero (expressionAt85 (fun j => (p j:ℤ))) w)
    (hJ : w 0=v 0) (hX : w 6=v 6)
    (hA : v 0*(p 0:V) ∣ v 6+(p 1:V)) :
    ¬w 1+w 2<1+w 0*(p 0:V) := by
  have ha : w 0*(p 0:V) ∣ w 6+(p 1:V) := by rw [hJ,hX]; exact hA
  intro hgap
  exact (normalized_actual_zero_coefficient p w hb hw hz hgap) ha
end DiophantineConsistency.AdaptiveGap85SameCoordinates
