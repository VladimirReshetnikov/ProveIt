import OwnZeroQuotient86
import FreshRoot86
import PositiveMap85To86

/-! Source-only 86→85 fresh-root positive witness map. All bare imports are
unelaborated drafts; no Lean result or endpoint is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.FreshMap86To85Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing
open FirstFields86Draft OwnZeroQuotient86Draft FreshRoot86Draft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Replace Y by its q³ quotient and choose the new first root P+tau. -/
def reverse (v : Fin 14 → V) (s tau : V) : Fin 14 → V :=
  Function.update (Function.update v 7 s) 8 (firstP v+tau)

theorem reverse_positive (v : Fin 14 → V) (s tau : V)
    (hv : ∀ j, 0<v j) (hs : 0<s) (htau : 0<tau) : ∀ j, 0<reverse v s tau j := by
  intro j
  by_cases hj8 : j=8
  · subst j
    have hp : 0<firstP v+tau := lt_of_lt_of_le htau (by simp)
    simpa [reverse] using hp
  · by_cases hj7 : j=7
    · subst j
      simpa [reverse] using hs
    · simpa [reverse,hj8,hj7] using hv j

/-- Forward substitution of this fresh 85 valuation is the fresh 86
valuation, provided the natural quotient equation is explicit. -/
theorem forward_reverse (beta : V) (v : Fin 14 → V) (s tau : V)
    (hY : v 7=Q beta v*s) :
    PositiveMap85To86Draft.forward beta (reverse v s tau)=fresh v s tau := by
  funext j
  by_cases hj8 : j=8
  · subst j
    simp [PositiveMap85To86Draft.forward,reverse,fresh,putRoot]
  · by_cases hj7 : j=7
    · subst j
      simp [PositiveMap85To86Draft.forward,PositiveMap85To86Draft.q,reverse,fresh,putRoot,
        Q,q,hY]
    · simp [PositiveMap85To86Draft.forward,reverse,fresh,putRoot,hj8,hj7]

/-- Proposed positive map from an 86 own-zero to an 85 zero. The new first
root need not preserve or be bounded by the old first coordinate. -/
theorem positive_map (p : Fin 4 → ℤ) (beta : V) (v : Fin 14 → V)
    (hbeta : 0<beta) (hport : (p 0 : DiffRing V)=ι beta) (hv : ∀ j, 0<v j)
    (hz : InternalZero (P86ResidueGraph.graph p).output v) :
    ∃ v' : Fin 14 → V, (∀ j, 0<v' j) ∧ InternalZero (P85QcubeGraph.graph p).output v' := by
  obtain ⟨s,tau,hs,hY,htau,hn⟩ := OwnZeroQuotient86Draft.quotient_and_root
    p beta v hbeta (hv 0) (hv 7) hport hz
  let w := reverse v s tau
  have hpos : ∀ j, 0<w j := reverse_positive v s tau hv hs htau
  have hfresh := fresh_zero p beta v s tau hport hY hn hz
  have h := Ring85To86Draft.output_eval p (fun j => ι (w j))
  rw [←PositiveMap85To86Draft.cast_forward p beta w hport] at h
  have hforward : PositiveMap85To86Draft.forward beta w=fresh v s tau := forward_reverse beta v s tau hY
  rw [hforward] at h
  refine ⟨w,hpos,?_⟩
  apply (internalZero_iff _ _).mpr
  rw [←h]
  exact (internalZero_iff _ _).mp hfresh

end DiophantineConsistency.FreshMap86To85Draft

#print axioms DiophantineConsistency.FreshMap86To85Draft.positive_map
