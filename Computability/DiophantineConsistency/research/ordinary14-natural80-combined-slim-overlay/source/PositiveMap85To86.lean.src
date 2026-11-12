import RingComparison85To86
import DiophantineConsistency.Compact44.P72Root

/-! Source-only positive 85→86 witness map. Draft graph/ring imports are
unelaborated; no reverse or endpoint result is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.PositiveMap85To86Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing Ring85To86Draft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def q (beta : V) (v : Fin 14 → V) : V := 1+v 0*beta

def forward (beta : V) (v : Fin 14 → V) : Fin 14 → V :=
  Function.update (Function.update v 7 (q beta v*(q beta v*q beta v)*v 7)) 8 (v 8+v 7)

theorem forward_positive (beta : V) (v : Fin 14 → V) (hv : ∀ j, 0<v j) :
    ∀ j, 0<forward beta v j := by
  have hq : 0<q beta v := by dsimp [q]; simp
  intro j
  by_cases hj8 : j=8
  · subst j
    simpa [forward] using add_pos (hv 8) (hv 7)
  · by_cases hj7 : j=7
    · subst j
      simpa [forward] using mul_pos (mul_pos hq (mul_pos hq hq)) (hv 7)
    · simpa [forward,hj8,hj7] using hv j

theorem cast_forward (p : Fin 4 → ℤ) (beta : V) (v : Fin 14 → V)
    (hport : (p 0 : DiffRing V)=ι beta) :
    (fun j => ι (forward beta v j)) = Ring85To86Draft.transform p (fun j => ι (v j)) := by
  funext j
  by_cases hj8 : j=8
  · subst j
    simp [forward,Ring85To86Draft.transform,map_add]
  · by_cases hj7 : j=7
    · subst j
      simp [forward,Ring85To86Draft.transform,q,hport,map_add,map_mul,map_one]
    · simp [forward,Ring85To86Draft.transform,hj8,hj7]

/-- Forward positive-zero map, with explicit beta cast; beta need only be a
natural model value in this direction. -/
theorem positive_map (p : Fin 4 → ℤ) (beta : V) (v : Fin 14 → V)
    (hport : (p 0 : DiffRing V)=ι beta) (hv : ∀ j, 0<v j)
    (hz : InternalZero (P85QcubeGraph.graph p).output v) :
    ∃ v' : Fin 14 → V, (∀ j, 0<v' j) ∧ InternalZero (P86ResidueGraph.graph p).output v' := by
  refine ⟨forward beta v,forward_positive beta v hv,?_⟩
  apply (internalZero_iff _ _).mpr
  have h := Ring85To86Draft.output_eval p (fun j => ι (v j))
  rw [←cast_forward p beta v hport] at h
  rw [h]
  exact (internalZero_iff _ _).mp hz

end DiophantineConsistency.PositiveMap85To86Draft

#print axioms DiophantineConsistency.PositiveMap85To86Draft.positive_map
