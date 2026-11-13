import PositiveMap86To87

/-! Source-only conditional 87→86 positive map. Both the scalar gap and
strict omega bound remain explicit; no decoder or endpoint is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ConditionalMap87To86Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing PositiveMap86To87Draft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def reverse (beta K : V) (v : Fin 14 → V) : Fin 14 → V :=
  Function.update v 13 (v 13-C beta v*K)

theorem reverse_positive (beta K : V) (v : Fin 14 → V) (hv : ∀ j, 0<v j)
    (hstrict : C beta v*K<v 13) : ∀ j, 0<reverse beta K v j := by
  intro j
  by_cases hj : j=13
  · subst j
    simpa [reverse] using tsub_pos_of_lt hstrict
  · simpa [reverse,hj] using hv j

/-- Natural omega−C*K casts correctly only under the explicit strict bound. -/
theorem cast_reverse (p : Fin 4 → ℤ) (beta K : V) (v : Fin 14 → V)
    (hport : (p 0 : DiffRing V)=ι beta) (hK : (p 1 : DiffRing V)=ι K)
    (hgap : v 1+v 2<q beta v) (hstrict : C beta v*K<v 13) :
    (fun j => ι (v j)) = Ring86To87Draft.transform p (fun j => ι (reverse beta K v j)) := by
  have hC := cast_C beta v hgap
  have hd : ι (v 13-C beta v*K)=ι (v 13)-ι (C beta v*K) := P72Root.ι_tsub (le_of_lt hstrict)
  funext j
  by_cases hj : j=13
  · subst j
    simp [reverse,Ring86To87Draft.transform,q,hport,hK,map_add,map_mul,map_one,hC,hd] <;> ring
  · simp [reverse,Ring86To87Draft.transform,hj]

/-- Conditional reverse map. Deriving the two strict premises from the 87
own-zero remains a separate calibration task. -/
theorem positive_map (p : Fin 4 → ℤ) (beta K : V) (v : Fin 14 → V)
    (hport : (p 0 : DiffRing V)=ι beta) (hK : (p 1 : DiffRing V)=ι K)
    (hv : ∀ j, 0<v j) (hgap : v 1+v 2<q beta v) (hstrict : C beta v*K<v 13)
    (hz : InternalZero (P87ShiftedGuard.graph p).output v) :
    ∃ v' : Fin 14 → V, (∀ j, 0<v' j) ∧ InternalZero (P86ResidueGraph.graph p).output v' := by
  refine ⟨reverse beta K v,reverse_positive beta K v hv hstrict,?_⟩
  apply (internalZero_iff _ _).mpr
  have h := Ring86To87Draft.output_eval p (fun j => ι (reverse beta K v j))
  rw [←cast_reverse p beta K v hport hK hgap hstrict] at h
  rw [←h]
  exact (internalZero_iff _ _).mp hz

end DiophantineConsistency.ConditionalMap87To86Draft

#print axioms DiophantineConsistency.ConditionalMap87To86Draft.positive_map
