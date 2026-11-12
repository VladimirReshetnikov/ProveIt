import GuardGap86
import RingComparison86To87
import DiophantineConsistency.Compact44.P72Root

/-! Source-only positive 86→87 witness map. All imported graph clients are
unelaborated drafts; no reverse implication or endpoint is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.PositiveMap86To87Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def q (beta : V) (v : Fin 14 → V) : V := 1+v 0*beta
def C (beta : V) (v : Fin 14 → V) : V := (q beta v-v 1)-v 2
def forward (beta K : V) (v : Fin 14 → V) : Fin 14 → V :=
  Function.update v 13 (v 13+C beta v*K)

/-- The strict scalar gap justifies both natural subtraction casts. -/
theorem cast_C (beta : V) (v : Fin 14 → V) (hgap : v 1+v 2<q beta v) :
    ι (C beta v)=ι (q beta v)-ι (v 1)-ι (v 2) := by
  have hF : v 1≤q beta v := le_of_lt (lt_of_le_of_lt
    (le_add_of_nonneg_right (Arithmetic.zero_le (v 2))) hgap)
  have he : q beta v-v 1+v 1=q beta v := tsub_add_cancel_of_le hF
  have ha : v 2<q beta v-v 1 := by
    apply (add_lt_add_iff_right (v 1)).mp
    rw [he]
    simpa only [add_comm] using hgap
  have hq := P72Root.ι_tsub hF
  have hc := P72Root.ι_tsub (le_of_lt ha)
  simpa only [C,hq] using hc

theorem forward_positive (beta K : V) (v : Fin 14 → V) (hv : ∀ j, 0<v j) :
    ∀ j, 0<forward beta K v j := by
  intro j
  by_cases hj : j=13
  · subst j
    simpa [forward] using add_pos_of_pos_of_nonneg (hv 13) (Arithmetic.zero_le (C beta v*K))
  · simpa [forward,hj] using hv j

theorem cast_forward (p : Fin 4 → ℤ) (beta K : V) (v : Fin 14 → V)
    (hport : (p 0 : DiffRing V)=ι beta) (hK : (p 1 : DiffRing V)=ι K)
    (hgap : v 1+v 2<q beta v) :
    (fun j => ι (forward beta K v j)) = Ring86To87Draft.transform p (fun j => ι (v j)) := by
  have hC := cast_C beta v hgap
  funext j
  by_cases hj : j=13
  · subst j
    simp [forward,Ring86To87Draft.transform,q,hport,hK,map_add,map_mul,map_one,hC]
  · simp [forward,Ring86To87Draft.transform,hj]

/-- Positive 86→87 map from the 86 own-zero guard gap. -/
theorem positive_map (p : Fin 4 → ℤ) (beta K : V) (v : Fin 14 → V)
    (hport : (p 0 : DiffRing V)=ι beta) (hK : (p 1 : DiffRing V)=ι K)
    (hv : ∀ j, 0<v j) (hz : InternalZero (P86ResidueGraph.graph p).output v) :
    ∃ v' : Fin 14 → V, (∀ j, 0<v' j) ∧ InternalZero (P87ShiftedGuard.graph p).output v' := by
  have hgap : v 1+v 2<q beta v := by
    simpa only [q,AuxGraphNormClientDraft.q] using
      GuardGap86Draft.gap_of_86_zero p beta K v hport hK (hv 1) (hv 6) hz
  refine ⟨forward beta K v,forward_positive beta K v hv,?_⟩
  apply (internalZero_iff _ _).mpr
  have h := Ring86To87Draft.output_eval p (fun j => ι (v j))
  rw [←cast_forward p beta K v hport hK hgap] at h
  rw [h]
  exact (internalZero_iff _ _).mp hz

end DiophantineConsistency.PositiveMap86To87Draft

#print axioms DiophantineConsistency.PositiveMap86To87Draft.positive_map
