module
public import M6PA.Theory
public import M6PA.Calibration.FoundationRelationalSequentPadEnvironment
@[expose] public section

/-! Padding preserves finite label validity and supplies a proof-code budget
without replacing any of the requested free labels. -/
namespace M6.PA.RelationalSource.Numeric
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

theorem environment_pad {b f lo z : V} (h : EnvironmentsValid b f lo z) (n : V) :
    EnvironmentsValid b (padEnvironment f n) lo z := by
  refine ⟨h.1,h.2.1,h.2.2.1,?_⟩
  intro i hi
  obtain ⟨hlen,hprefix,hzero⟩ := padEnvironment_properties f n
  rw [hlen] at hi
  rcases lt_or_ge i (len f) with hp | hz
  · rw [hprefix i hp]
    exact h.2.2.2 i hp
  · rw [hzero i hi hz]
    exact h.1

theorem padded_proofEnvironment (d f lo z : V) (h : EnvironmentsValid 0 f lo z) :
    ProofEnvironment d (padEnvironment f d) lo (z+lo+d) := by
  refine ⟨?_,?_,?_⟩
  · have he := environment_pad h d
    exact ⟨he.1,le_trans he.2.1 (by simp),he.2.2⟩
  · rw [(padEnvironment_properties f d).1]
    simp
  · simp [add_assoc]

theorem padded_formula_coverage {p b f lo z : V}
    (h : FormulaCovered b f lo z p) (n : V) :
    FormulaCovered b (padEnvironment f n) lo z p := by
  refine ⟨⟨environment_pad h.1.1 n,h.1.2⟩,h.2.1,?_⟩
  rw [(padEnvironment_properties f n).1]
  exact le_trans h.2.2 (by simp)

#print axioms environment_pad
#print axioms padded_proofEnvironment
#print axioms padded_formula_coverage
end M6.PA.RelationalSource.Numeric

