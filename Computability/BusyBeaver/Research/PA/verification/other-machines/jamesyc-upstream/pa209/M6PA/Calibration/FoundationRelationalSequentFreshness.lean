module
public import M6PA.Theory
public import M6PA.Calibration.FoundationRelationalSequentFree
@[expose] public section

/-! Explicit finite-environment freshness for subsequent numeric vacuity.
The quantified name lies below every future allocator, but need not be above
all old names. Guarded term coverage remains a separate hypothesis. -/
namespace M6.PA.RelationalSource.Numeric
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def FreshEnvironment (c b f lo z : V) : Prop :=
  c<lo ∧ c≠z ∧ (∀ i<len b, c≠nth b i) ∧ ∀ i<len f, c≠nth f i

noncomputable def freshEnvironmentGraph : 𝚺ᴬ₁.Semisentence 5 := .mkSigma
  “c b f lo z. c<lo ∧ c≠z ∧ ∃ nb nf, !lenDef nb b ∧ !lenDef nf f ∧
    (∀ i<nb, ∃ y, !nthDef y b i ∧ c≠y) ∧
    (∀ i<nf, ∃ y, !nthDef y f i ∧ c≠y)”

theorem freshEnvironment_graph (c b f lo z : V) :
    freshEnvironmentGraph.val.Evalb ![c,b,f,lo,z] ↔ FreshEnvironment c b f lo z := by
  simp [freshEnvironmentGraph,FreshEnvironment,Matrix.comp_vecCons'']

theorem FreshEnvironment.advance {c b f lo z : V} (h : FreshEnvironment c b f lo z) :
    FreshEnvironment c (lo∷b) f (lo+1) z := by
  refine ⟨lt_trans h.1 (by simp),h.2.1,?_,h.2.2.2⟩
  intro i hi
  rcases zero_or_succ i with rfl | ⟨i,rfl⟩
  · simpa using ne_of_lt h.1
  · have hi' : i<len b := by simpa using hi
    simpa using h.2.2.1 i hi'

theorem FreshEnvironment.label_ne {c b f lo z y t : V}
    (h : FreshEnvironment c b f lo z) (ht : VariableLabel y t b f) : c≠y := by
  rcases ht with ⟨i,hi,_,rfl⟩ | ⟨i,hi,_,rfl⟩
  · exact h.2.2.1 i hi
  · exact h.2.2.2 i hi

theorem FreshEnvironment.totalLabel_ne {c b f lo z t : V}
    (h : FreshEnvironment c b f lo z) (ht : Covered t b f) : c≠totalLabel t b f := by
  obtain ⟨y,hy⟩ := (label_exists_iff _ _ _).mpr ht
  rw [← totalLabel_agrees hy]
  exact h.label_ne hy

/-- Old valid names are below lo; using lo as the new eigenlabel becomes
fresh at allocator lo+1. The reserve must explicitly differ from lo. -/
theorem environments_eigenFresh {b f lo z : V} (h : EnvironmentsValid b f lo z)
    (hz : lo≠z) : FreshEnvironment lo b f (lo+1) z := by
  refine ⟨by simp,hz,?_,?_⟩
  · intro i hi
    exact Ne.symm (ne_of_lt (h.2.2.1 i hi))
  · intro i hi
    exact Ne.symm (ne_of_lt (h.2.2.2 i hi))

/-- Freshness is preserved by free-variable shift with the matching finite
extension only when the extra label also avoids the quantified name. -/
theorem FreshEnvironment.prependFree {c b f lo z x : V}
    (h : FreshEnvironment c b f lo z) (hx : c≠x) :
    FreshEnvironment c b (x∷f) lo z := by
  refine ⟨h.1,h.2.1,h.2.2.1,?_⟩
  intro i hi
  rcases zero_or_succ i with rfl | ⟨i,rfl⟩
  · simpa using hx
  · have hi' : i<len f := by simpa using hi
    simpa using h.2.2.2 i hi'

#print axioms freshEnvironment_graph
#print axioms FreshEnvironment.advance
#print axioms FreshEnvironment.label_ne
#print axioms FreshEnvironment.totalLabel_ne
#print axioms environments_eigenFresh
#print axioms FreshEnvironment.prependFree
end M6.PA.RelationalSource.Numeric

