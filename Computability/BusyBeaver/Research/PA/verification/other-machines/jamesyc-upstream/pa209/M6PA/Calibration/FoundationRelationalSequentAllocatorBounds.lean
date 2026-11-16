module
public import M6PA.Theory
public import M6PA.Calibration.FoundationRelationalSequentBinderAlpha
@[expose] public section

/-! Common child allocator arithmetic. Both original allocator budgets and
both original valid environments are explicit premises. Reserve z is unchanged. -/
namespace M6.PA.RelationalSource.Numeric
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def commonAllocator (lo other : V) : V := max lo other+1

theorem left_lt_common (lo other : V) : lo<commonAllocator lo other :=
  lt_of_le_of_lt (le_max_left lo other) (lt_add_one _)
theorem right_lt_common (lo other : V) : other<commonAllocator lo other :=
  lt_of_le_of_lt (le_max_right lo other) (lt_add_one _)

theorem commonAllocator_budget {lo other parent child z : V} (hp : child<parent)
    (hl : lo+parent≤z) (hr : other+parent≤z) : commonAllocator lo other+child≤z := by
  have hc : child+1≤parent := succ_le_iff_lt.mpr hp
  rcases le_total lo other with h | h
  · unfold commonAllocator
    rw [max_eq_right h]
    have hh := le_trans (add_le_add (le_refl other) hc) hr
    simpa only [add_assoc,add_comm,add_left_comm] using hh
  · unfold commonAllocator
    rw [max_eq_left h]
    have hh := le_trans (add_le_add (le_refl lo) hc) hl
    simpa only [add_assoc,add_comm,add_left_comm] using hh

theorem environments_raise {b f lo other z : V} (h : EnvironmentsValid b f lo z)
    (hl : lo≤other) (hz : other≤z) : EnvironmentsValid b f other z := by
  refine ⟨lt_of_lt_of_le h.1 hl,hz,?_,?_⟩
  · intro i hi
    exact lt_of_lt_of_le (h.2.2.1 i hi) hl
  · intro i hi
    exact lt_of_lt_of_le (h.2.2.2 i hi) hl

theorem coverage_raise {b f lo other z p : V} (h : FormulaCovered b f lo z p)
    (hl : lo≤other) (hz : other+p≤z) : FormulaCovered b f other z p := by
  have ho : other≤z := le_trans (le_add_right (le_refl other)) hz
  exact ⟨⟨environments_raise h.1.1 hl ho,hz⟩,h.2⟩

theorem common_eigen_fresh {b f lo other z parent child : V}
    (hl : FormulaCovered b f lo z parent) (hr : FormulaCovered b f other z parent)
    (hp : child<parent) :
    FreshEnvironment lo b f (commonAllocator lo other) z ∧
      FreshEnvironment other b f (commonAllocator lo other) z := by
  have hb := commonAllocator_budget hp hl.1.2 hr.1.2
  have hm : commonAllocator lo other≤z := le_trans (le_add_right (le_refl (commonAllocator lo other))) hb
  constructor
  · refine ⟨left_lt_common _ _,ne_of_lt (lt_of_lt_of_le (left_lt_common _ _) hm),?_,?_⟩
    · intro i hi
      exact Ne.symm (ne_of_lt (hl.1.1.2.2.1 i hi))
    · intro i hi
      exact Ne.symm (ne_of_lt (hl.1.1.2.2.2 i hi))
  · refine ⟨right_lt_common _ _,ne_of_lt (lt_of_lt_of_le (right_lt_common _ _) hm),?_,?_⟩
    · intro i hi
      exact Ne.symm (ne_of_lt (hr.1.1.2.2.1 i hi))
    · intro i hi
      exact Ne.symm (ne_of_lt (hr.1.1.2.2.2 i hi))

theorem common_coverage_all {b f lo other z p : V}
    (hl : FormulaCovered b f lo z (qqAll p)) (hr : FormulaCovered b f other z (qqAll p)) :
    FormulaCovered (lo∷b) f (commonAllocator lo other) z p ∧
      FormulaCovered (other∷b) f (commonAllocator lo other) z p := by
  have hb := commonAllocator_budget (lt_forall p) hl.1.2 hr.1.2
  exact ⟨coverage_raise (coverage_all hl) (add_le_add (le_max_left lo other) (le_refl 1)) hb,
    coverage_raise (coverage_all hr) (add_le_add (le_max_right lo other) (le_refl 1)) hb⟩

theorem common_coverage_exs {b f lo other z p : V}
    (hl : FormulaCovered b f lo z (qqExs p)) (hr : FormulaCovered b f other z (qqExs p)) :
    FormulaCovered (lo∷b) f (commonAllocator lo other) z p ∧
      FormulaCovered (other∷b) f (commonAllocator lo other) z p := by
  have hb := commonAllocator_budget (lt_exists p) hl.1.2 hr.1.2
  exact ⟨coverage_raise (coverage_exs hl) (add_le_add (le_max_left lo other) (le_refl 1)) hb,
    coverage_raise (coverage_exs hr) (add_le_add (le_max_right lo other) (le_refl 1)) hb⟩

#print axioms left_lt_common
#print axioms right_lt_common
#print axioms commonAllocator_budget
#print axioms environments_raise
#print axioms coverage_raise
#print axioms common_eigen_fresh
#print axioms common_coverage_all
#print axioms common_coverage_exs
end M6.PA.RelationalSource.Numeric

