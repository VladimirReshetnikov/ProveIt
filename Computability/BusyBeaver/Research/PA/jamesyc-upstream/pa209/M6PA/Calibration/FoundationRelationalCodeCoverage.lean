module
public import M6PA.Theory
public import M6PA.Calibration.FoundationRelationalCodeRecursion
@[expose] public section

/-! A conservative all-model coverage invariant. The free environment is assumed
long enough for the source code; this is sufficient, not necessary, and no
existence of such an environment is inferred. -/
namespace M6.PA.RelationalSource.Numeric
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def FormulaCovered (b f lo z p : V) : Prop :=
  Guard b f lo z p ∧ IsSemiformula language (len b) p ∧ p≤len f

noncomputable def coverageGraph : 𝚺ᴬ₁.Semisentence 5 := .mkSigma
  “b f lo z p. !guardGraph b f lo z p ∧ ∃ n m, !lenDef n b ∧ !lenDef m f ∧
    !((isSemiformula language).sigma) n p ∧ p≤m”

theorem coverage_graph (b f lo z p : V) :
    coverageGraph.val.Evalb ![b,f,lo,z,p] ↔ FormulaCovered b f lo z p := by
  simp [coverageGraph,FormulaCovered,guard_graph,Matrix.comp_vecCons'']

theorem term_covered_of_code_bound {t b f : V}
    (ht : IsSemiterm language (len b) t) (hf : t≤len f) : Covered t b f := by
  refine ⟨ht,?_⟩
  intro i he
  rw [he] at hf
  exact lt_of_lt_of_le (var_lt_qqFvar i) hf

theorem coverage_all {b f lo z p : V} (h : FormulaCovered b f lo z (qqAll p)) :
    FormulaCovered (lo ∷ b) f (lo+1) z p := by
  refine ⟨guard_all h.1,?_,le_trans (lt_forall p).le h.2.2⟩
  simpa using h.2.1

theorem coverage_exs {b f lo z p : V} (h : FormulaCovered b f lo z (qqExs p)) :
    FormulaCovered (lo ∷ b) f (lo+1) z p := by
  refine ⟨guard_exs h.1,?_,le_trans (lt_exists p).le h.2.2⟩
  simpa using h.2.1

theorem coverage_and {b f lo z p q : V} (h : FormulaCovered b f lo z (qqAnd p q)) :
    FormulaCovered b f lo z p ∧ FormulaCovered b f lo z q := by
  have hpq := IsSemiformula.and.mp h.2.1
  exact ⟨⟨guard_child h.1 (lt_K!_left p q).le,hpq.1,
    le_trans (lt_K!_left p q).le h.2.2⟩,
    ⟨guard_child h.1 (lt_K!_right p q).le,hpq.2,
    le_trans (lt_K!_right p q).le h.2.2⟩⟩

theorem coverage_or {b f lo z p q : V} (h : FormulaCovered b f lo z (qqOr p q)) :
    FormulaCovered b f lo z p ∧ FormulaCovered b f lo z q := by
  have hpq := IsSemiformula.or.mp h.2.1
  exact ⟨⟨guard_child h.1 (lt_or_left p q).le,hpq.1,
    le_trans (lt_or_left p q).le h.2.2⟩,
    ⟨guard_child h.1 (lt_or_right p q).le,hpq.2,
    le_trans (lt_or_right p q).le h.2.2⟩⟩

theorem coverage_rel_atom {b f lo z k r ts : V}
    (h : FormulaCovered b f lo z (qqRel k r ts)) :
    ∃ y, AtomTranslation y k r ts b f lo z := by
  obtain ⟨hr,ht⟩ := IsSemiformula.rel.mp h.2.1
  obtain ⟨hk,htags⟩ := source_relations _ _ |>.mp hr
  subst k
  apply (atom_exists_iff _ _ _ _ _ _ _).mpr
  refine ⟨rfl,ht.lh,h.1.1,?_,?_,htags⟩
  · apply term_covered_of_code_bound (ht.nth (by simp))
    exact le_trans (nth_lt_qqRel_of_lt (by rw [ht.lh]; simp)).le h.2.2
  · apply term_covered_of_code_bound (ht.nth (by simp))
    exact le_trans (nth_lt_qqRel_of_lt (by rw [ht.lh]; simp)).le h.2.2

theorem coverage_nrel_atom {b f lo z k r ts : V}
    (h : FormulaCovered b f lo z (qqNRel k r ts)) :
    ∃ y, AtomTranslation y k r ts b f lo z := by
  obtain ⟨hr,ht⟩ := IsSemiformula.nrel.mp h.2.1
  obtain ⟨hk,htags⟩ := source_relations _ _ |>.mp hr
  subst k
  apply (atom_exists_iff _ _ _ _ _ _ _).mpr
  refine ⟨rfl,ht.lh,h.1.1,?_,?_,htags⟩
  · apply term_covered_of_code_bound (ht.nth (by simp))
    exact le_trans (nth_lt_qqNRel_of_lt (by rw [ht.lh]; simp)).le h.2.2
  · apply term_covered_of_code_bound (ht.nth (by simp))
    exact le_trans (nth_lt_qqNRel_of_lt (by rw [ht.lh]; simp)).le h.2.2

#print axioms coverage_graph
#print axioms term_covered_of_code_bound
#print axioms coverage_all
#print axioms coverage_exs
#print axioms coverage_and
#print axioms coverage_or
#print axioms coverage_rel_atom
#print axioms coverage_nrel_atom
end M6.PA.RelationalSource.Numeric

