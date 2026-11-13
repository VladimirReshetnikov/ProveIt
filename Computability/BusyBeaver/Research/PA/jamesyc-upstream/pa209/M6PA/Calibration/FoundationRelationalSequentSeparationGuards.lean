module
public import M6PA.Theory
public import M6PA.Calibration.FoundationRelationalSequentSeparationCode
@[expose] public section

/-! Exact three-binder source separation coverage and requested output
freshness, derived from the whole-schema guard and finite environments. -/
namespace M6.PA.RelationalSource.Numeric
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem separation_property_coverage {p f lo z : V}
    (hc : FormulaCovered 0 f lo z (sourceSeparation p)) (hp : IsSemiformula language 1 p) :
    FormulaCovered ((lo+1+1)∷0) f (lo+1+1+1) z p := by
  have hb := coverage_all (coverage_exs (coverage_all hc))
  have hh := (coverage_and (coverage_or (coverage_and hb).1).2).2
  refine ⟨⟨?_,hh.1.2⟩,?_,hh.2.2⟩
  · refine ⟨hh.1.1.1,hh.1.1.2.1,?_,hh.1.1.2.2.2⟩
    intro i hi
    have he : i=0 := by simpa using hi
    subst i
    simpa using lt_add_one (lo+1+1)
  · simpa using hp

theorem separation_output_fresh {p f lo z : V}
    (hc : FormulaCovered 0 f lo z (sourceSeparation p)) (hp : IsSemiformula language 1 p) :
    FreshEnvironment (lo+1) ((lo+1+1)∷0) f (lo+1+1+1) z := by
  have hprop := separation_property_coverage hc hp
  have hcd : lo+1<lo+1+1 := lt_add_one _
  have hdL : lo+1+1<lo+1+1+1 := lt_add_one _
  refine ⟨lt_trans hcd hdL,ne_of_lt (lt_of_lt_of_le (lt_trans hcd hdL) hprop.1.1.2.1),?_,?_⟩
  · intro i hi
    have he : i=0 := by simpa using hi
    subst i
    simpa using ne_of_lt hcd
  · intro i hi
    exact Ne.symm (ne_of_lt (lt_trans (hc.1.1.2.2.2 i hi) (lt_add_one lo)))

theorem separation_label_bounds {p f lo z : V}
    (hc : FormulaCovered 0 f lo z (sourceSeparation p)) (hp : IsSemiformula language 1 p) :
    lo<z ∧ lo+1+1<z ∧ lo+1≠lo ∧ lo+1≠lo+1+1 := by
  have hprop := separation_property_coverage hc hp
  have hd : lo+1+1<z := lt_of_lt_of_le (lt_add_one _) hprop.1.1.2.1
  exact ⟨lt_trans (lt_trans (lt_add_one lo) (lt_add_one (lo+1))) hd,hd,
    Ne.symm (ne_of_lt (lt_add_one lo)),ne_of_lt (lt_add_one (lo+1))⟩

#print axioms separation_property_coverage
#print axioms separation_output_fresh
#print axioms separation_label_bounds
end M6.PA.RelationalSource.Numeric
