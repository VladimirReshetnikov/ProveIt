import DiophantineConsistency.PRALanguage
import Foundation.FirstOrder.Arithmetic.Basic.Hierarchy
set_option autoImplicit false
namespace DiophantineConsistency.ParsonsHierarchyMap
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage

theorem map_lt {ξ : Type} {n : ℕ} (t : Semiterm ℒₒᵣ ξ (n+1)) :
    Semiformula.lMap embedding (“#0 < !!t”) = (“#0 < !!(t.lMap embedding)”) := by
  simp [Semiformula.Operator.lt_def, Semiformula.lMap_rel, Matrix.fun_eq_vec_two,
    PRALanguage.embedding, Language.ORing.embedding]

theorem hierarchy {ξ : Type} {n : ℕ} {Γ : Polarity} {s : ℕ}
    {φ : Semiformula ℒₒᵣ ξ n} (h : Hierarchy Γ s φ) :
    Hierarchy Γ s (Semiformula.lMap embedding φ) := by
  induction h with
  | verum => simp
  | falsum => simp
  | rel r v => simp
  | nrel r v => simp
  | and h1 h2 ih1 ih2 => simpa using Hierarchy.and ih1 ih2
  | or h1 h2 ih1 ih2 => simpa using Hierarchy.or ih1 ih2
  | ball ht h ih =>
      have hpos := (Semiterm.lMap_positive (Φ := embedding) _).mpr ht
      have hr := Hierarchy.ball hpos ih
      simpa [Semiformula.lMap_ball, map_lt] using hr
  | bexs ht h ih =>
      have hpos := (Semiterm.lMap_positive (Φ := embedding) _).mpr ht
      have hr := Hierarchy.bexs hpos ih
      simpa [Semiformula.lMap_bexs, map_lt] using hr
  | exs h ih => simpa using Hierarchy.exs ih
  | all h ih => simpa using Hierarchy.all ih
  | sigma h ih => simpa using Hierarchy.sigma ih
  | pi h ih => simpa using Hierarchy.pi ih
  | dummy_sigma h ih => simpa using Hierarchy.dummy_sigma ih
  | dummy_pi h ih => simpa using Hierarchy.dummy_pi ih
end DiophantineConsistency.ParsonsHierarchyMap
