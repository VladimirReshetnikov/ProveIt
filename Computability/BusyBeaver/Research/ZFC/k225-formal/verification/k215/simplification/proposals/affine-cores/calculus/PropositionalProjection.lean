import BusyBeaver.ZFC.Kalmar

/- Uncompiled proposal. A finite propositional schema, not a new logical axiom.
   The carrier and implication need not be injective or free of aliases. -/
namespace SetTheory.BusyBeaver.ZFC.PropositionalProjection
open Kalmar
universe u

theorem not_imp_left {A : Type u} {imp : A → A → A} {bot : A} {T : A → Prop}
    (hC : Kalmar.Classical imp bot T) (a b : A) :
    T (imp (imp (imp a b) bot) a) := by
  let f : PF := .imp (.imp (.imp (.var 0) (.var 1)) .bot) (.var 0)
  have ht : PF.Tautology f := by
    intro v
    cases h0 : v 0 <;> cases h1 : v 1 <;>
      simp [f, PF.truth, h0, h1]
  have h := tautology_complete hC f 2 (by simp [f, PF.Bounded]) ht
    (fun n => if n = 0 then a else b)
  simpa [f, PF.eval] using h

end SetTheory.BusyBeaver.ZFC.PropositionalProjection
