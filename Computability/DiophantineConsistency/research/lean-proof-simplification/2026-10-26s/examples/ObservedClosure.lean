import ZF.Zf

/-! Closure of internally represented certificates under union and adjoining
one justified observation. Unobserved members of the model's set are allowed. -/
namespace ObservedClosure
open SetTheory
universe u v
variable {V : Type u} {I : Type v} {mem : V → V → Prop}

structure Rules (mem : V → V → Prop) (I : Type v) where
  encode : I → V
  step : V → I → Prop
  mono : ∀ {S T}, Sub mem S T → ∀ i, step S i → step T i

namespace Rules
variable (R : Rules mem I)

def Closed (S : V) : Prop := ∀ i, mem (R.encode i) S → R.step S i

theorem empty (H : ZFAxioms mem) : R.Closed (vempty H) :=
  fun _ hi => False.elim (vempty_spec H _ hi)

theorem cup (H : ZFAxioms mem) {S T : V}
    (hS : R.Closed S) (hT : R.Closed T) : R.Closed (vcup H S T) := by
  intro i hi
  rcases (vcup_spec H S T _).mp hi with hi | hi
  · exact R.mono (fun x hx => (vcup_spec H S T x).mpr (Or.inl hx)) i (hS i hi)
  · exact R.mono (fun x hx => (vcup_spec H S T x).mpr (Or.inr hx)) i (hT i hi)

theorem insert (H : ZFAxioms mem) (hinj : Function.Injective R.encode)
    {S : V} {i : I} (hS : R.Closed S) (hi : R.step S i) :
    R.Closed (vcup H S (vsingle H (R.encode i))) := by
  have hg : Sub mem S (vcup H S (vsingle H (R.encode i))) :=
    fun x hx => (vcup_spec H _ _ x).mpr (Or.inl hx)
  intro j hj
  rcases (vcup_spec H _ _ _).mp hj with hj | hj
  · exact R.mono hg j (hS j hj)
  · have hji : j = i := hinj ((vsingle_spec H _ _).mp hj)
    subst j
    exact R.mono hg i hi

end Rules
end ObservedClosure
