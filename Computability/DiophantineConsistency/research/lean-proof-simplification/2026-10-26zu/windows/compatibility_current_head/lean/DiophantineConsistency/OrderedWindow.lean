import Mathlib.Order.Monotone.Basic

/-! # Recovering an index from a monotone half-open window

The index order need not be well founded. The boundary map need not be
strictly monotone; the nonempty windows supply the required separation.
-/
namespace DiophantineConsistency.OrderedWindow

variable {I C : Type*} [LinearOrder I] [Preorder C]

theorem index_unique (succ : I → I)
    (step_le : ∀ {a b : I}, a < b → succ a ≤ b)
    (base : I → C) (mono : Monotone base)
    {a b : I} {x : C}
    (ha : base a ≤ x) (ha' : x < base (succ a))
    (hb : base b ≤ x) (hb' : x < base (succ b)) : a = b := by
  apply le_antisymm
  · exact le_of_not_gt (fun h => (not_lt_of_ge ha) (hb'.trans_le (mono (step_le h))))
  · exact le_of_not_gt (fun h => (not_lt_of_ge hb) (ha'.trans_le (mono (step_le h))))

end DiophantineConsistency.OrderedWindow
