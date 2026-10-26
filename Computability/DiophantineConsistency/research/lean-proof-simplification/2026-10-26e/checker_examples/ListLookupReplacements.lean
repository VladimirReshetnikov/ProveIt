import Init.Data.List.Lemmas
import Init.Data.Option.Function

/-!
These two statements use only pinned Lean v4.32.0 library APIs, not project-
specific logic. At creation they were source-verified but not elaborated.

Delete the repeated private helper declarations and call the standard lemmas
at their sites, or retain one-line private aliases while migrating.
-/
namespace CheckerRefactor

example {α : Type} {xs : List α} {i : Nat} {a : α}
    (h : xs[i]? = some a) : a ∈ xs :=
  List.mem_of_getElem? h

example {α : Type} (xs : List α) (a : α) (h : a ∈ xs) :
    ∃ i : Nat, xs[i]? = some a :=
  List.mem_iff_getElem?.mp h

example {α β : Type} {f : α → β} (hf : Function.Injective f) :
    Function.Injective (Option.map f) :=
  Option.map_injective hf

end CheckerRefactor
