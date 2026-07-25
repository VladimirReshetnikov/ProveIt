/-!
# Componentwise extensionality for small `Fin` tuples

The coded-syntax layers repeatedly prove `f = g` for substitution vectors
`f g : Fin n → α` (`n ≤ 5`) by `funext` followed by a nest of
`cases i using Fin.cases` whose leaves close by `rfl`.  `fin_cases` is not
available in this import closure, so these helpers name the componentwise
argument once; a call site passes one proof per component.
-/

namespace LeanProofs.BoundedPAConsistency

theorem funext_fin1 {α : Sort _} {f g : Fin 1 → α}
    (h0 : f 0 = g 0) : f = g := by
  funext i
  cases i using Fin.cases with
  | zero => exact h0
  | succ i => exact i.elim0

theorem funext_fin2 {α : Sort _} {f g : Fin 2 → α}
    (h0 : f 0 = g 0) (h1 : f 1 = g 1) : f = g := by
  funext i
  cases i using Fin.cases with
  | zero => exact h0
  | succ i =>
    cases i using Fin.cases with
    | zero => exact h1
    | succ i => exact i.elim0

theorem funext_fin3 {α : Sort _} {f g : Fin 3 → α}
    (h0 : f 0 = g 0) (h1 : f 1 = g 1) (h2 : f 2 = g 2) : f = g := by
  funext i
  cases i using Fin.cases with
  | zero => exact h0
  | succ i =>
    cases i using Fin.cases with
    | zero => exact h1
    | succ i =>
      cases i using Fin.cases with
      | zero => exact h2
      | succ i => exact i.elim0

theorem funext_fin4 {α : Sort _} {f g : Fin 4 → α}
    (h0 : f 0 = g 0) (h1 : f 1 = g 1) (h2 : f 2 = g 2)
    (h3 : f 3 = g 3) : f = g := by
  funext i
  cases i using Fin.cases with
  | zero => exact h0
  | succ i =>
    cases i using Fin.cases with
    | zero => exact h1
    | succ i =>
      cases i using Fin.cases with
      | zero => exact h2
      | succ i =>
        cases i using Fin.cases with
        | zero => exact h3
        | succ i => exact i.elim0

theorem funext_fin5 {α : Sort _} {f g : Fin 5 → α}
    (h0 : f 0 = g 0) (h1 : f 1 = g 1) (h2 : f 2 = g 2)
    (h3 : f 3 = g 3) (h4 : f 4 = g 4) : f = g := by
  funext i
  cases i using Fin.cases with
  | zero => exact h0
  | succ i =>
    cases i using Fin.cases with
    | zero => exact h1
    | succ i =>
      cases i using Fin.cases with
      | zero => exact h2
      | succ i =>
        cases i using Fin.cases with
        | zero => exact h3
        | succ i =>
          cases i using Fin.cases with
          | zero => exact h4
          | succ i => exact i.elim0

end LeanProofs.BoundedPAConsistency
