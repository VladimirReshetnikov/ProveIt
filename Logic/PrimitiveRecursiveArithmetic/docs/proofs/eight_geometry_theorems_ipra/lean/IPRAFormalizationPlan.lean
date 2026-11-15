import ConciseIPRA.BiInterpretation

/-!
# Repository-facing completion plan

Place the eventual modules beside this file in a new Lean library, or copy the
finished arithmetic layer under
`Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/`.

Planned dependency graph:

* `GeometryCodes`:
  integer, rational, tuple, matrix, and list codes; primitive-recursive graph
  theorems for all operations.
* `GeometryPolynomial`:
  sparse polynomial syntax, normalization, evaluation correctness, and a
  compiler from equality certificates to `PRAAx` derivations.
* `GeometryProjective`:
  coded point/line predicates, dot/cross/determinant operations, incidence,
  bounded minor search, and explicit matrix inversion.
* `GeometryTheorems`:
  exact `Fm PTm n` statements and `PRAAx` proofs for all eight theorems.
* `GeometryTransfer`:
  applications of `pra_theorem_iff` followed, optionally, by existing native
  calculus equivalences.

No theorem below is postulated: the only executable declarations in this file
are checks that the required bridge names are available from the current
`ConciseIPRA` import.
-/

namespace LeanProofs.ConciseIPRA.GeometryPlan

open LeanProofs.ConciseIPRA

#check pra_iff_teq
#check pra_theorem_iff
#check teq_roundTrip
#check pra_roundTrip

/-!
For a completed arithmetic theorem

```
h : [] ⊢[PRAAx] phi
```

the transported theorem is obtained by

```
exact (pra_theorem_iff phi).mp h
```

and has target

```
[] ⊢[TeqAx] phi.map (fun _ => FromPRA.sigma)
```

The eight `phi` formulas must expose all code well-formedness and apartness
hypotheses.  Existential conclusions use the explicit witnesses from the
report; Carnot polygon additionally uses quantifier-free induction on the
root and side lists.
-/

end LeanProofs.ConciseIPRA.GeometryPlan
