import IPRADerivations.Core.Order
import IPRADerivations.Core.Search
import SCOPE.StructuralKernel

/-!
# Certificate observers and escape analysis: implementation blueprint

Four constructive observer interfaces should be formalized.

1. Exact stability: every two valid certificates have equal observations.
2. Quotient stability: observations are equal in an explicit, witnessed
   congruence relation.
3. Metric stability: every two observations are within an explicit rational
   diameter at the requested precision.
4. Gap stability: an approximate label is separated from every competing label
   by a supplied positive margin, allowing a unique exact branch to be named.

The public theorem must not mention the private certificate.  The structural
kernel then seals it by `Prf.exE`.  A canonical certificate is selected only if
its code itself, rather than an invariant observation, belongs in the public
conclusion.

Suggested target structures:

```
structure ExactObserver ...
structure QuotientObserver ...
structure MetricObserver ...
structure GapObserver ...

theorem eliminate_exact ...
theorem eliminate_quotient ...
theorem eliminate_metric ...
theorem stabilize_under_gap ...
theorem spanning_tree_descent ...
```

For `spanning_tree_descent`, orient a supplied finite spanning tree toward its
root.  Exact edge compatibility composes by equality transitivity.  Metric edge
bounds compose by the triangle inequality, and the final error is the explicit
sum along the root path.  This gives the finite observation needed by a
consumer without constructing a global infinitary quotient or a global choice
of representatives.
-/

namespace LeanProofs.IPRA.SCOPE.Observers
end LeanProofs.IPRA.SCOPE.Observers
