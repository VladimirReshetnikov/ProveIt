# Integration map

## Proposed destination

`Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/IPRADerivations/Foundations/TAPIR/`

## Upstream imports

| New module | Upstream imports |
|---|---|
| `Kernel.lean` | `ConciseIPRA.PR` |
| `Schedule.lean` | `IPRADerivations.Foundations.TAPIR.Kernel` |
| `Certificates.lean` | `IPRADerivations.Foundations.TAPIR.Kernel`, `Foundations.BoundedReflection` |
| `SearchK.lean` | `Core.Search` (initial comparison), `Core.Definitions`, arithmetic/order/sign modules |
| `Reflection.lean` | `IPRADerivations.Foundations.TAPIR.SearchK`, `Foundations.BoundedReflection` |
| `Trace.lean` | `IPRADerivations.Foundations.TAPIR.Kernel`, `Core.Definitions`, `Foundations.Termination` |
| `Examples.lean` | all preceding TAPIR modules |

## Suggested first client

Choose a small existing packet with one bounded certificate, one local witness,
and at most one explicit residual producer.  The migration should end in a
declaration of the form:

```lean
([] : List (Fm PTm 0)) ⊢[PRAAx] phi
```

or, while a producer remains open:

```lean
[B] ⊢[PRAAx] phi
```

## Compatibility strategy

Do not replace `Search.mu` or the existing one-parameter bounded-reflection API
initially.  Add generic-arity modules and prove specialization/compatibility
lemmas.  Migrate clients only after the new modules compile and the old build
remains green.
