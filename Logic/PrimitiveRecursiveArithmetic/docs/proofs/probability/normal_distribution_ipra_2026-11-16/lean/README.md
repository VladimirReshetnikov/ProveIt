# Lean formalization blueprint

These files are a concrete roadmap, not a completed formalization.

- `FiniteGaussianBlueprint.lean` gives proposed executable data structures and finite recurrences for intervals, moments, Hermite polynomials, and certificate checkers. It is intentionally self-contained at the design level.
- `ObjectLanguageTargets.lean` records the exact ProveIt imports, namespaces, target theorem shapes, and the ordinary-to-native endpoint.
- `ROADMAP.md` gives the dependency graph, proof obligations, induction invariants, and milestone order.

The target ProveIt snapshot is `8f028dcb4be7a7397d0c11d7c467aa1170cbf2f3`. Relevant checked interfaces at that snapshot are:

```lean
import ConciseIPRA.PR
import ConciseIPRA.NativeBiInterpretation

namespace LeanProofs.ConciseIPRA
-- PR, PTm, PRAAx, Prf, PRA.qfInd
-- pra_iff_native
end LeanProofs.ConciseIPRA
```

A finished headline theorem must be an actual derivation, for example

```lean
 theorem gaussianMomentSentence :
   ([] : List (Fm PTm 0)) ⊢[PRAAx] momentSentence := by
   ...
```

and not merely an ambient theorem over `Real` or a Boolean test in the metatheory.
