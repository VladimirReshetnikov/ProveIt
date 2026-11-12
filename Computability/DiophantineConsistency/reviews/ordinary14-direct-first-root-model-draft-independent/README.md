# Independent source review: generic direct first-root bridge

**Source review passes; not elaborated.** The proposed file states generic
fact-level lemmas, not an equation, iPRA or PDF theorem. Its four residual
parameters are explicitly fixed independently of the selected coordinate.

The imported `P72Root.ι_magnitude_sq` has the needed equality between the
embedded natural magnitude and the square of a difference. The difference
ring supplies an injective natural embedding and no zero divisors; a positive
scale can therefore be cancelled without assuming an orientation for that
difference. The positive radicand makes the resulting natural square root
positive. In the reverse direction the choice `P+tau` is positive and realizes
the negative square-root branch. The five-square extraction follows the
existing ordered-difference-ring source pattern.

The independent checker pins the source and referenced theorem providers,
checks these declarations and explicit hypotheses, replays the author's
inventory and its receipt, and exercises finite square extraction and root
maps, including a zero-scale counterexample to cancellation. Its finite
controls do not establish the proposed universal lemmas. Lean was not invoked:
parsing, typeclass synthesis, tactic elaboration, axiom reports, provider
closure, and the arbitrary-model graph client remain unverified. In
particular, no conclusion here asserts that the four other graph residuals
are independent of the changing input, or that either graph or the iPRA
endpoint has been connected.

From `Computability/DiophantineConsistency`, run:

```
python3 -I -S -B reviews/ordinary14-direct-first-root-model-draft-independent/check.py
```

The output should match `result.json` byte-for-byte.
