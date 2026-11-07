# 32-witness sextic by eliminating the q² cut

This is a **source-only external candidate**, separate from the checked 33-witness quartic seed and its symbolic iPRA endpoint. It substitutes the first positive cut

```text
q² = (beta · (x₁ + 1) + 1)²
```

into every other residual, then drops that cut's coordinate and its defining residual. Original full coordinates 0–14 remain unchanged; original coordinate 15 is reconstructed by the displayed natural square; original 16–33 become new 15–32. The distinguished input remains coordinate 0 and is unused. The resulting `seed.json` has **32 natural witness coordinates and 23 residuals**, with the same fixed port-byte binding as the audited 33 candidate. The new seed is their sum of squares.

## External degree and normalization argument

The structural checker verifies maximum syntactic residual degree 3, attained only by `q3`, `tau` and `cTminusR`, so the seed has degree at most 6. At all-zero witnesses its first residual is `−(beta+1)^3`, independent of the distinguished input. The fixed current beta is positive, so that residual and its square are nonzero; normalization follows over the integers.

There is also an exact-degree argument over the fixed integer ports: set every witness except `x₁` to zero. The coefficient of `x₁³` in the retained `q3` residual is `−beta³`; each other residual has degree at most 3. Consequently, the coefficient of `x₁⁶` in the sum of their squares is a sum of squares of integer coefficients and is at least `beta⁶ > 0`. Thus the candidate polynomial has degree exactly 6, provided the audited AST denotes the intended seed. This is a mathematical argument pending independent review, not a Lean degree theorem.

## Reconstruction obligations

For the **32→33** direction, take arbitrary natural values for the new coordinates, insert the natural square above as old coordinate 15, and shift the remaining coordinates back. The dropped q² residual is zero and each other old residual is the corresponding new residual. Zero of a finite sum of squares implies every residual vanishes in the intended ordered difference-ring model, so the lifted 33 seed is zero.

For the **33→32** direction, zero of the old sum of squares gives every residual zero; the q² residual identifies the embedded old coordinate 15 with the embedded natural square. Injectivity of the natural-model embedding recovers the needed natural-coordinate equality. Drop old coordinate 15 and use the same substitution identities to obtain zero of the 32 seed. These all-model sum-of-squares, cast, injection, lift and projection steps still need Lean proofs; the 16 numerical controls in `check.py` are not such proofs. The old 33 proof and endpoint are untouched.

The checked `NineFreshJones.nine_iff`, `ExecutableJones.hasNaturalZero_expression`, and upstream `Jones1982.Nine.wset_iff_nine` all require degree at most 4 and cannot be applied directly to this degree-6 seed. Upstream `Jones1982.diophantine_quartic58` accepts arbitrary Diophantine-set representations over standard naturals and returns an existential 58-witness quartic for positive inputs, but it does not preserve 32 witnesses, give these explicit coefficients, or supply the required all-IΣ₁-model/iPRA transfer. No 32-witness Jones expression or endpoint is claimed.

## Reproducible evidence

Author no-Lean build/check commands exited 0. `build.py --check` reproduces the exact seed AST; `check.py` independently replays every substitution/index map, verifies the degree and first-residual coefficient facts, and checks 16 finite integer assignments. The scripts do not prove all-model semantics. Pins: builder `046c6f4ced5c677cce7b1af6ba8dca194f459abad1b5719fff451ed62c13b8be`, checker `c6b5b5415d66f5ee3e14ed980880d34c394edf1fe4f9f78404c998bd6988b063`, seed `f26172a2cad6e6a8fda042c67821f2fa7651426a62e980173eb5fac07cd835ab`, result `713122ce49cee5d820ba7362a74f3ec3175bc947644e4939c9ac102ca1e123ce`. The original v1 copied a graph-relative coefficient path into the candidate directory, where it did not resolve; v1 is preserved. This v2 explicitly points to the original graph-owned `coefficients/` directory and verifies all four compressed and raw file hashes, lengths and positive bit lengths. The `MF_source.bin.gz` file is the source high mask; the current Lean model port is high+beta exactly once, and byte matching alone is not a model-port proof. Independent source/mathematics review is required.

The [independent v2 audit](../../reviews/nine-sharing-sign32-sextic-frontier-independent/) passed, including all transformed residuals, fixed-port bytes and the exact-degree-six argument. It does not establish either all-model bridge direction, a degree-six Jones theorem or an endpoint.
