# Incremented mask for the concrete symbolic recipe

In every IΣ₁ model, let `mask` be the cast of the concrete finite-list mask
constructed in `compact44-concrete-mask-prototype`. The source proves that this
mask equals the cast of the unexpanded bit-exponent recipe. For positive N and
C ≥ 1, it applies the mixed-increment decoder to the explicit assumption

```
NoCarry (C − 1) (mask * rep(67 * 8807, N) + 1).
```

The conclusion is that the origin digit of C is 1 and all of its first 8807N
radix-2^67 digits are at most 3. The concrete support's size, digit classes and
origin are supplied by the separately audited concrete-mask theorem.

The model mask here is a symbolic recipe. Equality to the retained MC payload,
its binding to the actual graph port, and derivation of the NoCarry premise
are not established. Nor does this prove coefficient bounds, carry reset,
machine simulation, or a PRA proof.

The historical 24-module window provider and 342-module endpoint successor
share six different object hashes; this packet does not combine their objects.
Instead, it rebuilds the three small mixed-mask modules from their exact audited
sources against each corresponding endpoint successor, and composes them with
that same successor's concrete-mask branch. The exploratory author-side chain
session 2299 exited 0 for all four compilers, without warnings. The paired
replay, source pins, direct imports and provider audit are recorded separately.

The initial paired-wrapper session 48498 exited 1 before creating its output or
launching Lean: its schema check expected `author_receipt_sha256` for an audit
that records `receipt_sha256`. The corrected driver explicitly selects the key
for each audit, checks the pinned digest, and rejects conflicting duplicate
keys. `schema_controls.py` checks both expected schemas, missing and conflicting
keys and wrong digests; its normal isolated run exited 0 and an isolated `-O`
run was rejected with exit 1. These synthetic controls do not authenticate any
external service or extend the resource-monitor guarantees.
