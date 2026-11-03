# General guard obstruction for the nonnegative gauge

`Mask79GuardObstruction.moved_guard_iff` proves in every supported IΣ₁ model, for arbitrary natural ports and valuations with `F>0`, that

```text
(F+b*t) + (C−q*b*t) < q    iff    t=0 and F+C<q,
```

where `b=beta*J`, `q=b+1`, `t` is a model-natural value, and subtraction is the model's natural truncated subtraction. In particular the actual moved guard forces `t=0`; the additional strict C-positivity bound is not needed for this obstruction. If `t` is nonzero, discreteness gives `t≥1`, hence `F+b*t≥1+b=q`, while the second moved summand is nonnegative.

Thus the checked [nonnegative-parameter gauge](../ten-positive-79-gauge-actual-output/README.md) cannot turn an unguarded positive valuation into a guarded one. This supersedes the narrower [small-C obstruction](../ten-positive-79-gauge-actual-obstruction/README.md). It does not decide whether an unguarded positive 79 graph zero exists, rule out a different transformation (including one with different parameterization), or prove/disprove unrestricted 79/80 equivalence or an iPRA endpoint.

Guarded author `observations/attempt01/` and its enclosing tool session exited 0. Source SHA-256 is `228839f8d74ee7cdd5538644fbf824784ae754232eda14a6f5d091a0dc097fbc`; terminal SHA-256 is `c25366a6bf76585bfc62f6f6e7c60dd5dc24682ae5f1d32c8b2af4040934e8d1`; output `/tmp/mask79-guardobstruction-1k1ive27/Mask79GuardObstruction.olean` has SHA-256 `d0cbf2d2fd8666d9efeaeedd5de95ec62d5e48f803f174be53f674b7ede2ca24`. The direct natural-lift object and selected predecessor objects are pinned; full historical transitive project, package and dynamic ancestry remain inherited. No independent Lean replay or external file semantics is claimed.
