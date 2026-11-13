# Existing model Pell lower-bound source audit

The desired no-parity, one-step Pell descent proof is already present as the
source-only `AuxRootBoundsModelDraft.first_ordinate_large` in the pinned
[natural81 overlay](../ordinary14-natural81-combined-slim-overlay/source/AuxRootBounds.lean.src).
Its explicit hypotheses in a repository ordered IΣ₁ model are

```
0 < m,  2 < k,  tau*tau = 1 + m*(m+1)*k*k.
```

It proposes `8*m+4 ≤ k`. It sets `q=m−1`, uses the existing
`ArithmeticPellFirstNorm.descent` to obtain `u>0`, `v<k`, a smaller norm and
`k=2*u+(2*m+1)*v`, excludes `v=0` by `k>2`, invokes the existing
`two_le_ordinate` (a consecutive-square argument, not a parity hypothesis),
and compares squares to derive `u>m*v`. Thus `v≥2`, `u≥2m+1`, and the stated
bound follows. The intermediate truncated-subtraction identity is explicit.

The same overlay's source-only `FirstMainLargeKDraft.first_main_large_k` adds
positive `X,Y,eta,zeta` and a main natural norm to rule out `k=2`; it then
instantiates `m=X*Y*Y`. Its square-gap client explicitly assumes the main
natural norm and discriminant identity. That client imports `Compact44.P72Root`
for an embedding/subtraction lemma and has separate provider ancestry. Both
source files are **unelaborated proposals**, not kernel-checked results or
proofs that a zero of the compact 13-variable graph supplies their hypotheses.
In particular an `X=0` branch, signed-root quotient extraction, fixed-port
bounds and all parent/iPRA connections remain separate obligations.

The deterministic checker pins these exact existing sources and the repository
Pell source, checks the relevant theorem signatures and absence of a parity
premise, and performs only a bounded numerical sanity check. It does not run
Lean, validate tactics or authenticate any provider. Run from
`Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary13-gamma-pell-existing-source-audit/check.py | cmp - research/ordinary13-gamma-pell-existing-source-audit/receipt.json
```
