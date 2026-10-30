# One-gate factorization of the adaptive thirteen-variable output

This is an output-only candidate, not an accepted replacement for the maintained equation. The pinned parent has 13 witnesses, four coefficient ports and 88 live binary operations. Factoring its first-root expression gives a candidate with the **same complete integer polynomial** and 87 live operations: 47 multiplications, 22 additions and 18 subtractions. Its 13 witnesses and four ports all remain live. The parent's reported degree is inherited by polynomial identity; this packet does not independently certify that degree or claim minimality.

Write the parent's existing intermediate values as

```text
M = q3*qm,  W = 1+k*qm,
Z = M*g31+Y*qm-Bt*(W*q3).
```

The candidate changes only the root-computing block:

```text
Z = M*(g31-k*Bt)+Y*qm-Bt*q3.
```

The difference is identically zero over a commutative ring. The previous root block uses eight gates including the two `W` gates and `Y*qm`; the replacement uses seven. `M` is retained because the first norm also uses `M*M`. The old `W` cut is no longer produced. Consequently this is an optimization of the equation **output**, not a replacement for the existing `NativeAdaptiveGraph.core` record interface, which exposes `W`.

The [stdlib-only finite audit](audit.py) checks the exact parent JSON pin, the actual 88-row schedules in both `AdaptiveEquationSyntax2011` and `NativeAdaptiveGraph`, topology and complete output liveness, the exact local sparse-polynomial identity evaluated from the parent and candidate gates, the unchanged surrounding rows, and a deliberately altered sign. It passes under normal Python and `python -O`. The generated [candidate DAG](candidate.json) uses the same witness and port names; its coefficient metadata is deliberately not substituted into the maintained current2011 binding.

The [generic Lean lemma](../../Lean/DiophantineConsistency/AdaptiveFirstRootFactor87.lean) proves that the two root forms have exactly equal formal signed pairs for arbitrary signed inputs over every commutative semiring. Its arbitrary-context corollary makes no positivity assumption on `Bt`. This is stronger locally than an integer-only calculation and applies to nonstandard semiring models. The [syntax-level lemma](../../Lean/DiophantineConsistency/AdaptiveFirstRootFactor87Syntax.lean) compiled against the repository's `Expr.splitNatural` evaluator and proves equality of the local split values in every commutative semiring, including under any later contextual zero test. Neither local lemma by itself binds the complete new 87-row DAG to the maintained 88-row expression in Lean, proves an HA derivation, or changes the inherited consistency calibration. Those bindings and independent review are required before adopting the candidate.

## Literal binding update

The [independently replayed literal theorem](../../reviews/adaptive-first-root-factor87-literal-independent.md)
now identifies both complete expressions as substitutions into the same
actual one-hole context. It proves their split values equal for arbitrary
ports and their positive-shifted internal-zero tests equivalent at the
maintained ports, over every commutative semiring. The count is for the
unshifted output DAG and excludes the shift. This transfers the parent
equation's zero set, but it does not itself prove an HA or PRA consistency
equivalence for the 13-variable equation. Earlier statements in this proposal
about the literal binding being absent describe the prior checkpoint.

## Further screening

The bounded one- and two-operation modular-signature scans, their saved outputs,
and their important exclusions are recorded in [SCREENING.md](SCREENING.md).
They found no candidate in the screened subset and do not prove minimality.
