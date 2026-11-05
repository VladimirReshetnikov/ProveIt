# Checked 76Y strict-root evaluator

`IndependentYStrictDraft.lean` defines ring-level names for `c`, `a`, rank,
`c*T−R` and `Delta`, and proves the
decomposition of the signed `oldV`, and a direct evaluator equality for
`Na = A*(V²−y²)+y²`. Its `actual_strict` declaration establishes
the new-zero witness guard

```
P64QCube76YBinding.oldV ports castWitness < ι (v 12)
```

for every positive 76Y zero in the indicated IΣ₁ model. It combines the
checked graph residual split (`Na=1`), actual-zero size bound `f²>c+1`,
positive `y`, and generic auxiliary strictness lemma.

Sequential verification needs the generated 76Y graph, the 77 unit helper,
the [ring binding](../fourteen-p64-qcube76-independent-y-binding-draft/README.md),
and the checked bounds, graph and size sources in the
[independent-y lemma packet](../p64-qcube76-independent-y-lemmas-draft/README.md).
The [bounded guarded check](../p64-qcube76y-strict-guarded-check/README.md)
passed with no warnings or `sorryAx`. The mathematical argument and its
limits are stated in the [analysis](../p64-qcube76-independent-y-analysis/README.md).
The witness-map composition, positive-zero equivalence and iPRA endpoint
remain separate. Captured-provider transitive ancestry remains inherited.

Source SHA-256:
`c959e856d4554e735c57ef91f9255633a5ff899639f0222a2e8a11a02e61ad2a`.
