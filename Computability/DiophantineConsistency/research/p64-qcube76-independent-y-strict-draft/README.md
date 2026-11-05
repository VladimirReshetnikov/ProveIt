# Unchecked 76Y strict-root evaluator draft

`IndependentYStrictDraft.lean` is an **unchecked source draft**. It proposes
ring-level names for `c`, `a`, rank, `c*T−R` and `Delta`, the definitional
decomposition of the signed `oldV`, and a direct evaluator equality for
`Na = A*(V²−y²)+y²`. Its `actual_strict` declaration attempts to discharge
the new-zero witness guard

```
P64QCube76YBinding.oldV ports castWitness < ι (v 12)
```

for every positive 76Y zero in the indicated IΣ₁ model. It combines the
drafted graph residual split (`Na=1`), drafted actual-zero size bound
`f²>c+1`, positive `y`, and drafted generic auxiliary strictness lemma.

Sequential verification needs the generated 76Y graph, the 77 unit helper,
the [ring-binding draft](../fourteen-p64-qcube76-independent-y-binding-draft/README.md),
and the bounds, graph and size drafts in the
[independent-y lemma packet](../p64-qcube76-independent-y-lemmas-draft/README.md).
The mathematical argument and its limits are stated in the
[analysis](../p64-qcube76-independent-y-analysis/README.md). None of these
new 76Y files has been checked in Lean; this packet is not evidence of a
positive-zero equivalence or iPRA endpoint. In particular, simplifier and
coercion behavior, evaluator identities and the complete model composition
remain to be checked.

Source SHA-256:
`c959e856d4554e735c57ef91f9255633a5ff899639f0222a2e8a11a02e61ad2a`.
