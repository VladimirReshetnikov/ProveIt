# A bounded shared-intermediate search for the 13-variable circuits

The [independent review](../../reviews/frontier13-shared-gate-screen-independent-audit/README.md)
reproduced the bounded search, exact identities and liveness checks. Its
search-family and fixed-port exclusions remain essential.

The search found no new operation-count improvement. In each original graph it
found two exact two-target forms of the already known [G linearization](../adaptive-g-linearized-product-tradeoff/README.md).
They keep 87/86 total operations while reducing the multiplication count by
one. After applying the already documented G linearization to each graph, the
screen found no further improvement in the specific family below. This is not
a global minimum or a new smaller consistency equation.

The bounded family selects two distinct original target rows, with the first
earlier than the second. Each target remains one binary `+`, `-` or `*` gate,
and both must use a shared value `t`. That value is either an earlier node or
literal, or the result of **one** new binary gate whose inputs are available
before the first target. Each target's other input may be an earlier node or a
literal `0, 1, 2, 3, 4`; it may instead use `t` twice. Both subtraction orders
are included. All other original rows and the output remain unchanged. A
candidate must preserve **each target polynomial** for all four symbolic
ports. Dead gates are pruned from the output graph, and an improvement means
fewer live binary gates, or the same number of gates with fewer multiplications.

`screen.py` evaluates every graph on three deterministic tuples modulo
`2305843009213693951`, enumerates the declared shared-gate shapes whose
signatures match both targets, and recounts the complete live DAG. An exact
integer-polynomial identity must agree at every sample, so finite-field
mismatch is a sound rejection within this family. Product lookup fails closed
on a zero or non-invertible nonliteral divisor; multiplication by literal zero
cannot match because every target's sampled vector is checked nonzero.
`t+t` and `t*t` are explicitly included; `t-t` is zero and cannot match.
Sample matches are not by themselves accepted as identities.

There are exactly two sampled improvements in each original graph. The script
independently checks the required rows and proves the following local
identities exactly in `Z[q,F,alpha]`, using `q = 1 + qm`, `qF = q-F` and
`C = qF-alpha`:

```text
t = q*qF;       g28 = q²-t;     G = t-C
t = q²-g28;     g44 = t-qF;     G = t-C
```

The first form preserves the original `g28=Fq` and `G=alpha+qF*qm`; the
second preserves the original `g44=qF*qm` and the same `G`. All later rows
therefore retain the same polynomials. The script checks that all 13 witnesses
and all four ports remain live in both resulting output circuits. Their exact
polynomials and existing degree certificates are unchanged.

This family is deliberately narrow. It excludes replacing either target by a
zero-cost direct alias, replacements that do not use the shared value in both
target rows, more than one new shared gate, changing other rows, alternative
positive-witness encodings, fixed-port-only identities, zero-set equivalences
without target polynomial identities, and constants outside the stated set.
It does not optimize variable liveness beyond checking the two reported
representations, prove minimality, or provide a new Lean theorem. Earlier
nodes with equal sampled signatures are all retained rather than merged.

Three positive controls check a genuine strict shared-gate reduction, reuse of
an existing shared alias, and the case where both targets use `t` twice.
`run.py` records the actual normal and optimized-mode rejection exits and
refuses to overwrite `receipt.json`. Run `python3 screen.py` for a read-only
rerun, or `run.py` in a copy without the recorded receipt.
