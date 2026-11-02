# Reduced denominator integrality in IΣ₁ models

`ReducedNormInduction.reduced_denominator_one` proves the unbounded
**reduced-denominator lemma** in every model of `IΣ₁`. For model naturals
`r,v,a,b`, its exact hypotheses are

```
r > 0,  b > 0,  Bez a b 1,
(r+1)(vb)² = r a² + b².
```

Its conclusion is `b=1`. `Bez` is the repository's supplied four-natural
signed-coefficient certificate. The theorem works with arbitrary model
values, including nonstandard ones; it is not an induction argument over an
external standard-natural witness. It assumes neither a graph, a strong
norm nor a prior bound on `v`.

The proof fixes `r,b` and defines

```
P(k) := ∃ x, Bez x b 1 ∧ (r+1)(kb)² = r x²+b².
```

Lean's `definability` tactic proves this exact predicate is `Σ₁` after
unfolding `Bez`. `InductionOnHierarchy.least_number 𝚺 1` is then applied
to a least model index satisfying `P`. The zero index is impossible because
`b²>0`; when the index is one, cancellation gives `a²=b²`, hence `a=b`,
and the certificate gives `b | 1`. Otherwise the preceding
[simultaneous-state theorem](../reduced-model-state-prototype/README.md)
constructs a strictly smaller index with the same predicate, contradicting
minimality. The proof does not perform least-number induction on an
unbounded universal predicate or assume the theorem it proves.

This is a **model-level Lean theorem**, not a literal proof in `IΣ₁`, a
Lean certificate that a corresponding theorem is provable in iPRA, or an
end-to-end equation/consistency equivalence. In particular, it assumes a
reduced natural fraction and a Bézout certificate. The remaining work must
normalize the actual signed numerator and nonzero denominator in the model,
bind the graph's cleared norm to these hypotheses, derive the ordinary
strong norm, and separately construct the object-level iPRA proof or a
justified proof-producing bridge. Classical Lean metatheory appears in its
axiom report and should not be confused with object-theory axioms.

## Paired current-provider evidence

The [replay](replay.py) pins the independently audited
[smaller-state parent](../../../reviews/ordinary12-reduced-model-state-independent-audit/CHECK.json),
its two matched seed objects, the prior reduced-norm and square-divisor
parents, the matched 70-source current provider and reviewed sampled
monitor. It compiles this source separately over author and peer overlays,
checks exact direct imports and axiom reports, and compares source/object
hashes and parent states. RSS/free-space sampling is not a hard quota or
whole-process-tree accounting; package-transitive and dynamic provider
ancestry remain inherited.

Actual wrapper session `54640` exited `0` and printed receipt SHA
`298e528a7c814b129ff41e4551f5b18768d52c500bfff86322f430ad4af82199`.
The [receipt](evidence/receipt.json) records both compiler and dependency
check exits as `0`, matching object hashes, direct imports and sampled peak
RSS. Both [author](evidence/author.log) and [peer](evidence/peer.log) logs
report only `propext`, `Classical.choice`, and `Quot.sound`, without warnings
or `sorryAx`. This paired suffix has not yet received an independent audit.

The retained [failed attempt](observations/attempt01-terminal.json) was
session `6714`, actual exit `1`, on ambiguous `lt_irrefl` references and an
already-closed tactic; its source is preserved and its reports contained
`sorryAx`. Exploratory session `95482` then actually exited `0` without
warnings; the paired replay above is the evidence for the present source.

When the pinned temporary provider and suffix artifacts remain available,
and after coordinating other Lean processes, reproduce with

```
python3 -I -S replay.py --output /tmp/ipra-reduced-model-induction-new
```
