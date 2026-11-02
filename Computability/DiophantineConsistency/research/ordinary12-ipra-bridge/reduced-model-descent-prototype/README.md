# Reduced-norm descent: divisor, inequalities and signed numerator

This packet formalizes a noncircular part of the adjacent-coefficient
descent in arbitrary `IΣ₁` models. It is independent of the 12-variable
graph, its ports, a strong norm or any final rank. It does not yet prove the
unbounded integrality lemma or a derivation in iPRA.

For model naturals `r,v,a,b`, suppose

```
r > 0,  v > 1,  b > 0,
Bez a b 1,
(r+1)(vb)² = r a² + b².
```

`Bez` is the repository's four-natural signed-coefficient certificate.
`model_bounds` uses the independently audited `square_divisor_of_reduced_norm`
to produce `s` with `r=b²s`, and proves

```
vb < a,            r a < (r+1)vb.
```

The bounds are established in the model's ordered difference ring and
transported back to model naturals. The generic ring lemmas then use the
**supplied** `s` and define the signed transforms

```
v′ = (2r+1)v − 2bsa,
a′ = (2r+1)a − 2(r+1)vb.
```

They prove that the cleared norm is preserved, that `−v<v′<v` under the
above order hypotheses, and that a Bézout certificate transfers from `a`
to `a′`. The explicit coefficient update uses
`a′−a=b·[2bsa−2(r+1)v]`.

`bez_iff_diff` proves equivalence between the model's four-natural Bézout
certificate and a certificate in its difference ring.
`model_signed_numerator` combines the square-divisor witness with the
Bézout transform and returns a model natural `t` such that
`ι t=a′` or `ι t=−a′`, together with `Bez t b 1`. This latter theorem
requires the reduced norm and the original certificate; unlike the strict
bounds it does not require `r>0`, `v>1` or `b>0`. Its existential choice is
a model-level result, not a primitive-recursive term or an iPRA proof.

Still needed are a proof that the transformed `v′` is nonzero and its
natural absolute value is a smaller positive witness, simultaneous transport
of the reduced norm and certificate into that new natural state, the
appropriate `Σ₁` least-number or bounded primitive-recursive iteration, and
a graph-to-reduced-norm bridge. These steps must not assume the desired
strong norm. The model reasoning uses classical Lean metatheory; no object
proof in iPRA is constructed by this packet.

## Paired current-provider evidence

The [replay](replay.py) checks the independently audited paired
[square-divisor suffix](../model-square-divisor-prototype/README.md), its
matching objects, and the audited 70-source current provider before and
after rebuilding this one source separately over author and peer overlays.
It checks direct imports, axiom reports, source/object hashes and sibling
matching. It uses the previously reviewed sampled process monitor; the RSS
and free-space checks are samples, not hard quotas or full-tree resource
accounting, and its documented process-group limitations still apply.

Actual wrapper session `18589` exited `0` and printed receipt SHA
`2a3e44b6579798dd99557fcb050776fef12678479b24528b1f767b513e594742`.
The [receipt](evidence/receipt.json) records both compiler and dependency
check exits as `0`, matching sibling objects and reports, direct imports,
and sampled peak RSS. Both [author](evidence/author.log) and
[peer](evidence/peer.log) compiler logs are retained. The seven axiom
reports contain only `propext`, `Classical.choice`, and `Quot.sound`, with
no `sorryAx` or warnings. The Python `-O` control exited `1` before output
creation. This is a paired suffix replay, not a fresh full-project rebuild,
independent audit of this new packet, package-transitive/dynamic ancestry
review, or object-level proof.

Earlier failed attempts and their precise scope are retained in
[observations](observations/): initial ordered-instance errors had actual
exits `1` but their full source/log bytes were not saved; session `81341`
exited `1` on a parser error, and session `82910` exited `1` on a negative
cone-branch rewrite. The successful exploratory session `59882` exited `0`;
the paired replay above is the retained authoritative result for the
present source. The parser-failure source was reconstructed by reversing
the subsequent parser-only edits and is labelled accordingly.

To reproduce where the pinned temporary provider and suffix artifacts are
available, and only after coordinating other Lean processes, use:

```
python3 -I -S replay.py --output /tmp/ipra-reduced-model-descent-new
```
