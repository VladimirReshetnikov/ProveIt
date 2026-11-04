# Trace75 mask-coordinate probe: 74 operations

This is a separate research candidate, derived from package 163's
`compact/equations/trace75_degree402.json` (SHA-256
`8b9b9421ae8a0762725852034b3db6d29b14660b3a4d0587e1494a933b5271c9`).
It has 10 strictly positive witnesses and four fixed ports; all 74 rows and
all 14 inputs are live. The binary operation count is 44 multiplications,
16 additions and 14 subtractions. Subtractions are integer subtractions.
The changed chart has exact degree 402 by the separate [external degree
certificate](../trace74-degree-check/README.md), which checks the actual
fixed coefficients; this is not a Lean degree theorem.

The old witness `alpha` is replaced at witness index 2 by `C`. Write
`bJ = beta*J`, `q = bJ+1`, `qmF = q-F`. The graph removes the old row
`C = qmF-alpha`, replaces `G1 = bJ*qmF` by `G1 = q*qmF`, and replaces
`G = G1+alpha` by `G = G1-C`. Every other row retains its exact order and
operands. For the substitution `alpha = q-F-C`, the old `C` equals the new
witness `C`, and

```
old G = bJ*(q-F) + (q-F-C) = q*(q-F)-C = new G.
```

The only consumer of the different old/new `G1` is `G`. Exact polynomial
normalization of these local identities in Z[bJ,F,C], together with the
ordered-row comparison, proves equality of every shared observable register
and hence of the output after this substitution, in every commutative ring.
The coordinate map is an involution on unrestricted ring valuations. The
provided script is an external checker. A separate [Lean ring client](../trace75-mask-coordinate-ring-probe/README.md)
now proves the corresponding identity against `value75` for arbitrary ports;
the JSON-to-Lean row comparison remains external.

**Positive-domain boundary.** From a positive old valuation, the mapped
candidate witness `C=q-F-alpha` is positive only if `alpha+F<q`. From a
positive candidate valuation, the mapped old witness `alpha=q-F-C` is
positive only if `F+C<q`. With those respective guards, the coordinate maps
are inverse and preserve zero. The reverse guard `F+C<q` does not follow
from a positive graph zero for arbitrary ports, as shown below. Whether it
follows at the fixed BFS tuple remains open. No unconditional positive-solution
equivalence, halt equivalence or internal iPRA proof for this candidate is asserted.

**Conditional mask-cover guard.** The separately [Lean-checked model lemma](../trace74-mask-cover-guard-draft/COMBINED.md) derives `F+C<q` from the natural four-block identity, its two population inequalities and stated size/positivity bounds, together with `beta+1≤MC+HP` and `HP≤beta`. Saturation supplies both no-carry facts before mask coverage supplies `F≤MC*J`; the guard is not assumed. This remains conditional: these block/population facts and symbolic fixed-mask hypotheses have not been derived from a fixed-BFS 74 zero. The check retains inherited provider ancestry and search-path limitations.

**Guard-independent roots.** For positive 74 witnesses and positive beta, the separately [Lean-checked model theorem](../trace74-arbitrary-root-draft/README.md) extracts the two positive root witnesses without assuming `F+C<q`. It uses the ring coordinate identity with a potentially negative synthetic old alpha and factors independent of that coordinate. A subsequent [Lean-checked Pell client](../trace74-arbitrary-root-draft/PELL.md) derives a positive first recurrence index and doubled norm, still without that guard. A further [first-index residue theorem](../trace74-arbitrary-root-draft/RESIDUE.md) shows `k ≡ 2*n (mod q⁴)` for the same positive Pell index, still without the guard. These direct-pin checks retain provider ancestry, search-path and intermediate-object limitations. The [guard-independent carrier and signed-offset theorem](../trace74-guardfree-adjacent-draft/OFFSET.md) also derives `q⁴ ∣ e` in the model difference ring for the same positive 74 zero. A further [signed-rank congruence](../trace74-signed-rank-congruence-draft/README.md) combines it with the same first Pell index: `q⁴ ∣ (rank+1−2n)` in the difference ring. The link to a natural rank, repunit, rank/population bounds, a fixed-port guard and an iPRA endpoint remain open.

**Boundary investigation.** A [Lean-checked same-witness theorem](../trace74-boundary-concrete-zero-rebuild/README.md), with an [independent result audit](../../reviews/trace74-boundary-concrete-zero-result-independent/README.md), now proves the following for every IΣ₁ model with the stated `ORingStructure`: at the ports `(beta,K0,MC,MF)=(1,1,28,0)` there is one positive valuation `w` for the formal `value74` graph with `w 0=w 1=w 2=1`, `value74=0` in the model difference ring, and `q=w 1+w 2`. Thus the strict guard `F+C<q` does not follow from positivity and a 74 zero for arbitrary ports. The proof returns an existential witness; it does not export a closed vector of numerals.

The theorem uses the [kernel-checked finite Pell interval](../trace74-boundary-natural-seed-rebuild/README.md), [generic model transfer and assembly](../trace74-boundary-generic-assembly-rebuild/README.md), and [cast-based model facts](../trace74-boundary-seed-model-facts-rebuild/README.md). Its captured provider closure retains the four inherited baseline source-ancestry and outside/package/dynamic limits documented in the result audit. The formal Lean graph's correspondence with the external JSON remains external.

These ports violate the fixed BFS bounds. The counterexample does not decide the guard at the fixed BFS tuple, prove that the 75 graph has no positive zero, establish 74/75 existence inequivalence, or supply a fixed-port halt/iPRA theorem.

The [conditional saturation theorem](../trace74-conditional-saturation-guard-rebuild/README.md)
now has a Lean replay and independent result audit: its natural block,
size, population, and `F <= MC*J` assumptions imply both no-carry facts and
the guard. A separate [scalar example](../trace74-saturation-scalar-obstruction/README.md)
shows why saturation and no-carry alone do not imply that comparison for
arbitrary ports. For the retained fixed payload an [external exact check](../trace74-fixed-mask-cover/README.md)
establishes `MC + HP > beta`; a conditional model-arithmetic draft uses that
cover and the second no-carry fact to recover the comparison. The fixed mask
check is not yet a Lean theorem about the symbolic ports, and neither route
has derived the block and population assumptions from a 74 zero.

The `coefficient_binding` object, including the tuple description and all
compressed/raw hashes, is copied verbatim from the pinned 75-row JSON. Its
`coefficients/` path belongs to that source package's layout, not this probe's
directory. The parent compressed files available in
`candidates/ten-positive-qcube-product-square/coefficients/` match each
`parent_gzip_sha256`; decompressing them yields all four pinned raw hashes
and bit lengths, and their values satisfy the stated elementary mask bounds.
The new package-163 compressed hashes are retained as metadata but those
compressed files are not reconstructed or checked here. The direct-BFS tuple
label is inherited; this check does not independently prove its connection to
Lean's symbolic direct-BFS port or to any file/PDF displayed elsewhere.
In particular, no other tuple is silently substituted for the exact inherited
raw `K0` hash `0a86821a704294199c2e1a50379d242c96840a3366e9d965689ba3d74605203f`.

Reproduce the read-only check from the repository root:

```
python3 -I -S -B Computability/DiophantineConsistency/research/trace74-mask-coordinate-probe/check.py
```

The captured output is `check-observation.txt`. The script pins both JSON files, checks
ordered topology, liveness and every row transformation, computes the local
symbolic identities, compares shared register evaluations on 100 deterministic
modular samples, and checks the available parent coefficient payloads.
Sampling is a diagnostic; the exact local normalization and row induction
supply the all-ring reasoning.
