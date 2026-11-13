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

**Conditional mask-cover guard.** The [fixed-symbolic-mask specialization](../trace74-fixed-mask-saturation-conditional-rebuild/README.md) now discharges the mask-cover inequality in every indicated arithmetic model and derives `F+C<q` under the remaining natural block, range, positivity and population hypotheses. Saturation supplies both no-carry facts before mask coverage supplies `F≤MC*J`; the guard is not assumed. These remaining hypotheses have not been derived from a fixed-BFS 74 zero. The check retains inherited provider ancestry, search-path and exact unevaluated-power-warning limitations.

**Guard-independent roots.** For positive 74 witnesses and positive beta, the separately [Lean-checked model theorem](../trace74-arbitrary-root-draft/README.md) extracts the two positive root witnesses without assuming `F+C<q`. It uses the ring coordinate identity with a potentially negative synthetic old alpha and factors independent of that coordinate. A subsequent [Lean-checked Pell client](../trace74-arbitrary-root-draft/PELL.md) derives a positive first recurrence index and doubled norm, still without that guard. A further [first-index residue theorem](../trace74-arbitrary-root-draft/RESIDUE.md) shows `k ≡ 2*n (mod q⁴)` for the same positive Pell index, still without the guard. These direct-pin checks retain provider ancestry, search-path and intermediate-object limitations. The [guard-independent carrier and signed-offset theorem](../trace74-guardfree-adjacent-draft/OFFSET.md) also derives `q⁴ ∣ e` in the model difference ring for the same positive 74 zero. A further [signed-rank congruence](../trace74-signed-rank-congruence-draft/README.md) combines it with the same first Pell index: `q⁴ ∣ (rank+1−2n)` in the difference ring. The link to a natural rank, repunit, rank/population bounds, a fixed-port guard and an iPRA endpoint remain open.

**Guard-independent Pell bounds.** A [four-stage checked client](../trace74-guardfree-fold-draft/README.md) recovers an odd Pell ordinate and derives first Pell index `n≥2`, `8P+4≤k`, and `2q⁴<c` from a positive 74 zero without the reverse guard. A later [checked exclusion](../trace74-n2-exclusion-join-draft/README.md) rules out the small first-index branch when `q≥4`, giving `n≥3` and `32P²+32P+6≤k`. The checks retain provider ancestry and search-path limitations. The separate fixed-payload `n=2` scalar example is only partial and is not a full graph zero.

For `beta≥31`, the checked first/main index window forces main index 5 if the first index is 3. A [model-level graph theorem](../trace74-n3-graph-exclusion-draft/README.md) excludes that case by joining exact Pell formulas, ordered-ring inequalities and the graph's q-divisibility. Its [follow-up](../trace74-first-index-four-draft/README.md) gives first index `n≥4` for the same zero and preserves the first-index residue. An [ordinary scalar family](../trace74-n4-scalar-pell-witness/README.md) shows that the same two ordinate equations and q-divisibilities alone do not exclude index 4; it is not a graph zero. These checks retain their recorded provider and external-binding limitations and do not derive the 74 guard.

The weighted graph projection supplies a further constraint: a [checked graph theorem](../trace74-n4-r5-graph-exclusion-draft/README.md) excludes simultaneous first index 4 and main index 5 for the same positive zero at `beta≥31`. The [index-four client](../trace74-n4-odd-seven-draft/README.md) therefore identifies its main ordinate with index 7. A later [graph exclusion](../trace74-n4-graph-exclusion-draft/README.md) rules out that remaining case using the q-divisibility and exact seventh-ordinate interval. For `q≥2³⁰`, the checked [index-five exclusion](../trace74-n5-graph-exclusion-draft/README.md) and [follow-up](../trace74-first-index-six-draft/README.md) raise the first-index bound to `n≥6` when `beta≥31`. A [fixed-symbolic-beta client](../trace74-fixed-first-index-six-draft/README.md) supplies both bounds from the symbolic beta and positive first witness; its other ports remain arbitrary.

A further [same-zero theorem](../trace74-atleast-five-r7-graph-exclusion-draft/README.md) excludes main ordinate index 7 whenever the supplied first index is at least 5 and `q≥2³⁰`. These checks retain their recorded provider and external-binding limitations; they do not supply the missing rank sign, guard, or iPRA endpoint.

The subsequent [index-six exclusion](../trace74-n6-graph-exclusion-draft/README.md) and [index bound](../trace74-first-index-seven-draft/README.md) raise the first index to `n≥7` when `beta≥31` and `q≥2³⁰`. A [general index-nine exclusion](../trace74-atleast-seven-r9-graph-exclusion-draft/README.md) then yields a linked odd main index `r≥11`, retaining `n<r<2n` for the same zero. A [symbolic-beta specialization](../trace74-fixed-main-index-eleven-draft/README.md) supplies the size bounds from a positive first witness; its other ports remain arbitrary. A [model-level graph theorem](../trace74-near-diagonal-graph-join/README.md) excludes the additional window `r≤n+2` for `n≥8` and `q≥2³⁰`, with both ordinate equations for that same zero. The result does not exclude larger index gaps or establish the reverse guard or the iPRA endpoint.

The [fixed-symbolic client](../trace74-near-diagonal-fixed-client/README.md) combines these bounds for one positive zero: `n≥7`, `r≥11`, and `n+2<r<2n`, retaining both ordinate identities, oddness and the first-index residue. Its other ports remain arbitrary; the external fixed-payload link and the reverse guard remain open.

The [global width-three fixed-symbolic client](../trace74-width3-fixed-global/README.md) strengthens that same linked pair to `n+3<r<2n` without an extra lower bound on `n`. It combines the large-`n` theorem with the separately checked exclusions of the two surviving small-index pairs, `n=8,r=11` and `n=10,r=13`.

The [variable-width model criterion](../trace74-variable-width-index-client/README.md) excludes further same-zero index pairs under its explicit arithmetic threshold. Its [two-sevenths fixed-symbolic client](../trace74-variable-width-two-sevenths/README.md) retains one linked pair and proves both `n+min(⌊n/4⌋,118013)<r` and `n+min(⌊2n/7⌋,32781)<r` without an upper bound on `n`; neither bound dominates the other for all `n`. The [fractional client](../trace74-variable-width-fractional-client/README.md) separately proves `8n≤590069 → 5n<4r`. These checks use captured providers, and the reverse guard and iPRA endpoint remain open.

An [ordinary-integer extension](../trace74-near-diagonal-width345/README.md) analyzes wider windows `r≤n+c` for `c=3,4,5` at `n≥4c`, using the same graph projection assumptions and `Y≥q³`. The [width-three graph join](../trace74-width3-graph-join/README.md) now checks the `c=3` exclusion in Lean for `n≥12` and `q≥2³⁰`, retaining the same tuple and both supplied ordinate equations. The widths four and five remain ordinary-integer arguments. A separate [general fixed-width note](../trace74-general-width-obstruction/README.md) gives wider conditional thresholds and a symbolic-beta calculation, without a model-level proof of those general bounds.

**Conditional natural rank.** Under the individual bounds `0<F<q`, `0<C≤q` and the stated port conditions, the [checked natural rank/window and difference-ring binding](../trace74-natural-rank-window-draft/README.md) give `3q<R` and `R+q³+q+1≤q⁴` without assuming `F+C<q`. It remains open whether a positive fixed-port 74 zero forces those individual bounds.

The later [fixed-port-bounds saturation join](../trace74-fixed-rank-port-bounds-rebuild/README.md) discharges the fixed mask's three basic bounds and proves the guard from those individual bounds, the specified port identities, the radix equality and two population inequalities. The [repunit specialization](../trace74-fixed-mask-repunit-split-draft/README.md) supplies the radix and fixed-mask population data from one positive repunit length. Separately, the [population-window theorem](../trace74-population-window-rebuild/README.md) obtains a second population bound under its stated power, alignment and ordinate hypotheses. None of these results derives the individual bounds, repunit, power or alignment from a 74 zero; the fixed symbolic coefficients' link to the external payload remains external.

**Further guard-free congruences.** For the same actual positive zero, the [main-index theorem](../trace74-signed-rank-main-draft/README.md) relates the magnitude of the signed rank to an odd main Pell index `r≥3` by `SignMod c |R| r`. The [model remainder theorem](../trace74-fc-model-remainder-draft/README.md) also gives `(C+MC·J+q(F+MF·J)+1) % q² = (2n) % q²` for the same first-Pell index `n≥3` when `q≥4`. A separate [checked index window](../trace74-index-upper-draft/GRAPH-README.md) establishes `n<r<2n` for first and odd main indices of the same graph zero when `beta≥15`. These results do not bound `F` or `C`, identify the two indices, or prove the reverse guard. The checks retain their recorded captured-provider and external-binding limitations.

**Guard-free projection and upper bound.** A [Lean-checked projection](../trace74-guardfree-projection-draft/README.md) uses the actual positive graph zero and its odd main Pell ordinate to prove divisibility of the weighted product `(h·X)(X−2ʳ)(2ʳX+1)` by `H`. The required index alignment and height bound are still open, so this is not yet `X=2ʳ`. Independently, a [Lean-checked model theorem](../trace74-guardfree-rank-upper-draft/README.md) gives `R+q³+q+1≤q⁴` for positive `J,F,C` under the stated natural-port inequalities, even when `R` is negative. It assumes neither a graph zero nor the individual digit bounds. Its [external arithmetic precursor](../trace74-signed-rank-upper-bound/README.md) exhibits a negative-rank scalar example, so the upper bound alone gives no lower bound on the signed rank. Both Lean results retain their recorded provider and external-binding limitations.

**Guard-independent carrier sign.** The [checked carrier client](../trace74-carrier-nonnegative-draft/README.md) proves that an actual positive 74 zero with positive beta has `B≥0` and `F≤(K0+w)C`, without assuming the reverse guard. This does not give `F<q` or `C≤q` on its own; a separate fixed-payload partial example satisfies `B>0` and the first-Pell/size/offset facts while `F≥q³`. The latter is not a full graph zero. The Lean check retains its direct-pin/provider limitations.

**Boundary investigation.** A [Lean-checked same-witness theorem](../trace74-boundary-concrete-zero-rebuild/README.md), with an [independent result audit](../../reviews/trace74-boundary-concrete-zero-result-independent/README.md), now proves the following for every IΣ₁ model with the stated `ORingStructure`: at the ports `(beta,K0,MC,MF)=(1,1,28,0)` there is one positive valuation `w` for the formal `value74` graph with `w 0=w 1=w 2=1`, `value74=0` in the model difference ring, and `q=w 1+w 2`. Thus the strict guard `F+C<q` does not follow from positivity and a 74 zero for arbitrary ports. The proof returns an existential witness; it does not export a closed vector of numerals.

The theorem uses the [kernel-checked finite Pell interval](../trace74-boundary-natural-seed-rebuild/README.md), [generic model transfer and assembly](../trace74-boundary-generic-assembly-rebuild/README.md), and [cast-based model facts](../trace74-boundary-seed-model-facts-rebuild/README.md). Its captured provider closure retains the four inherited baseline source-ancestry and outside/package/dynamic limits documented in the result audit. The formal Lean graph's correspondence with the external JSON remains external.

These ports violate the fixed BFS bounds. The counterexample does not decide the guard at the fixed BFS tuple, prove that the 75 graph has no positive zero, establish 74/75 existence inequivalence, or supply a fixed-port halt/iPRA theorem.

The [conditional saturation theorem](../trace74-conditional-saturation-guard-rebuild/README.md)
now has a Lean replay and independent result audit: its natural block,
size, population, and `F <= MC*J` assumptions imply both no-carry facts and
the guard. A separate [scalar example](../trace74-saturation-scalar-obstruction/README.md)
shows why saturation and no-carry alone do not imply that comparison for
arbitrary ports. For the retained fixed payload an [external exact check](../trace74-fixed-mask-cover/README.md)
establishes `MC + HP > beta`. A separate [Lean model theorem](../trace74-symbolic-cover-model-cast-rebuild/README.md)
now proves coverage for the symbolic ports, and the fixed-mask saturation
specialization above uses it. The connection between the external payload and
those symbolic ports remains external; neither route has derived the block
and population assumptions from a 74 zero.

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

**Fixed-port guard under investigation.** A [coupled-Pell construction](../trace74-symbolic-coupled-pell-strategy/README.md)
proposes a positive 74 zero at the retained external ports with `F+C≥q`.
An [independent mathematical review](../../reviews/trace74-symbolic-coupled-pell-strategy-independent/README.md)
found the construction valid conditional on the recorded finite gcd checks
and port/graph correspondence. The enormous witness has not been
materialized, and the external computations and file-to-Lean binding are
not Lean theorems. This is strong evidence against the universal reverse
guard, not an independently kernel-checked counterexample or a decision of
74/75 positive-existence equivalence. The maintained root equation is
separate from this research candidate.

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

The [FreeJ transport comparison](../trace74-freej-transport-comparison/README.md) records the exact 74 versus Compact44 transport-register identity and why the positive synthetic alpha/guard cannot be assumed when applying that pattern to this independent C chart. The checked 74 B-nonnegativity consequence alone does not establish the guard.
