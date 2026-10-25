# Whole incoming complemented-label radix47 sidecar

**Ten positive unknowns; useful profiles 79 operations / degree 382 and 80 / 338.**
This separate component specializes the four lower-Y circuits to the entire
incoming complemented-label radix47 tuple. Its four raw constants total
**207,214 bytes**, and its largest fixed port has **415,904 bits**.
The sibling `positive/` radix67 component is unchanged.

| Literal DAG | Chart | Weight | Operations | Degree | Role |
|---|---|---|---:|---:|---|
| `q2_v2.json` | X=qw,Y=q²s,D=q⁵ | V² |78|516|dominated control|
| `q2_bv.json` | X=qw,Y=q²s,D=q⁵ | bV |79|382|useful tradeoff|
| `q1_v2.json` | X=q²w,Y=qs,D=q⁶ | V² |79|456|dominated control|
| `q1_bv.json` | X=q²w,Y=qs,D=q⁶ | bV |80|338|useful tradeoff|

## Exact source and attribution

This is the complete **incoming** complemented-label encoding in
`ConZFC_Common_Remainders_Radix47_2026-10-25.zip`, not the current repository's
conditional three-anchor/clause-alias radix47 layout. It complements all 34
physical label bits and uses seven shared marker weights, complete carry bounds,
new padding and its own certified controller. Those encoding results and the
coefficient storage improvement are inherited, not claimed as new here.
We claim only their explicit checked composition with the new four charts.

`PROOF.md` gives both directions and an explicit fresh-positive-witness bridge
to the **actual incoming P66 polynomial**, with its six factors equal to
1,1,1,1,1,Delta. It does not substitute ports using scalar inequalities alone.
`REDUCTION_PROOF.md` is the unchanged original radix67 reduction proof retained
as a mathematical dependency; its original tuple-size and decoder labels are
historical. The bridge explicitly replaces that final native specialization
and its canonical witnesses with the complete new47 source, not the algebra.

The whole incoming proof, source polynomial, all four payloads, 51 native target
identities, independent review, and 37 retained dependencies are copied under
`provenance/radix47/`. The active `SOURCE_PINS.json` resolves every listed file
locally. Historical ledgers and programs are retained as static evidence;
no inherited producing program is executed or imported.

The theorem is ordinary mathematics formalizable in ZFC at the named retained
Pell/native/refutation boundary: no positive zero iff Con(ZFC). No consistency
proof, zero-existence claim, new full Lean/Rocq or object-ZFC proof, acceptance
of the incoming encoding into the current repository, or global optimum is claimed.

## Reproduce offline

Python 3.10+ and its standard library suffice. Run from this directory:

    python3 -B build.py --check
    python3 -B verify.py --output /tmp/positive47-check.json
    python3 -B -O verify.py --output /tmp/positive47-check-O.json
    python3 -B rebuild_coefficients.py

The producer reads frozen JSON only. The independent verifier does not import
it. The rebuilder decodes the full seed and all 943 tiles, reconstructs all 3297
Phi coefficients and the entire four-integer tuple, checks every raw byte against
the incoming P66 binding, collects all 51 native target linear identities, and
checks actual mask populations, carry bounds, controller primes, exact orders,
units and valuation-one lift. The graph verifier covers every row, proves all
whole leading forms, checks liveness/counts, enforces the coherent tuple across
all four graphs, and rejects ten actual algebraic corruptions per graph.
Normal and optimized receipts agree. Finite tests do not replace the full
unbounded source proof or establish existence or absence of a refutation.

The graphs have the same free-port row lists as their radix67 siblings, but
represent different specialized polynomials. All four constants change together;
there is no per-port selector or fallback to another radix. Source pins and
archive hashes are recorded in `SOURCE_PINS.json` and `PROVENANCE.json`.
`report_section.tex` and `coefficients.tex` are the article-ready bridge and
complete new47 fixed-integer recipe. The original incoming complete native
one-page TeX/PDF is also retained as evidence, not renamed as our ten-variable equation.

No remote repository was modified or published. New bridge exposition and
verification were prepared with AI assistance. Independent review means a
separate review in this workflow, not outside human endorsement.
