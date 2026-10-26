# Delete the selector which the native mask always forbids

This isolated packet decodes the entire pinned943-tile source, then retains
exactly its942 admissible selectors. The bijection is `g(0)=0` and
`g(j)=j+1` for1<=j<=941. Its image is precisely all old indices except1.
The omitted tile is exactly `(5,0,0,0)`, with coefficient6145; the retained
source MC mask already forbids its selector in every cell. All other
tile tuples, edge equalities, marked Start, actions and finite language
data are preserved. Every new selector coefficient is checked exactly
against its mapped decoded tile, not merely against modular residues.

Use selectors0..941, south942..950, north960..968, west969..976,
east978..985, Boolean dummy977 and zero-weight Start marker1005.
The shared color-copy shift18 and spatial shift9 are unchanged. With
Phi built from all942 admissible tiles and all34 weighted labels,

```
Lambda = rho^1992 + rho^2998
DC = rho^18 + rho^1005 + Lambda*Phi(1/rho)
DR = rho^9
K = DC + rho^(L+9)
MC = beta - rho^977 - G_942(rho) - Psi(rho,1).
```

There are978 physical positions and MC clears all978. There is no
forbidden-position exception or added rho term. In particular new
selector1, representing old selector2, is allowed by the actual mask.
Origin residues remain `MC=2 mod4` and `MF_native=4 mod8`, since a change
at rho's field1 concerns binary bit47, not binary bit1.

The complete clause centers are1992 and2998, with gap1006. First reflection
is1007. All17 color-copy fields, the marker, both full clauses and both
predecessors are checked. The only foreign upper-predecessor term is
`c0*x1005`. Maximum product is4003; padding covers18 full fields4004..4021
and low27 bits at4022. The native core105 plus873 padding bits gives978
tests, exactly complementary to MC. Whole shifted-origin and rank checks
retain `pc(R)=3dN+2` and `R=3 mod4`.

Start's positive south-copy tests are961..968. Every nonzero phase
candidate has offset at least20. At20 it requires new selector941,
which is old tile942, and its impossible complemented south bit0. Larger
surviving offsets force two distinct selectors in the same decoded cell.
The complete support enumeration has934 candidates: zero,932
multiple-selector contradictions, and that one calibrated exception.
The Boolean coefficient envelope is3829914518400942, exactly6145 below
its predecessor, and all carry/reset inequalities hold. Safe-dummy
increments have maximum exponents3975,986,977.

The full new controller works at `L=4027`, `d=189269`, with exact orders
23/1342, spacing30866 and auxiliary prime246929. The lift quotient is
184584. New K residues modulo47,4027,lambda are17,452,148485, giving
`H=(38,3031,56296)`. Dense polynomial, direct decoded-tile and whole-integer
routes agree. All four fixed integers are rebuilt; their total raw size
remains94,689 bytes. The intended improvement is the printed tile table
and closed MC recipe, not a further raw-byte reduction.

The probe also retains a scoped local obstruction for marker1004: at
offset19, new tile3 (old tile4) matches the tested Start south and marker
bits. This is not asserted to extend to a complete native word or equation
zero. A separate complete ordinary proof, independent review and whole
page/port binding are needed before promotion; accepted sources remain
unchanged.

```
python research/admissible942-probe/probe.py --write
python research/admissible942-probe/probe.py
python -O research/admissible942-probe/probe.py
```
