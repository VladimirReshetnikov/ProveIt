# Scoped intake of Report 19: lazy ordered evaluation

No gap was found in the stated finite-support mathematical argument. The
report evaluates the same ordered binary cellular automaton while avoiding
allocation of its full factor list. This can make individual steps practical;
it does not yet replace the ordered history by a smaller Diophantine circuit.

Root read the full proof and the displacement/context/validation audit
addendum. The files are in
`SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/five-particle-binary-automata/`:

| Read artifact | SHA-256 |
|---|---|
| `19-lazy-eval-PROOF.md` | `3845793b205fe1cbf88d018472b3f740ff506fa391f89fb79ad37dad1f41fe18` |
| `19-lazy-eval-audit-addendum.md` | `3d6bdf79d1a355a20313107d4b41095570c3c4363364db23e9159b5cc15c73b5` |

A separate reviewer read these proofs, the report's audit design, and the
frozen compiler's endpoint formulas as text. That review also found no gap
and cross-read this intake. In particular it checked the distinction between
the reverse endpoint's marker used for candidate geometry and its invariant
old-marker key used for exact matching.

This is a proof intake, not a fresh implementation audit. Neither archived
code nor old tests were executed; the factor-descriptor and gate-application
implementations have not been independently recertified here. Source-machine
universality, the frozen CA construction, and its input loader remain inherited
dependencies. Published benchmarks and test totals are not new evidence from
this intake.

## Why skipping is sound on arbitrary finite supports

Each two-particle endpoint contains an occupied pair at distance at most D.
Each three-particle endpoint has one such close pair, while its third particle
lies more than D from both pair members. Searching every close pair and every
third particle therefore detects the endpoint even in a malformed support
with multiple apparent heads. False candidates are harmless. Completeness,
not uniqueness of a global head, is the required property.

The cursor argument uses the current support. A noncandidate factor has no
raw key and hence acts identically. After a candidate changes the support,
discovery is repeated before advancing to any later factor. New candidates
behind the cursor are ignored, as the ordered product never revisits them;
new candidates ahead are included. A factor that leaves the support unchanged
does not invalidate the candidate set. This inductive invariant also works
with the reversed order. It would fail if discovery were performed only once
on the initial support.

The report correctly allows cascades on malformed inputs and does not infer
that entire E and P blocks are global involutions from their matching behavior
on admissible encodings. Its concrete cascade is evidence already in the
report, not an independently rerun fixture in this intake.

The displacement argument requires only a matching between equal-cardinality
endpoint sets, each contained in an interval of radius at most B3. Disjoint
active rewrite windows combine these matchings, giving displacement at most
2B3 per changing factor. No persistent particle labels are needed. Contextual
read intervals enlarge arithmetic bit width, not the movement bound. Closed
interval counting also correctly rejects multiple particles in one guard
window. Exact integer conflict masks describe the same finite class overlaps;
their potentially large cost is retained.

## The arithmetic boundary

A fresh scalar calculation verifies, for the report's published metadata,

    m=122622, p=66066, a=75495,
    D=2m+4p=509508,
    F=p(4D+15)+a+p(4D+14)+m
     =8pD+29p+m+a=269291358255.

This checks the formula and substitution, not the full source table. Avoiding
an allocation of F descriptors is a useful evaluation improvement. It does
not remove F factors from the definition of the ordered CA.

The number K of changing factors depends on the current support; the proof
retains K and the number of tested candidates in its cost bounds. At most F
factors are checked per fixed-source step. Sparse events also carry chronology:
skipped factors must act identically on the appropriate current support,
and candidate generation must be refreshed after every change. A certificate
that merely lists successful swaps would omit this obligation.

Thus a potential Diophantine transfer must explicitly encode or eliminate
cursor order, simultaneous gate semantics, the completeness of skipping,
and the varying event count. Unrolling an externally fixed number of steps
does not supply a fixed-arity certificate for unbounded time. Conversely,
this intake proves no lower bound against a future packed event certificate.
No ordinary-input loader, new universal operation bound, constant-K theorem,
or polynomial-in-log-J validation bound follows from the lazy evaluator.
