# Integration into ProveIt

Suggested new report directory:
`Topology/UnknotRecognition/reports/graded_torus_occupancy_20261008/`.
A synthesis section may cite Theorems 3.1, 4.2, 5.2 and 6.1 of the supplied
article (check final numbering after any editorial changes).

## Preserve the maintained implementation

Do not replace `fast/fastunknot/` with the vendored reference code. This package
reuses a prior report's geometric harness, while the maintained scanner is
array-based and includes additional improvements. No production patch is
represented as tested here.

## Required adapter contract

1. Start from a certified open-braid disk frontier, with fixed top endpoints and
   current bottom endpoints. Close only after scanning the word. A generic PD
   frontier is not automatically interchangeable with this geometry.
2. Retain absolute raw `(h,q)` shifts. A child with resolution i and c circles
   labelled by mask ell has `(h+i, q+i+c-2*popcount(ell))`.
3. Each coefficient term from a to b must satisfy
   `q_b-q_a = s-c(a,b)+2*dot_count`, and h_b = h_a+1.
4. Allocate both resolutions and all delooped children before cancellation.
   Exhaust every homogeneous scalar identity, not just a heuristic subset.
5. Update incoming/outgoing adjacency locally. Keep a deduplicated scalar
   candidate queue and check stale candidates before mutation. Scalar candidates
   can only connect equal `(matching,q)` types at adjacent h, which proves an
   O(M*mu) bound on simultaneously pending pairs even when some are stale.
6. Keep coefficient encodings and caches inside the poly(s) * 2^O(s) envelope.
   Rebase boundary labels or release old stage caches. A relabelling must also
   transport overlay-circle / dot-subset indices.
7. Close every surviving object and every map. Use absolute quantum grading in
   final field-rank computations. For F_2 rank-two unknot detection first check
   that the closure has exactly one component.
8. Budget exhaustion must return an unknown/no-verdict status and permit an
   existing exact fallback; it is not a knot-type inference.

## Production validation before changing defaults

Run the complete maintained suite; compare every existing exact invariant/output
with the old version; replay this package's independent cube and graded residue
fixtures; verify braid/Markov relations and common-disk rebasing; test resource
failures; measure max live/allocated objects and caches. Benchmark the actual
production old/new algorithms on an identical output contract in fresh processes.

Use guaranteed indexing structures for a deterministic bit-complexity claim.
Python dictionary timings alone do not prove a worst-case lookup theorem.
Do not count full trace or explicit exponential-cube homotopy witnesses inside
an output contract that only promises homology ranks.

## Mathematical placement

The scalar residue formula and recovered grading should cite existing
`radical.tex` / `homogeneous.tex`, rather than be relabelled as wholly new.
The main new continuation is their use with a constant-per-bidegree relative
comparison model, the bounded-incidence cost estimate, and the torus-block
parameter theorem. Cite Kelomäki's external Morse model prominently. Theorems
remain statements about a specified scanner and certified classes, not about
all diagrams or all presentations.
