# Review: parallel particle dynamics and their quartic certificates

This successor intake reads the main proof notes of the newly committed
Reports 26, 27, 28 in full and checks the small literal quartic independently.
It executes none of the archive Python and does not rerun the prior compiler
suites. The three archive hashes and six member hashes are embedded in
[the bounded checker](review_parallel_particle_reports.py) and recorded in
[its exact receipt](review_parallel_particle_reports.json).

**Result.** The reports give a coherent route from two parallel full-shift
involutions to a source-sized sparse evaluator and a canonical natural-witness
quartic for each *fixed* finite horizon. This improves representation and
execution of the particle substrate. It supplies no smaller fixed-arity
universal polynomial and does not change the current 74/85 bounds.

## 1. Mathematical interface checked

Report 26's lemma starts from finitely many equal-weight endpoint swaps of
write radius b and endpoint-symmetric candidate predicates of read radius
r>=b. Candidate keys retain both type and anchor. Select a key only if it is
alone within H=2(b+r) and its hypothetical swap preserves the entire candidate
key set within b+r. The latter local comparison is global key preservation:
outside that interval the swap cannot affect a predicate.

The crucial simultaneous step is valid. A candidate read window cannot meet
two selected write windows, since their anchors are separated by more than
2(b+r). Therefore simultaneous swaps preserve every raw candidate predicate.
A key's prospective test reads only radius b+2r; every other selected write
window is outside this neighborhood of an isolated key. Its own swap
interchanges the two candidate sets being compared. Thus eligibility of both
selected and rejected keys is preserved. The second application undoes exactly
the same swaps, on arbitrary full-shift inputs. The radius bound is 3(b+r).

Applying the lemma to the existing five-particle endpoint geometry gives two
blocks and the bound 180D+258+9J. The report retains the old guards, exact
read intervals and reverse endpoints. Its admissible-state argument partitions
every free/contact boundary and makes the unique intended key pass the
prospective test. The inherited template geometry/source simulation is still
a dependency: this intake has not reconstructed the complete source compiler.
The new CA differs from the old ordered rule on malformed configurations, so
an old arbitrary-input evaluator or certificate cannot be reused on that
basis alone.

Report 27 supplies the needed new evaluator. Every literal endpoint has a
unique close pair; enumerating occupied pairs, optional third particles and
incident source records finds its type. Testing its exactness and guard then
recovers every raw type-anchor key, including on malformed supports. Reverse
free motion and reverse endpoint interactions use their actual predecessor
anchors. Complete rediscovery after each hypothetical swap is necessary:
checking only initially present types would miss candidate births.

All isolated candidate supports are disjoint and contain at least two
particles, so a mass-n block has at most floor(n/2) hypothetical swaps. The
resulting two-block step uses at most 2+2floor(n/2)<=n+2 raw-discovery calls,
or at most 4+4floor(n/2)<=2n+4 with the stated verification. Source incidence,
explicit guard-class tables, sorting and integer bit costs still count. This
is not an arithmetic circuit with just two paid operations.

Report 28 replaces dynamic scheduling with fixed slots, deterministic sorting,
prefix-rank routing and fully computed hypothetical lanes. All source records,
false guard cells, missing-lane dummies and rejected branches remain paid.
Canonical signed natural pairs and comparator bits/slacks have unique values;
every assignment depends only on earlier wires. Consequently the triangular
system has at most one complete natural assignment for each external tuple,
and the endpoint/domain checks retain it exactly for the desired relation.
This is a natural-witness theorem; the note makes no real-witness uniqueness
claim. The topological construction, not single-coordinate mutation tests,
is the argument for complete witness uniqueness.

## 2. Independent finite evidence

The fresh checker implements the generic lemma example directly, with
b=r=1, endpoint supports{-1,0} and{-1,1}, period 12 and H=4. It enumerates all
4,096 binary words. Raw keys, all selection statuses, mass and involutivity
are preserved. There are 504 changed words and 72 words with multiple selected
moves, so the checks are not vacuous. Omitting prospectivity sends
{0,1,2} to{0,1,3} and then fixes the latter; the actual rule rejects that move.
This finite periodic example supports the lemma's mechanism, not the entire
particle compiler or full-shift theorem.

For Report 28's supplied two-particle, one-step example, the checker parses
all 1,502 residuals independently and expands their squares with exact integer
coefficients. The result equals the entire saved 12,595-term quartic. Counts:

| Quantity | Independently recounted value |
|---|---:|
| External natural coordinates |8|
| Natural witnesses |1494|
| Residuals |1502|
| Residual monomial occurrences |5511|
| Ordered expansion contributions |29249|
| Collected polynomial monomials |12595|
| Exact polynomial degree |4|
| Sum of coefficient bit lengths |29413|

Every residual and the expanded quartic vanish at the complete supplied
assignment for{0,5}->{1,6}. Incrementing each of the 1,494 witness coordinates
individually breaks an incident residual. This checks the pinned algebraic
artifact and supplied assignment; it neither reconstructs the emitter nor
independently proves that every source instance has the advertised semantics.

The archived sample's 95 endpoint types, new-rule radius 1,698, and old ordered
radius 21,144 describe different resources from the 1,494 witnesses and 1,502
squares. The review keeps those quantities separate.

## 3. Consequence for universal Diophantine research

The fixed source, mass n, horizon T and direction are compiler arguments.
The witness formula is

    W(T)=4 max(n-1,0)+T(w_E+w_P).

For the two-particle example, w_E=w_P=745, so W(T)=4+1490T.
The construction therefore has horizon-dependent arity. Treating T as an
existential input to one of these finite expanded polynomials would require
another encoding theorem; the family itself does not supply it. Likewise,
unique finite-horizon witnesses do not establish a finite-fold representation
for unrestricted halting.

The useful future interface is the deterministic bounded-mass evaluator and
its charged source-record/slot circuit. A new unbounded-history compression
could use that interface. Its costs would have to include the complete
prospective rediscovery and ordinary-input loader. None is inferred here
from the two-involution presentation or the degree-four finite certificates.

## Replay and limits

From any working directory:

    python /absolute/path/to/review_parallel_particle_reports.py \
      --repo-root /absolute/path/to/Proofs \
      --expect /absolute/path/to/review_parallel_particle_reports.json

The checker reads only pinned archive data, uses the Python standard library,
and keeps its checks active under optimization. It compares receipts with
exact JSON types. It is deliberately a validator of these pinned artifacts,
not an untrusted replacement archive loader or a general certificate API.
Report 26's full source binding and Report 28's general emitter implementation
remain outside this bounded replay. The main proof notes were read; their
historical audit claims are not reported as newly rerun evidence.
