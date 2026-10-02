# Six new substrate reports: review, constructor repairs and local reductions

The six reports delivered at `1977e6ea6` pass mathematical review within their
stated domains and quantifiers. Three sandpile constructor defects and a
thermal circuit-descriptor defect are reproducible; checked repair patches
are supplied below. All original author suites and exported examples replay.
The wiring reports also yield three concrete natural-domain residual
reductions. None of these report-level counts lowers the separate universal
87-operation bound.

The contemporaneous [complete sparse-TM improvement to744](gpcp_history_computed_fields744.md)
is a separate proved result:744 operations,122 positive witnesses and exact
degree187625. The new reports are not used as a substitute for its ordinary
input, program or positive-witness proof.

The [replay checker](incoming_substrate_review_1977e6ea6.py) and
[receipt](incoming_substrate_review_1977e6ea6.json) pin all six archives and
every member. They execute18 original verifier/CLI commands in private copies,
including all eight delivered erasure certificates. The deliberately wrong
uniform-erasure target must reject. Retired archives are read from their
tracked arrival commit, with the same byte hashes checked; all six fallback
paths are exercised even while the ZIPs remain in `docs/incoming`.

This is mathematical and source review supported by exact finite checks.
It does not certify historical priority, constitute a Lean/Rocq proof, or
repeat the authors' PDF rendering audits. The delivered archives are preserved
unchanged. The repair patches are applied and tested in private copies; they
are not silently substituted for the original bytes in the review.

## What each report actually supplies

|Report|Reviewed result|Remaining universal-interface cost|
|---|---|---|
|Exact Wiring|Exact six-rule wiring semantics, boundary parity/product bounds, sorted-memory certificates and a constructive finite controller argument|The shipped polynomial exporter is the memory component; full unknown-schedule controller export and fixed-arity unbounded compression remain absent|
|Topology Is Not Free|Exact local loop kernel, chronological/sorted memory, and a paper construction for bounded unknown schedules|Delivered quartics are local loop and memory kernels; the complete controller is not a shipped exporter|
|No Ghost Wires|Implemented endpoint-parametric quartics for all six rules along an externally supplied finite structural schedule, with exact cyclic-wire counts|Schedule choice, horizon-independent arity and a paid ordinary-integer loader remain separate|
|Exact Erasure|Strictly positive stochastic mortality embeddings without a common invariant line, and two bounded numerical quartic encodings|The alphabet encodes the instance; bounded arity grows with word length; no single printed universal alphabet/input loader is supplied|
|Thermal Arithmetic|A natural-DAG root-preserving diagonal Hamiltonian with effective positive-spectrum confinement and precise undecidable endpoint predicates|Static spectral representation, not autonomous step-by-step computation; no numerical universal polynomial is instantiated or counted|
|Sandpile|Unique natural cubic certificates for finite undirected stabilization, spatial closure, canonical radius and exact eventual periods|The spatial radius remains a compiler parameter; the universal loader is imported and fixed-arity compression is absent|

These differences matter. A finite-horizon quartic, a cubic family with growing
spatial arity, and an existence-level MRDP consequence cannot be compared to a
fully charged universal arithmetic circuit just by their polynomial degree.

## Exact wiring and interaction nets

All three wiring articles and their Python sources were read. The numbered
annihilation conventions agree with Lafont: delta preserves auxiliary labels
and gamma exchanges them. Cyclic wires without ports are retained. These
conventions were checked against the original rule diagrams, not inferred
from an unlabelled underlying graph. See [Lafont, Interaction Combinators](https://www.i2m.univ-amu.fr/perso/yves.lafont/pub/combinators.ps),
journal pages71 and81–82.

**Exact Wiring.** Its boundary-subset parity theorem and bounded product
argument are sound in their declared finite domain. Strict sorted keys and
time bounds force chronological consistency; address-change flags and reset
gaps are uniquely recovered. The controller composition is constructive
mathematics, while the implemented exported polynomial is the memory circuit.
The displayed example has144 residuals,167 natural witnesses and21 parameters.
The reviewer found one minor API limitation: `Circuit.failures` ignores unused
trailing natural coordinates instead of requiring the exact declared tuple
length. This does not change the polynomial on its declared coordinate set.

**Topology Is Not Free.** Component gluing and its local arithmetic kernel
correctly count both two-edge cycles and longer closed wires. The local loop
kernel has23 residuals and17 auxiliary coordinates over six source matching
coordinates. Its distinct sorted-memory encoding has `17L−4` residuals.
The linear-size unknown-schedule construction is supplied on paper; the
delivered exporters cover these kernels rather than a complete machine.

**No Ghost Wires.** Pair suppression and permutation-orbit gluing agree with
component traversal. For the old/replacement matching alpha and gluing
involution beta fixing the surviving boundary B, the exact relation is

```text
cycles(alpha composed with beta) = |B|/2 + 2*(new closed wires).
```

The orbit minimum, distance and reset equations uniquely determine the
auxiliary fields on natural coordinates. The implemented compiler genuinely
composes all six rules with fixed endpoint parameters and an externally
supplied schedule. Its distinguishing two-step example has68 parameters,
126 witnesses and169 quadratic residuals. Its quartic degree is a finite
trace result; neither unknown schedules nor unbounded computation are encoded
at fixed cost. A repeating net up to a specified renaming is a sufficient
nontermination certificate, not a characterization of all infinite runs.

The [earlier quadratic delta certificate](interaction_combinator_quadratic_topology.md)
has a different scope and ledger: its472-operation quartic pays a complete
selected delta step and its routing helpers. That terminating fragment is not
the new reports' six-rule compiler, and its operation count is not directly
comparable with their residual counts.

### Three source-derived reductions

These are proved local transfers checked against the actual emitted residuals.
The [portable wiring checker](incoming_wiring_checks_1977e6ea6.py) preserves the finite tests;
a separately hardened rewritten
compiler and optimized straight-line operation ledger are future work.

1. **No Ghost orbit rows:169→147 in the example, same126 witnesses.** The
   retained equation `d=(1−e)(s+1)` with `d,e,s≥0` forces `e≤1`, hence
   `e∈{0,1}`. Delete `e(e−1)=0`. With the retained reset `eh=0`, replace
   `r+(1−e)(h+1)−i=0` by the linear row `r+h+1−e−i=0`; the old row is the
   new row minus `eh`. This changes fixed-successor orbit blocks from5n to4n
   rows and selector blocks from6n to5n, preserving the complete natural zero
   set. It is not equality of the two SOS polynomials away from their zeros.
   Over signed integers the bit implication fails; the recorded one-point
   exception has `(r,d,e,h,s)=(-1,-2,-1,0,-2)`.

2. **Topology loop kernel:23→15 rows and17→15 helpers.** Its four equations
   `e_i+sum_j m_ij=1` already force every natural source matching entry to be
   Boolean, so six separate Boolean rows are redundant. For each of the two
   fixed gluing edges, `g_ij=h_ij` and `h_ij=e_i e_j` permit deletion of h and
   substitution of `g_ij=e_i e_j`. The two erased helpers restore uniquely.
   This remains quadratic before the final SOS and quartic afterward. The
   nonnegativity of every term in the row-sum argument is essential.

3. **Exact Wiring memory:144→134 rows in the example.** Retained strict
   keys `Ha+t` and bounds `0≤t<H` force adjacent addresses to be nondecreasing.
   Thus `a_next−a=(1−z)(d+1)` with natural d,z forces z to be Boolean without
   its separate Boolean row. Keeping `zd=0`, the address row can be replaced
   by `a_next−a−d−1+z=0`; old minus new equals zd. There is one removed row
   per adjacent sorted record. The proof needs the actual key/time bounds;
   the isolated address equation alone does not suffice. The other report's
   distinct `difference=b(1+h)` encoding does not imply b is Boolean and
   must not receive this deletion by analogy.

Independent evidence includes573 cross-report rule contexts,573 actual
No Ghost source forms,9,422 orbit-row identities,573 wrong-loop endpoint
rejections,40 complete signed SOS corrections,2,303 local natural orbit
cases,2,187 local topology source assignments,30 zero-set maps,60 signed
topology corrections,36 memory source forms including empty event logs,
180 memory identities and10,100 adjacent-key cases. Finite enumeration
supports the displayed general arguments; it is not their replacement.

## Exact erasure

The affine stochastic lift preserves the mass/information decomposition and
strict positivity. Its tensor guards exclude common invariant lines while
leaving a common invariant hyperplane. The result is not irreducibility.
The rank identity holds for every word, including arbitrary interleavings
of guards and an empty source projection. The PCP connector is idempotent
with a nonzero empty-block factor, so adjacent connectors do not fabricate
an empty PCP solution.

The seven-state/eight-letter undecidability result is kept distinct from
the nine-state variable-alphabet many-one completeness result. The imported
small mortality bounds use the reduction convention of the
[Cassaigne–Halava–Harju–Nicolas paper](https://arxiv.org/pdf/1404.0644);
the separate ordinary halting-to-PCP interface is supported by
[Forster–Heiter–Smolka](https://arxiv.org/pdf/1711.07023). The report prints
and implements PCP-to-mortality and subsequent maps, not the full prior
halting-to-PCP compiler.

With iid full-support switching, one erasing finite block is absorbing and
occurs with a geometric waiting bound. Here existence of an erasing word,
almost-sure finite erasure and finite expected erasure coincide. This does
not extend to arbitrary infinite stochastic computations. The report's
label-output entropy is elementary; no entropy-undecidability claim follows.

The numerical full-prefix and shifted-information quartics have bijective
natural zero sets for each bounded labelled word. At n=7,k=8 their counts
are `57T→44T` witnesses and `50T+42→37T+36` residuals. The shift is paid and
its nonnegativity follows from exact column sums. The uniform-parameter
quartic is a separately proved schema, with its selected matrices and clock
counted; it is not a third implemented numerical export format. Input matrix
validity remains an explicitly stated promise.

Natural selectors are indispensable. At D=6 the matrices `[[3,2],[3,4]]`
and `[[3,1],[3,5]]` have nonzero information restrictions1 and2, so no word
erases. Signed selectors `(2,−1)` would produce restriction0. The actual
checker rejects them. The receipt records256 independent tensor-rank cases
with both numerical certificate formats and162 complete small natural
selector/prefix assignments, including duplicate labels.

## Thermal arithmetic and its repair

For a genuine natural arithmetic DAG with k source witnesses and g materialized
gates, the marker gives `m=k+g+1` modes and `r=g+2` equations. The Hamiltonian

```text
Q(n) = sum_j f_j(n)^2
H(n) = (1 + sum_i n_i) Q(n)
```

has degree at most five and `r(m+1)` displayed nonnegative terms, each on at
most four modes. Its zeros biject with source roots, retaining any multiplicity
already present among those roots. The term count is not an optimized
addition/multiplication count. Integrality gives `H>0 ⇒ H≥1+sum(n)` and
effective positive-spectrum cutoffs.

Finite zero multiplicity is correctly separated from positive-spectrum
confinement. The finite-fold equivalences do not resolve finite-fold MRDP;
padding gives the separate unconditional compactness/trace undecidability
result. The critical fugacity is a uniformly computable real. Equality to
its exact endpoint is the undecidable predicate; the real itself is not
noncomputable. The interval code pays both spatial and energy-truncation
tails and raises on resource exhaustion. Its optional exact ground-series
callback is an external promise. Four-mode support does not imply finite
local dimension or geometric locality.

The static number-operator interpretation is consistent with
[Kieu's primary squared-polynomial construction](https://arxiv.org/pdf/quant-ph/0111063).
No physical halting algorithm or autonomous universal dynamics is imported.

The public low-level builder nevertheless accepted invalid descriptors:

```python
c = Compiler(1)
z = c.add(c.variable(0), Atom('mode', 1))
f = c.finish(z, z)                 # invalid first gate: u = x+u
f.energy((0, 7, 1)) == 0
f.energy((0, 8, 1)) == 0           # two completions over the same input
```

It also accepted `Atom('const',0.5)`, producing canonical tuple `(0,0.5,1)`
and energy0.5 on natural supplied tuple `(0,0,1)`, and accepted Boolean atoms.
These refute the low-level input contract, not the theorem for natural DAGs.

The [thermal repair](thermal_exact_dag_guards.patch) validates exact atom and
gate descriptors, available earlier coordinates and parameter bounds before
simplification, zero powers or finalization. Direct `Compiled` construction
validates and snapshots consecutive topological gates. Sharing is rebuilt
from the public gate list so edits cannot preserve stale cache references.
This reference implementation now scans prior gates during assembly; worst-case
construction time can be quadratic, with no extra emitted arithmetic gates.

The7936-assertion supplied suite passes after repair, with both JSON outputs
byte-identical. The patch author's868 focused checks include219 rejected
descriptors and625 complete natural fiber tuples. The root replay independently
checks malformed descriptors,96 complete fiber tuples, snapshots,
edited gate-list sharing,400-digit input and both unchanged outputs. All six
original exported Hamiltonians are independently expanded;240 canonical and
180 arbitrary full tuples,18 exact geometric partition enclosures and three
excited boundary enclosures also pass.

Independent patch review adds496 checks, including145 malformed descriptor
rejections, six unchanged compiled exports,78 canonical evaluations and256
full supplied tuples. It also replays all7936 author assertions and verifies
both regenerated JSON files byte for byte. No patch changes were requested.

## Sandpile cubic certificates and three repaired constructors

For finite loopless undirected graphs whose components reach a sink, the
support-burning criterion is sound and complete for a proposed odometer.
Necessity uses the earliest last-toppling in each support subset; sufficiency
uses the maximal level set of the difference from the true odometer. The
earliest parallel-burning rank conditions force every auxiliary uniquely.
The directed counterexample in the report correctly excludes arbitrary
dissipative directed graphs.

The baseline has `13n+12E` natural coordinates and `14n+12E` structured
summands; the compact compiler has `10n+6E` and `10n+7E`, where E counts
distinct undirected adjacencies. Both are cubic and related by explicit
inverse zero-set maps. The two-site example changes38→26 witnesses and
40→27 summands while expanding216→324 monomials. No arithmetic-operation
saving is inferred from the coordinate counts. Weighted nonnegativity is
essential; four-square conversion gives a finite-fold degree≤6 integer
corollary, not a signed cubic with unique witnesses.

The collar and canonical-radius arguments correctly certify finite total
topplings, rather than merely finitely many topplings at each site. The
universal application uses [Cairns's periodic-plus-finite construction,
Sections5–6 and Theorem3](https://arxiv.org/html/1508.00161v2). A finite-box
certificate does not supply fixed-arity compression or an implemented
machine-to-sandpile loader. The stated single-fold boundary is an equivalence
with the representation conjecture, not its solution.

The exact eventual period is also correct. If h≥0 is nonzero on each internal
component, let c=L⁻¹h and let q be its least denominator-clearing positive
integer. Beyond the supplied full-support threshold, the endpoint repeats
every q inputs and the odometer increases by qc. Any eventual period p must
make pc integral, so q divides p. The quadratic box bound on odometer height
does not supply a computable bound on the necessary spatial radius.

Three public constructor failures bypassed these hypotheses:

1. `Graph` retained mutable adjacency and degree lists. Construct
   `Graph([[0,1],[1,0]],[2,3])`, then mutate the first off-diagonal entry to2
   and the first degree to1. The baseline accepts a complete certificate
   for odometer(2,1) at input(0,2), while legal stabilization has odometer(0,0).
   A fresh constructor rejects the mutated directed graph.
2. `PeriodicInput((4,), background=[0,0,0,0])` retained the background list.
   After constructing a valid radius0 certificate, set background[2]=2.
   The same certificate remains zero although infinitely many sites2 mod4
   are initially unstable. The interior/collar only sees residues0,1,3.
3. Direct `SpatialInstance` construction bypassed the checked builder.
   A one-dimensional background1 with height2 at site2 accepts a manually
   supplied radius0/minimum0 instance with its radius0 graph and collar.
   Its certificate is zero while a legal wave at sites2,3,4,… never ends.
   The distant finite defect lies outside the tested collar.

The [sandpile repair](sandpile_immutable_input_guards.patch) snapshots all
graph and periodic-input containers, including nested override records.
The direct spatial constructor checks the source/graph classes, radius and
defect inclusion, exact site order, canonical box graph and entire collar,
and snapshots its coordinate arrays. All three original suites pass; nine
receipts and exported example files remain byte-identical.

The independent subset-burning oracle checked66252 candidate odometers on
43 graphs, with1065 complete zero-set round trips. Further checks cover109
eventual-period pairs on24 weighted graphs. The original suites additionally
cover86975 odometer candidates,7660 ranks,20800 comparison tuples,37179
five-way tuples,275 compact round trips and103 spatial input/box pairs.
The patch author's354 focused checks and the independent repair replay cover
all three failures and immutable valid inputs.

## Replay, patch status and continuation

Run from the repository root with Python and SymPy available:

```sh
python Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/incoming_substrate_review_1977e6ea6.py
```

Default execution recomputes and compares the receipt; `--write` regenerates
it. Patch checks also require the standard `patch` executable. Repairs are
applied to exact archive sources in temporary directories with fuzz disabled.
Only runtime duration and Python-version fields are removed from verifier
stdout comparisons; mathematical counts, outputs and source hashes remain.

The archives remain historical originals. Apply each patch with `patch -p1`
from its package root (`sandpile_diophantine_certificates` or
`thermal_arithmetic`). No maintained imported copies existed at review time;
the patches and complete replays are the delivered repairs. This status must
be updated if a subsequent intake installs and patches those sources.

The immediately useful next work is to turn the three checked wiring
reductions into guarded complete rewritten packets with explicit operation
ledgers, then account for schedule selection and memory jointly. Exact erasure's
shifted mass coordinates and sandpile's support-burning ranks are also useful
compression mechanisms, but neither currently removes its unbounded horizon
or spatial-arity obligation.
