# Runtime searches and source-restricted affine checking

No machine with fewer than 246 states was found by the searches in this
directory. The completed finite domains below all have zero survivors. The
positive reusable result is a source-aware extension of the affine box oracle:
an additional decrement of a register proved zero may be treated as the exact
identity on the complete encoded file. The proof and implementation retain all
other register values, spares, head position, and gap effects.

The five program layouts are applications of the previously published source27
reassociation transformations to the Context246 runtime. The reassociations
themselves are prior work. `reference/context246` is the unchanged baseline;
`candidates/layoutN/program.json` and `machine_old.tm` are the new source sites
and retained 246-state tables. All state numbers in this directory are the old
labels: dispatcher 96, blank start 95, halt 254, contextual pulse state 255.
New decoder labels can exceed 255; the merger uses 512-state arrays and
1024-bit row footprints to accommodate them.

## Completed domains

### Exact instruction merger screens

For each unordered pair of distinct working states `a < b`, independently select
the original row of `a` or `b` as the provider for each read symbol. Redirect all
retained targets `b` to `a`, and use the merged dispatcher if 96 was removed.
The domain has `4 * binomial(246, 2) = 120,540` recipes per table. These recipes
need not be distinct resulting machines.

Every literal fixture compares the complete tape and final head at dispatcher
96, or requires a halt for a CH instruction. Each fixture permits at most 20,000
literal moves within tape cells -64 through 447. The baseline preflight passed
all fixtures, used all 492 literal rows, and needed at most 558 moves. The
candidate simulator uses baseline footprints to select quick probes, followed
by every affected fixture. An unaffected deterministic baseline path cannot
observe the changed state or an incoming redirection and therefore is unchanged.

Three distinct input domains were screened:

| Domain | Concrete cases per table | Register assumptions |
|---|---:|---|
| `unrestricted` | 8,391 | One arbitrary sample vector per source guard; spares `[0,2]` |
| `guards` | 8,385 | The same vectors, with six impossible source guards removed |
| `product` | 33,540 | Four vectors per feasible guard, all nine registers satisfying the certified product masks |

The word `unrestricted` names the source guard domain; it does **not** mean that
all numerical vectors were enumerated. The product fixtures include minimum
and maximum allowed categories plus two varied category assignments. They
distinguish value 1 from values at least 2 and include value 3. Every fixture
respects its own CD guard. They do not enumerate all combinations of categories,
all natural values within a category, all gaps, or all spare lists.

Exactly 5,327 of the old 8,385 guard-restricted vectors violate at least one of
the product masks. A failure on those vectors cannot reject a transformation
whose correctness is claimed only on the complete product invariant. The new
product-domain runs resolve this mismatch for the declared finite witnesses.

| Layout | Unrestricted recipes | Guard-restricted recipes | Product-restricted recipes | Survivors |
|---|---:|---:|---:|---:|
| Baseline | Prior work, not repeated here | 120,540 | 120,540 | 0 |
| 0 | 120,540 | 120,540 | 120,540 | 0 |
| 233 | 120,540 | 120,540 | 120,540 | 0 |
| 235 | 120,540 | 120,540 | 120,540 | 0 |
| 236 | 120,540 | 120,540 | 120,540 | 0 |
| 237 | 120,540 | 120,540 | 120,540 | 0 |

This is 17 completed table/domain screens, with 2,049,180 recipe evaluations
across domains. A table's mutation recipes are repeated under different input
assumptions, so this number is not a count of distinct machines. Exact counts,
probe counts, baseline bounds, and fixture hashes are recorded in
`verification/runtime/provider-merges.json` and `fixture-manifest.json`.

The separate synthesized-row fusion family lives in `code/fusion`; its counts
must not be confused with this provider-only family.

### Protected affine folds on the five new layouts

The symbolic search preserves all 42 rows used by the inherited marking and
register-operation induction proofs, including their targets, and keeps
dispatcher 96. A uniform fold removes one eligible state and redirects its
incoming transitions. A mixed fold additionally copies one of the removed
state's rows into the survivor. Duplicate orientations with interchangeable
eligible survivors are suppressed as shown in `search_folds.py`.

The completed scope requires at least one state of the pair to have a changed
decoder row relative to the Context246 table. The unchanged parts had already
been searched in the prior archive. Every new baseline passes all 8,391 affine
guard cases. Each affected candidate case has a budget of 1,500 symbolic rules;
survivors would then be checked on every case.

| Layout | Uniform recipes | Mixed recipes | Symbolic case checks | Survivors |
|---|---:|---:|---:|---:|
| 0 | 1,611 | 1,332 | 19,459 | 0 |
| 233 | 2,527 | 2,208 | 5,296 | 0 |
| 235 | 1,150 | 888 | 2,131 | 0 |
| 236 | 1,150 | 890 | 2,191 | 0 |
| 237 | 687 | 446 | 1,207 | 0 |
| Total | 7,125 | 5,764 | 30,284 | 0 |

All 12,889 recipes failed before a full-survivor recheck was required. The
failure categories are unsupported affine configuration, exhausted symbolic
fuel, or missing transition. These are limitations of the specified checker;
they are not proofs of semantic inequivalence for every candidate. See
`verification/runtime/protected-folds.json` for all counts.

### Removing the contextual pulse state 255

Two broader families were completed in addition to earlier searches.

1. `search_pulse_families.py` deletes state 255 and varies 21 specified sets of
   rows. Every set includes `(75,0)` and explores changes to increment-entry,
   seek, rollback, or return rows. Eight families have two holes, ten have three,
   and three have four. Each hole has 100 actions: either write bit, either move,
   and one of the 25 explicitly listed runtime targets. The sum of domain sizes
   is `8*100^2 + 10*100^3 + 3*100^4 = 310,080,000`. Lazy execution covers these
   domains with 2,606,985 partial trace checks. All 21 have zero survivors on the
   48 exact complete-tape fixtures, including sampled nonhomogeneous spare
   lists. Allowed endpoint ticks are 1 through 249; tick 250 and later are
   outside this experiment.

2. `search_any_aux.cpp` deletes state 255, replaces `(75,0)`, and permits an
   arbitrary second retained row to change. There are 489 auxiliary rows and
   980 actions per hole: either write bit, either move, and any of the 245
   retained working targets. Halt is excluded as a target. The domain has
   `489*980^2 = 469,635,600` assignments. All have zero survivors on 58 direct
   register-operation fixtures with at most 1,000 moves each. The nine primary
   registers are compared exactly; the result must have at least one spare and
   every spare must encode 1, but the spare count may change. Inputs contain
   only spares encoding 1. This is deliberately a different, weaker spare
   contract than the preceding exact-spare family. The literal tape buffer is
   -512 through 1535. The screen also rejects an outward blank-ray self-loop,
   which can never return to the macro endpoint.

An unknown row is intercepted before use. Successful earlier traces therefore
do not depend on its later assignment. A failure before encountering the
unassigned auxiliary row rejects every completion at once; the complete recipe
count is still included. All 489 row groups and their 960,400 assignments are
recorded in `verification/runtime/any-auxiliary-row.json`. Runtime timestamps
are omitted from the portable records.

These domains overlap each other and earlier work. Their sums are assignment
counts, not a lower bound on the number of states and not distinct-machine
counts.

## Source invariants and the additional affine rule

`product_verifier.py` reparses the exact source SHA-256
`1fbc30fcf82a1442ed88d1a1dde412630a431d32a7265d22bdf8517bffe01746`, reconstructs
the full guarded control flow, and checks the supplied product invariant without
trusting its generator. The abstract categories are `{0}`, `{1}`, and `{2,3,...}`.
In particular, a positive decrement of the third category has both possible
output categories `{1}` and `{2,3,...}`; it is not treated as remaining positive
at least 2.

The initial premise is **T=W=H=0 at the source root**, with N,A,D,X,Y,L arbitrary.
It proves 6,456 reachable abstract sites, 8,385 feasible guards, and 8,384
nonhalting abstract edges. The excluded zero-based full-guard indices are
8202,8203,8204,8358,8359,8360. CD cases are ordered zero then positive. The two
positive CD guards are at leaf indices 6316 (X) and 6434 (T); the next two leaves
in each corresponding block are unreachable.

`admissible_guards.py` verifies equality of every original/new guarded edge by
in-order source leaf index, operation, affected register, guard, and successor.
It then rechecks the product closure against each new layout. Carry residues
retain their cleared trailing zeros, and decoding rejects discarded nonzero
suffix bits. Control B/C arguments may differ across source reassociations,
but their decoded successors must agree. Independent reconstruction and actual
blank-prefix replays are provided separately in `code/proof` and
`verification/proof`.

The actual certified blank roots for layouts 0 and 233 have logical values
`[3,0,0,0,3,0,0,0,0]`, satisfying the invariant premise. The premise does not claim
consistency calibration for every arbitrary register vector it permits. A
product-admissible vector may still be unreachable because the certificate
forgets correlations. Consequently a negative product-domain screen rules out
correctness on its declared witness domain, not correctness restricted to the
actual execution alone.

`affine_checker.py` optionally intersects the source masks with the current CD
guard and uses the exact physical register permutation. If a marked register
is proved zero, state95 may apply the inherited universal zero-decrement macro,
returning to state112 with an unchanged full box and no gap growth. A mark is
allowed only before a nonempty register effect, so repeated extra zero tests
preserve the masks. After an increment or positive decrement, the box state
prevents another mark. The existing 42 macro-support rows remain protected.

`known_zero_oracle.tex` gives the compositional soundness argument. This is an
ordinary symbolic checker and a mathematical proof extension, not a new
proof-assistant kernel theorem. It keeps an exact complete-file endpoint. The
four finite representatives per guard used by the merger are a separate
rejection method and cannot substitute for the all-parameter box proof.

## Reproduction

Run commands from the archive root. Python 3.10 or later and a C++17 compiler
are needed; the auxiliary-row search additionally uses OpenMP when available.
Do not run Python with `-O`, because assertions implement verification gates.
Large generated fixtures and compiled binaries are intentionally omitted.

Quick source and affine checks:

```sh
python code/runtime/admissible_guards.py
python code/runtime/check_affine.py --domain product
python code/runtime/search_pulse_families.py --baseline-only
```

Reproduce the five strict protected fold domains:

```sh
python code/runtime/search_folds.py 0 233 235 236 237 --output-dir /tmp/zfc-runtime-folds
```

The command supports `--domain product` for future use of the extra-known-zero
rule, and `--all-pairs` to remove the changed-state restriction. Those broader
symbolic domains are **not** included in the completed fold counts above.

Reproduce all 17 provider-row merger screens while streaming one generated
fixture at a time to the C++ process, without writing the large fixture to disk:

```sh
python code/runtime/run_provider_merges.py --work-dir /tmp/zfc-runtime-merges
```

For an individual corpus:

```sh
python code/runtime/make_merge_cases.py 233 --domain product --output /tmp/layout233-product/merge-cases.txt
```

To regenerate the exact historical directory names consumed by the separate
independent fixture audit:

```sh
python code/runtime/regenerate_fixtures.py --domains unrestricted guards --output-dir /tmp/zfc-runtime-fixtures
python code/proof/audit_guard_transport.py --fixtures-root /tmp/zfc-runtime-fixtures --baseline-fixtures /tmp/zfc-runtime-fixtures/baseline_merges/merge-cases.txt
```

Complete pulse families:

```sh
python code/runtime/search_pulse_families.py --output /tmp/zfc-pulse-families.json
c++ -O3 -std=c++17 -fopenmp code/runtime/search_any_aux.cpp -o /tmp/zfc-any-aux
/tmp/zfc-any-aux reference/context246/machine/zfc_prefix246_old.tm > /tmp/zfc-any-aux.log
```

Without OpenMP the auxiliary search may be compiled without `-fopenmp`; it uses
the same domains in one thread. Output group ordering and elapsed times can
vary. Compare exact recipe counts, eligible row groups, survivor counts, and
fixture hashes rather than timestamps or group order. The C++ quick-probe order
uses a fixed seed, but standard-library shuffle implementation differences may
change the number passing probes while leaving the completed domains unchanged.

## Attribution and proof boundary

The source and foundational machines derive from Jeff's ZF-254 work and the
subsequent ProveIt research chain, including the attributed permutation and
Context246 constructions. The unchanged baseline contains its own source
attributions, prior notices, and `sources/LICENSE.ProveIt`.

The merger is adapted from the prior
`zfc-beyond246/context/merge_search.cpp`; pulse primitives and the product
certificate checker derive from its `alternative/search_pulse.py` and
`alternative/verify_invariant.py`; the auxiliary screen extends
`audit/search_flexible_spares.cpp`. Protected folds adapt
`zfc-below246/experiments/decoder/fold_search246.py`. These exact research
archives were already present in the user-supplied ProveIt incoming material.
This archive adds the declared runtime search domains, their application to the
five Context246 layouts, exact invariant transport, product-admissible fixture
generation, and the additional known-zero affine rule.

All finite and symbolic failure claims are explicitly bounded above. No result
here is a 246-state lower bound, a proof of nonhalting, a formal ZFC consistency
proof, or a complete certification of a machine below 246 states. Any future
survivor still needs its uniform simulation proof, exact blank bootstrap,
source calibration, and the associated formalization steps.
