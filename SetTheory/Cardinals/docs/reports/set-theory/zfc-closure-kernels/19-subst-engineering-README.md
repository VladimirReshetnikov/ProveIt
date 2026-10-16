# Offline engineering artifacts

This directory reproduces a **268-working-state compiler control** while
retaining all eight original logical axiom rows, equality machinery, original
rho6, and the original base-four codec. It improves the supplied full-program
269-state Re-Pair experiment by one state. It is above the verified 253-state
benchmark and is **not a newly proved ZFC-consistency machine**.

The selected numeric table is
`artifacts/full_logic_best.tm`: 268 working states, 536 transitions, start 0,
and terminal target 268. Its SHA-256 is:

```text
77f88b15383b13846090a31f3780673daf57c8b66fed2b9e7de252686901a61d
```

## Quick commands

Use Python 3.10 or newer, with no extra packages. From this directory:

```sh
python -B verify.py
python -B reproduce.py --output /tmp/zfc-engineering268
```

The first command checks the pinned inputs and stored artifacts, independently
verifies all 4,533 pairs of the register-machine certificate, checks every
numeric table row, and runs the PSC identity-model regression. It does not
import the compiler or grammar generator for the certificate or table checks.

The second command regenerates the selected recipe, compares the numeric and
named tables, label map, two DAGs and certificate byte-for-byte with the stored
artifacts, and then performs the independent checks. Its default does not run
a search. It took about two seconds in the delivery environment. Omitting
`--output` uses a temporary directory and removes regenerated files afterward.
No network, Git checkout, Lean, Rocq/Coq, or external Python package is needed.
The `-B` option avoids creating bytecode caches beside the pinned inputs;
do not use `-O`, since the finite verifiers use assertions.

To repeat the larger, optional searches:

```sh
python -B reproduce.py --output /tmp/zfc-engineering268-grid --full-grid
python -B reproduce.py --output /tmp/zfc-engineering268-psc --psc-controls
```

`--full-grid` repeats the 53,760-choice conjunction/grammar family.
`--psc-controls` repeats four 2,048-choice PSC comparisons, checks their
selected recipes and table hashes against the stored results, and retains
the generated control tables in the selected output directory. These two
options may be combined.

## What changed

Write the original theory factors as C, G, Vr and Ve. The selected source
commutes the power-container/transitivity conjuncts inside C, commutes the
collection/support conjuncts inside G, and uses the outer association

```text
Vr AND ((Ve AND C*) AND G*)
```

The eight logical rows and their parameters are unchanged. Relative
conjunction `And_F(A,B) = ((A -> (B -> F)) -> F)` has Boolean value
`F or (A and B)`, so the used commutations and associations are implicational
tautologies. The original logical rules lift these equivalences through the
surrounding quantifiers.

The supplied prior report's weighted Re-Pair algorithm is then used with
seed 341 and exponent 4, retaining the original closed macro 161 before
grammar search. The new contribution is this full-logic conjunction layout
and its 268-state result; Re-Pair and the certificate architecture are prior
work and are explicitly attributed in `NOTICE.txt`.

## Artifacts and provenance

`artifacts/` contains the total/named selected table, label map, reference and
candidate DAGs, finite RM certificate, original search evidence, independent
checks, PSC comparison results, and the PSC identity-model result.
`ARTIFACT_SHA256.json` preserves hashes of these delivered records.

`vendor/` is a minimal, unchanged, repo-shaped input snapshot. Its paths are
needed because the ProveIt recovery helper locates its upstream files from
its own source location. `PINNED_INPUTS.json` covers all 19 vendor files.
This is not a complete ProveIt repository or formal-proof distribution.

`full_logic_search.py` is adapted only to use bundled default inputs and
generate the selected recipe immediately by default. The exact historical
search source corresponding to the source hash in the original search JSON
is retained as `provenance/full_logic_search_20261016.py`. Its original
53,760-case search is available with `--conjunction-grid
--original-baseline --iterations 0` in the packaged version.

`full_logic_psc_controls.py`, `psc_identity_model.py`, the independent
certificate wrapper, and all vendor files retain their original bytes.
`provenance/offline_reproduction.json` records the delivery-time offline
regeneration. Results that contain elapsed times or the adapted generator's
hash need not be byte-identical to historical research records; the six
selected machine/certificate artifacts are compared exactly.

## Verification boundary

The certificate relates the candidate register program to a separately
re-emitted program for exactly the revised axiom word. It checks 2,601
increments, 1,931 decrement tests and one halt, including both decrement
branches. It is finite executable evidence, not a Lean/Rocq kernel theorem
and not a proof of the complete binary Wade interpreter.

The public backend's sole undefined transition, `1.inc/read1`, is explicitly
totalized by writing 1, moving right and halting. This adds no working state
and uses the stated partial-transition halting convention.

The PSC identity regression interprets quantifier operators as identity and
sets `R(i,j)` true exactly when `i >= 2` and `j = 0`. It is a semantics of the
incomplete coded calculus, not an ordinary first-order membership model.
The prior supplied report already proved the broader finite-sort obstruction;
this small regression is a simpler PSC-only certificate.

See `compiler_findings.md` for the original research handoff. Its scratch-path
commands describe that research session; the commands above are the portable
delivery commands. License and attribution boundaries are in `NOTICE.txt`.
