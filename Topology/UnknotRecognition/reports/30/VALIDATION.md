# Validation and evidence record

This report accompanies **Exact binary boundary tensors and compressed
transport for unknot recognition**, 8 October 2026.

## Final maintained test gate

**714 tests passed in 105.729 seconds, with no failures, errors, or skips.**
The process exited with code 0. The recorded environment is Python 3.12.14
on Linux, with Regina 7.4.1 installed.

Command, from the maintained `fast/` directory:

```sh
python -B -u -m unittest discover -s tests -v
```

The exact output is `validation/full_tests_final.log`. This gate includes
the final supplied-order policy, checked Jones normalization, near-prefix
matcher, boundary transport, and corrected subprocess wrapper. It has 27
more test methods than the baseline's 687-method suite; individual methods
also contain many parameterized or exhaustive comparisons.

## Independent mathematical and implementation checks

| Component | Evidence | Scope |
|---|---|---|
| Binary Jones tensors | 140 whole-cube polynomial comparisons | Real knots, mirrors, different orders and outer faces; oracle does not use the turning tensor |
| Turning and phase conventions | All oriented smoothing circles on small examples; 20 exact random vertex gauges | Face equations, circle turning, gauge independence, self-loop and multigraph handling |
| Integer reconstruction | 180 bounded signed Laurent polynomials | Extreme coefficients/degrees, exact normalization, forged metadata, large integers, cancellation |
| New matcher | 500 periodic-prefix and 450 near-prefix LCS comparisons | Literal oracles, genuine prefix improvements, exponentially long grammar, work/node/cancellation behavior |
| Dihedral boundary transport | 817 presentations; 650,992 queries; 12,496 transported-value checks | Literal generator permutations and equivariance propagation, independent of gcd/CRT formulas |
| Cyclic canonical keys | 285 presentations; 6,356 queries; 1,034 literal classes; 44,790 witness checks | Literal isomorphism classes and transport, without using production canonicalization formulas |

The code and raw results for the last two rows are in
`fast/boundary_transport_research/`. The tensor and matcher focused checks
are included in the maintained test suite. Their source and evidence are
also described in `fast/spin_jones_research/README.md` and
`fast/near_prefix_research/RESULTS.md`.

Independent proof reviews checked the face-cochain construction, binary
tensor identity, one-phase lemma, faithful normalization and bit bounds,
the near-prefix alignment and periodicity reductions, and the covering
transport and canonical-count formulas. These are written proofs and
independently organized computational checks, not proof-assistant
formalizations or external peer-review certification.

## Controlled performance evidence

The initial Jones audit records **490 measured queries and 70 excluded
warmups**, over fourteen inputs, five arms, and seven shuffled rounds.
Every arm requests the full polynomial. The ordinary scope includes order
preparation; the matched-order scope uses one common externally prepared
certified order. An A/A arm repeats the baseline operation.

The 144-crossing grid has ordinary medians 313.118 ms (Potts) and 186.080 ms
(spin), with median paired ratio 1.719. Matched-order medians are
274.913/145.532 ms, with paired ratio 1.814. Peak states decrease 877 to 240,
and transitions 48,386 to 32,098. The 196-crossing grid completes 7/7 spin
queries; both Potts arms reach the state allowance in 7/7. That is a capacity
result, with no completed-time speedup ratio. A 254-crossing tree medial
regresses from 66.662 to 305.133 ms. Grid diagrams have independent
descending certificates; other large inputs are checked for agreement
among completed arms. These are not whole-recognition timings on hard knots.

An initial supplied-order policy defect is preserved, with its source and
raw limits. The separate correction follow-up records **35 measurements
and five warmups**, all complete. On the shuffled 64-crossing grid, ordinary
Potts/spin medians are 19.293/14.625 ms, while matched-order medians are
3.963/10.790 ms. The ordinary gain on this example comes from ordering;
the matched contraction still loses. The recorded source predates the
additional decoder-normalization consistency check. Its exact bytes are
preserved, and the measurements are not relabeled as final-source timings.

The matching audit records **225 whole-knot queries** and **280 kernel
measurements**, with five measured rounds and an excluded warmup. All
whole-knot queries return UNKNOT with identical per-case certificate
digests across arms, but none activates the new branch. Hence no completed
knot-recognition speedup is attributed to this matcher. On the equal-bigram
`N=2**500` kernel, baseline and generic-LCE ablation reach the two-million
work allowance, while the new query completes in 92.580 ms. The positive-
shift query completes in 3.515 ms. Negative controls preserve work counts.

Boundary timings are local prepared-query measurements. For 1,048,576
sheets, a literal orbit-label-and-root scan takes 0.761936 seconds; the
compressed median over eleven prepared calls is 5.929 microseconds,
excluding cover preparation. A 58,883-bit sheet count takes 4.245 ms to
prepare and 15.027 ms per median prepared two-constraint query. These
measurements do not time a hierarchy constructor or a complete recognizer.

All raw status values and source hashes are retained. Work/state limits
are incomplete queries, never completed-time denominators. Median paired
ratios can differ from ratios of displayed arm medians. Timing noise in
the shared environment is visible in A/A controls and is not evidence of
an algorithmic improvement.

## Baseline subprocess defect and correction

The initial integrated run contains 712 tests and one error. It is retained
as `validation/full_tests.log` and is **not** reported as a passing run.
The failing unchanged test deliberately delays reading a 500,000-byte
stdin payload. It fails identically in the pinned baseline and the then-
current source on the recorded Python 3.12.14 runtime.

The first short `communicate` call writes 65,536 bytes before timing out.
Subsequent `communicate(None)` calls in this runtime fail to register
stdin for further writing, although unsent input remains. The input
offset stays fixed, the child waits for more data or EOF, and the
three-second allowance expires. A single-call control sends all data
correctly in 0.135 seconds. `normal_surface_diagnosis.json` contains
source-hash equality with the pinned baseline and the observed input
offsets. The matching isolated logs and a runtime-source excerpt are
retained.

The final wrapper calls `communicate(payload)` once in an owned thread,
while the main thread polls completion at intervals of at most 50 ms.
On cancellation or error it kills/reaps the direct worker, joins the
communication thread, and closes all streams. Thread-start failure is
an inconclusive worker failure; caller cancellation exceptions propagate.
The unchanged large-payload test and the new blocked-payload cancellation
test pass. The final focused normal-surface gate passes all nine methods
in 2.841 seconds; the final full suite also passes them.

The direct worker must not leave descendants inheriting these pipes.
The maintained worker satisfies this model. The correction was exercised
on Linux; it is not a general process-tree supervisor. Its optional
Regina verdict retains the original external-engine trust label.

`validation/reproduce_pipe_defect.py` is a portable replay using the
archived before-source and the corrected package. The old result can
differ on another Python runtime. The original diagnostic script is
preserved as provenance and retains its original workspace paths.
One early incomplete tool capture is retained separately and is not
counted as a passing run.

## Integration and packaging checks

The patch is against:

```text
8a95834940cf77cdab1b39571ffc102ca8b6bede
```

It passes `git diff --check`, `git apply --check`, and actual application
to a fresh extraction of that baseline. **All 409 tracked or newly added
maintained files match the working source byte-for-byte after applying
the patch.** The exact patch hash and outcomes are in
`validation/integration_check.json`.

The standalone package was checked for imports of the new kernels and
required historical references, full-polynomial CLI output, agreement
with a small independent Jones oracle, and automatic use of the checked
archived LCS baseline when git is absent. A small canonical audit also
checks the packaged driver's path discovery. See `package_smoke.json`
and `packaged_canonical_audit.json` under `validation/`.

The full suite was run once on the final maintained source. It was not
needlessly rerun after byte-for-byte packaging. The final manifest checks
every delivered artifact, and `verify.py` exposes optional focused or
complete replay commands for the recipient.

## Document verification

The article is **37 pages**. Both modular and standalone TeX compile
successfully with pdfLaTeX/latexmk. Their extracted page text is identical.
All references resolve, there are no overfull or underfull boxes in the
final LaTeX log, and no extracted word extends outside a page. Pages were
rendered and visually inspected, including the turning-convention figure,
proof displays, performance tables, and final integration discussion.

`validation/document_build_check.json` records the PDF hash, page count,
text equality, and boundary/reference checks. The final build log is
included. PDF metadata timestamps can differ on recompilation; content
and file hashes in this archive refer to the delivered bytes.

## Conclusions supported by this evidence

The proofs and code establish a stronger implemented full-Jones bound,
an exact specialized compressed-word improvement, and exact boundary
transport and local marking-count results. The measurements establish
selected local gains, capacity improvements, and regressions. They do
not establish faster whole recognition on a hard-knot corpus or a
general quasi-polynomial unknot-recognition algorithm. The article's
research agenda identifies the global state, encoding, continuation,
and unary-work obligations that remain.
