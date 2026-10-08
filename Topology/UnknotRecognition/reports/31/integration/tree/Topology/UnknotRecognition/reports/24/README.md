# Topology in Three Records and Bidirectional Survivor Transfer

## Two exact compression kernels for unknot recognition

This research continuation develops two proved compression algorithms, supplies
their implementations, and evaluates their costs against the existing ProveIt
scanner. Read the [article PDF](article/unknot_compression_kernels.pdf) for the
complete statements, proofs, experiments, and research agenda. The
[LaTeX source](article/unknot_compression_kernels.tex) is modular and buildable.

The audited baseline is
[ProveIt commit 9cec5275f2d2113d0a784cedf156460829b61489](https://github.com/VladimirReshetnikov/ProveIt/tree/9cec5275f2d2113d0a784cedf156460829b61489/Topology/UnknotRecognition).
The new results are local structural and algorithmic improvements.
**Unrestricted quasi-polynomial unknot recognition remains open in this work.**
The default production reducer remains `standard`.

## What is proved

**Dihedral surface covers admit a sharp three-type classification.** Given a
valid covering presentation of a compact connected surface with nonempty
boundary, with monodromy `x -> ±x + a mod W` and binary-encoded `W`, the
algorithm describes all connected components using at most three
component-family records. It computes the exact number of covering-isomorphism
types, also at most three; this bound is sharp even for an orientable base.
Records include multiplicities, covering degrees, orientability, genus or
crosscaps, Euler characteristics, and boundary-lift data. Named component and
boundary queries do not expand the sheets. Runtime is polynomial in the
presentation's bit length. Extracting this presentation from an embedded normal
surface, and handling arbitrary external attachments, remain separate problems.

**Survivor transfer admits exact pruning and direction choice.** In an allocated
quantum-graded complex, the algorithm retains only scalar-homotopy/radical paths
that connect scalar survivors, then accumulates forward or backward per
component. It preserves the entire transferred differential. Sparse scalar
components and Boolean reachability further reduce setup costs. On an explicit
fixed-algebra family with `R` sources and `M` shared branches, the complete
stage takes `O((R+M) log(R+M+2))` word operations and `O(R+M)` words, whereas
the inherited forward transfer requires `Ω(RM)` coefficient propagations.
For odd `M`, the family has a nonzero output differential. Its realization by knot scan
prefixes is unproved. This separation is relative to the inherited forward
transfer; ordinary sparse cancellation already handles the family efficiently.

The perturbation formula and preceding quantum-triangular transfer prototype
are explicitly credited as inherited work. The contribution is their exact
support, direction, and representation refinement.

## Evidence, including the negative results

At `R=M=255`, radical-edge propagation attempts fall from **130,305 to 765**.
The recorded complete reduction was approximately **28.4 times faster than
the inherited forward transfer**, while the ordinary sparse reducer remained
faster. The same stage has 768 original objects, 512 scalar components, no
nontrivial dense scalar blocks, and 768 sparse scalar-map indices, compared
with 164,735 packed bits in the inherited representation. These are exact
representation counts, not measurements of Python heap memory.

The six actual-diagram benchmarks give a different practical conclusion:
full corridor reduction was **2.1–10.7 times slower than the standard sparse
scanner**. The adaptive option switched zero times, and the narrow compressed
setup follow-up established no reliable timing improvement. The stronger
grading-support certificate added **zero shortcuts** over the existing
degree-gap certificate: both accepted 196 of 639 stages across 72 diagrams.
These outcomes argue for retaining the current default.

The coordinated timing runs use seven shuffled paired warm rounds, fresh
states, recorded batch sizes, and unchanged standard/control arms. Actual
scans include reduction setup; synthetic measurements include the complete
reduction stage but exclude input construction. Controls still exhibit
substantial timing noise. The article separates these observations from
proved operation counts.

Correctness evidence includes **268 scanner tests**, **13,846 expanded-sheet
topology comparisons** in ten covering-test groups, and **3,885 entrywise
transfer comparisons** over 555 prefixes of 80 actual diagrams. Every prefix
also checks the eight special-contraction identities. General correctness
claims rest on the proofs, supported by these finite checks.

## Package map

| Path | Contents |
| --- | --- |
| `article/` | PDF, LaTeX sections, bibliography, figure sources, build script |
| `fast/` | Runnable scanner snapshot, additions, tests, audits, benchmark drivers and recorded JSON |
| `reference/` | Frozen preceding forward-transfer and first corridor implementations |
| `dihedral_covers/` | Standalone covering kernel, schema, examples and independent tests |
| `verification/` | Independent transfer audit, recorded verification, logs and experiment notes |
| `integration/` | Reviewable scanner patch and repository integration instructions |
| `INTEGRATION.md` | Exact APIs, CLI choices, compatibility and resource semantics |
| `PROVENANCE.json`, `SHA256_MANIFEST.json` | Source lineage and file hashes |

Keep `fast/` and `reference/` as sibling directories: historical comparisons
and several tests use the frozen modules.

## Build, verify and reproduce

Python 3.10 or later is required; the scanner and verification tools use the
standard library. From the unpacked package root:

```sh
python verify.py --output ../verification_local.json
sh article/build.sh
```

Verification checks archive hashes, runs the suites and independent audits
in a temporary copy, and compares deterministic results. The manuscript build
requires pdfLaTeX, BibTeX and the packages listed in its preamble. Matplotlib
is needed only to regenerate the included figure; its PDF is already supplied.

Replay the two recorded timing experiments with new output filenames:

```sh
python reproduce_benchmarks.py --experiment baseline \
  --output ../baseline_local.json
python reproduce_benchmarks.py --experiment compressed \
  --output ../compressed_local.json
```

The wrapper checks source hashes and restores historical code only inside a
temporary copy. Add `--prepare-only` to check this preparation without running
timings. Pause competing CPU-intensive work for measurements. Raw samples,
operation counters, seeds, crossing orders and environment details are in
`fast/results/`; elapsed times are not expected to reproduce exactly.

## Integration and next research

Review `integration/` before applying the patch to the pinned baseline.
[INTEGRATION.md](INTEGRATION.md) documents the opt-in `corridor` and
`corridor-adaptive` modes and the direct sparse-component/port-count controls.
Resource exhaustion remains `UNKNOWN` in recognition. Unsupported combinations,
including corridor reduction with homological windows, are rejected.

The article's **14-question research agenda** gives explicit success criteria
for knot realization, adaptive switching, sparse scalar bases, typed pruning,
exact window integration, survivor multiplicity bounds, recognition-specific
quotients, internal transfer interfaces, geometric presentation extraction,
attachments and hierarchy search. The outstanding global obstruction is a
proved bound on necessary intermediate information or hierarchy states;
compressing either local kernel alone does not supply it.
