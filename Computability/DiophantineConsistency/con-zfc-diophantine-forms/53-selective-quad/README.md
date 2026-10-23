# Selective quadratic encodings for Con(ZFC)

Read report.pdf (32 pages) and its editable report.tex. This package reviews
ProveIt through arithmetic pin 124c07c0b77a9e20e84676514d8b1ff78536ea3f,
with a separately identified formal-status update at
59e9d4d22b34abdcc27f378796b9bfa28c6f1cc2.

## Main explicit equations

All operation counts charge binary +, -, and multiplication, including
scalar multiplication and fixed-power evaluation. Domains matter.

- 10 unrestricted integers: exact degree 21,111,400, 659 operations.
  Uses Sun's 2026 bridge; improves source40's 237,520,456 / 782.
- 9 positive integers: exact degree 7,344,328, 738 operations.
  Natural version: 744 operations. A second positive form trades degree
  12,023,320 for 734 operations (740 on naturals).
- 13 unrestricted integers, Jones route without Sun 2026: exact degree
  57,866,184, 759 operations. The unseeded comparator is 71,382,096 / 770.
- 11 positive integers: degree 958 / 117 operations, or 962 / 115.
  Shifted two-equation systems have degrees (2,956) / 112 operations
  or (2,960) / 110.
- 15 positive integers: degree 80 / 72 operations, a minor short-circuit
  tradeoff. The included 56 / 74 form is a historical point, not new.

Each validated equation has a mathematical equivalence proof, formalizable
in ZFC, between its lack of solutions in the stated domain and Con(ZFC).
No consistency decision, global optimum, lower unknown-count theorem or
new end-to-end Lean/Rocq certificate is claimed. Recent external Lean
executable-equation results concern a different construction; their
current status is distinguished in the report.

## Structural changes

1. Isolate only the 71 monomials occurring in the quadratic source, while
   checking them against all 528 possible quadratic expansion monomials.
2. Allow reversed source intervals to overlap if no target is contaminated.
   All 71,808 interactions are checked; maximum target drops 35,178 -> 5,190.
3. Replace dense carry padding by a single bit at each target, with a
   proof permitting signed borrows.
4. Calibrate the binomial threshold to the actual mask population. For
   Jones, tune the block length to make that threshold a polynomial square.
5. Seed a positivity guard with an existing radicand to replace a three-root
   norm by a two-root norm.
6. Absorb a Pell index quotient with denominator Y instead of XY, and
   reconstruct the stronger divisibility after a short-index argument.

The 67-operation equation and 59-operation system remain unbeaten on their
operation metric. The previous twelve-positive degree901/112 form remains
a distinct point. No native coefficient-byte improvement is claimed here.

## Fixed coefficients and dependencies

Every active family uses the SAME complete source31 Wang943 121x8801 tuple:
B_native=2^1064921; beta=B_native-1; K0=K; MC=MC; MF=MF_source already shifted.
Its four uncompressed binary payloads total 533,099 bytes. Other packages'
smaller tuples are not spliced into this one. All fixed leaves have explicit
recipes or fixed power-of-two values; no consistency-dependent parameter
is left unspecified. Component binding files authenticate both byte payloads
and their adapter proofs. Repeated copies allow component replay.

The unbounded native compiler and literal K215 logical calibration are
explicit inherited dependencies. Source maps give their immutable origins.
Finite replay does not re-prove those theorems. Sun's 2026 representation
result is required only for packing/mask_popcount; Jones ratio results
are used by nine/ and jones/. The eleven and short routes use the inherited
Pell compiler, not Sun's 2026 bridge.

## Reproduce without modifying the release

Python 3.10+ with SymPy and NumPy:

    python verify.py
    python negative_controls.py

The root driver authenticates SHA256SUMS.json, copies the package into a
temporary directory, runs its finite stages, and compares the files in
REBUILD_FILES.json byte-for-byte. Use the driver without -O; individual
checkers also have optimized-run receipts. The three root corruption
controls are integrity tests only. Eleven selective-code mutation tests
are separately included.

Build the PDF with a normal TeX Live installation:

    sh build_report.sh

No shell escape or network access is needed for reproduction. PDF metadata
may vary on rebuilding. Tested package versions are requirements.txt.
No upstream received program is executed by the root replay; pinned
upstream scripts, where retained, are inert provenance.

## Layout

- weights/: selective code, exact certificate, source reconstruction,
  sparse-borrow theorem and semantic corruption controls.
- packing/mask_popcount/: ten-integer polynomial, fixed recipes, Sun
  source contract and complete inherited finalizer.
- nine/: calibrated nine-natural/positive circuits, conservative comparison,
  cancellation-aware exact degree certificates and independent checks.
- jones/: seeded and unseeded thirteen-integer polynomials, guard proof,
  cofinal odd-power base and Jones interface.
- batching/: eleven-positive equations and systems, proofs and full tuple.
- elimination/: independent eleven-variable audits and a rejected further
  transport-elimination direction, not a ten-positive result.
- short/: 80/72 tradeoff, historical 56/74 comparison and relaxed-rank proof.
- root_checks/: independent cross-checks and proof/dependency reviews.
- review/: frozen entry points and later formal-status evidence.

The reviewed search programs are not part of the mathematical definition;
the explicit certified tuple is. Root manifests and replay receipts bind
what is actually delivered. Retain inherited licenses and notices.
