EXACT RECTANGULAR CONTRACTION AND ECONOMICAL EQUALITY NETWORKS FOR 3-SAT
Research prepared for Vladimir Reshetnikov
Snapshot: October 26, 2026 Pacific time (relevant commits October 27 UTC)
Opening snapshot: ProveIt 8e76d515063c4b9fbd8743a846b457e3a01bc039 (29 filed + 5 incoming).
Closing snapshot: ProveIt 0cf10036e6ad732c27f13e6058f4acd9b3d78415 (34 filed; incoming clear).
Closing audit: all 213 files placed by 324f3d9b009ab0323f33be65cd6577867c9c4338
match the already-reviewed ZIP bytes; no new mathematical packet or content change.

MAIN RESULT

This packet obtains smaller leading exponential coefficients, relative to
the explicitly imported exact-contraction and matrix-multiplication theorems:

  Generic normalized cached time: 29.8116089454 -> 28.6327662766
  Low-degree cached time:          13.3796490663 -> 10.3367239856
  Low-degree cached space:         13.2530249330 -> 10.3366545687

Each coefficient multiplies s/sqrt(log_2(s)), where s is the original
normalized wire budget. The generic root degree is at most ceil(s^(9/10));
the low-degree root premise is ceil(s^(1/12)). These are distinct interfaces.
The generic new time and space both have coefficient 28.6327662765359...
The earlier alternative with generic space 25.9890677187 remains useful;
the new generic bound does not dominate every previous time-space pair.

The exact equality encoding has

  M_B = L + 2 sum_v floor(max(d_v-3,0)/(B-2))
      <= L(1 + 2/(B-2)).

With B=ceil(log_2(L+2)^2) and a small-size fallback, the low-degree theorem
gives a deterministic exact counter, and hence a 3-SAT decider, in

  poly(n+m) 2^((10.3367239855467... + o(1)) L/sqrt(log_2 L)).

Here L is the normalized literal count, n the declared variable count,
and m the original clause count. Safe eventual time and space coefficient:
10.337 per literal, or 31.011 per clause using L <= 3m.

THE ORDER-IMPROVEMENT OBJECTIVE REMAINS OPEN

The unrestricted variable-based order remains
poly(n+m) 2^O(n loglog(n)/sqrt(log n)). This is not a proof of a smaller
logarithmic-order exponent. The improved algorithms use subexponential
space; there is no new polynomial-space contractor or practical SAT timing.

WHAT IS NEW

1. An exact number-field-to-integer-to-residue-ring bridge using the pinned
   primary matrix bounds omega_C <= 9/4 and alpha_C > 93/200. It handles
   denominators, bit lengths, recursive circuits, array costs and uniformity.
2. New exact support certificates under that backend, including a new
   fifteen-plan cyclic menu, with integer-only exhaustive verification.
3. Fully paid generic and low-degree integer recursion schedules. Child
   table entries, the terminal route, precision, and packing gates are charged.
4. A count-preserving, nearly wire-preserving equality-network encoding
   with exact wire formula, compiler, and semantic tests.
5. A scoped proof that nonempty proper Heisenberg mode deletion cannot
   preserve finite single-point locality. It rules out that shortcut only.

The comparison grants earlier contractors their available high-occurrence
conditioning, so the equality encoding's factor saving is not counted twice.

FILES

  report.pdf                Complete proof report and repository review.
  report.tex, sections/     All LaTeX source needed to rebuild the report.
  code/                    Portable standard-library verification programs.
  data/                    Complete exact plans, weights and claimed fractions.
  results/                 Reproduced finite certificates and execution receipts.
  audit/                   Independent checks and formal-source/CI evidence.
  provenance.json          Repository pins, source blobs and incoming ZIP hashes.
  PROOF_STATUS.json        New/imported/implemented/unresolved status.
  INTEGRATION.txt           Suggested repository placement; no remote changes made.
  SHA256SUMS.txt            Checksums of distributed files except itself.

REPRODUCE THE CHECKS

Python 3.10 or newer; standard library only. No network access is required.
From this directory:

  python3 code/run_checks.py
  python3 code/run_checks.py --optimized

The first command runs all five suites. The second verifies the same results
with Python optimization and checks agreement with existing ordinary outputs.
The scripts also work when invoked by absolute path from another directory.
The support suites exhaust 2,460,861 pair choices in total. Depending on the
machine, the largest suite can take tens of seconds. No acceptance condition
relies on a removable Python assert or on floating-point optimization.

Individual commands:

  python3 code/verify_new_backend.py
  python3 code/verify_weighted_ten.py
  python3 code/verify_schedule.py
  python3 code/verify_packing_gates.py
  python3 code/verify_normalization.py

The equality compiler is code/equality_normalization.py. Import its public
functions to normalize a formula and build a network; its small-network
brute-force evaluator is for semantic verification, not asymptotic solving.

REBUILD THE PDF

Install a standard LaTeX distribution with pdfLaTeX, amsmath, amsthm,
mathtools, lmodern, geometry, microtype, booktabs, longtable, enumitem,
xcolor, fancyhdr and hyperref. Then:

  sh build_report.sh

The included PDF was compiled twice and rendered for visual inspection.

SCOPE AND DEPENDENCIES

The exact contraction identities, packing and entropy interface are imported
from the pinned source and preceding packets. The two stronger matrix
exponents are imported primary theorem dependencies. Their finite algorithms
are proved effective by a fixed exact search, but no practical schemes are
implemented here. This packet does not independently reprove all upstream
papers. The existing Anthropic theorem is a uniform machine theorem, but
does not verify these new numerical coefficients. Upstream CI evidence is
included; no fresh Lean build was possible in this environment.

The compiler and finite certificate checkers are implemented. The complete
subexponential SAT counter is not. The paper gives eventual asymptotic
upper bounds, not measured end-to-end speedups or usable crossover sizes.

Every application in this packet is exclusively to 3-SAT (and its exact count
as the computation used to decide satisfiability).
