SUBEXPONENTIAL SAT: ADAPTIVE SCHEDULES AND EXACT KERNEL ACCELERATION
Research iteration for Vladimir Reshetnikov, 27 October 2026

Start with report.pdf. Its complete editable source is the standalone report.tex. The report compares twenty refinement packets and the two primary ETH
manuscripts, including five late arrivals at the closing cutoff. Incoming code was inspected but not executed.

NEW RESULTS (normalized by contraction size s, not SAT variable count n)
* Streamed recursive separators, degree <= ceil(s^0.9), polynomial space:
  coefficient 55.331622..., with exact upper certificate <55.35; this improves
  the strongest checked late adaptive/separator composite >55.4.
* Cached CRT/contraction-tree branch: time coefficient 35.0706136705 and
  space coefficient 33.9995016442. Complete child costs are included.
  This improves the late 35.3545880584 / 34.2748030050 certificate.
* Optional lower-memory companion: 37.3246112387 / 33.6230409217.
* Degree <= ceil(s^0.51), polynomial space: 25.163765..., certified <25.2.
  Stronger very-low-degree and extra-memory branches remain separate options.
* Sparse-support candidate scoring refines the late dense quadratic scorer,
  preserving every selected label, tie and potential. On three controlled
  Q=8,16,24 fixtures it is 1.53--2.73x faster than our matched dense reference;
  other small cases regress. No universal speedup is claimed.
* NEW Cauchy refinement beyond the late quadratic implementation: precompute
  transition unit ratios and absorb the target prefactor once. Table products
  fall from (5N^2+N)/2 to N^2+N, with extra O(L) preparation charged and ONE
  inversion in both algorithms. Both use the same optimized mask backend.
  Final N=256 matched-reference timings improve by 1.46--2.29x; small cases
  can regress. Ring-operation ratios are not time ratios.

LATE-INTAKE CREDIT
Five packets arrived while this report was being prepared. They already
contain adaptive alphabet schedules, dense quadratic balancing, quadratic
Cauchy tables, separator aggregation, and cached contraction-tree/CRT ideas.
Those are credited, not claimed as new. Earlier 63.759/37.592 coefficients and
large gains over cubic feature recomputation remain historical ablations, not
claims to beat the closing frontier. New work is the explicit stronger
compositions/retunings, sparse-support scoring, and fused Cauchy transitions.

LIMITS
No new worst-case logarithmic exponent is established. These are ordinary
proofs relative to inherited contraction identities, not formal certificates
or an independent end-to-end verification of either ETH manuscript.
The independent Claude algorithm has unspecified constants and is not
numerically dominated here. No global optimality claim is made.

The code is component software, NOT a full fast SAT solver. Benchmarks use
exact-output self-authored references and include common initialization and
output. They are not SAT timings. Full-table Cauchy tests use the degree-two
unramified extension over Z/(2^p), not all original solver field degrees.
Small timing regressions and raw samples are retained. Sparse balancing
caches q^0 through q^M, with M total edges; this is pseudo-polynomial if edge
multiplicities are treated as succinct binary weights rather than M edges.

SOURCE SNAPSHOT
Initial ProveIt pin ab2fbc9e03d5c3d0ad6dec8686960bfe498b0b06; closing cutoff
fa6e904d109b738154db7fe41e7f2777e6d24aee:
  Computability/SubexponentialSAT
  docs/incoming
The unchanged OpenAI baseline is pinned at
7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a.
sources/manifest.json records twelve newly reviewed archive Git blobs, archive SHA-256s,
and selected unchanged report snapshots. sources/prior/ includes the prior
source manifest. Source evidence is not executed by any replay.

REPRODUCE CORRECTNESS / CERTIFICATE CHECKS
Python 3.10+ standard library is sufficient. From the extracted folder:
  python3 code/check_balancing.py /tmp/balancing.json
  python3 code/cauchy_checks.py /tmp/cauchy.json
  python3 code/verify_cache_schedule.py /tmp/cache-intermediate.json
  python3 code/verify_fused_cauchy.py /tmp/fused.json
  python3 late_cache_checks/verify_late_cache.py /tmp/cache.json
  python3 late_cache_checks/verify_lowmemory_companion.py /tmp/lowmemory.json
  python3 code/verify_comparison.py /tmp/comparison.json
  python3 asym_schedule_checks/verify_all_certificates.py /tmp/certificates.json
  python3 qa/performance_audit_checks.py /tmp/audit.json
  python3 qa/fused_audit_checks.py /tmp/fused-audit.json
Repeat with python3 -O if desired. Certificate checks explicitly raise errors;
they do not rely on removable Python assertions. The aggregate certificate
driver checks both modes and deliberate wrong constants/guards internally.
Use suitable temporary paths and python instead of python3 on Windows.

SEALED ARCHIVE REPLAY
  python3 code/verify_bundle.py
  python3 code/replay_archive.py PATH_TO_RELEASE.zip /tmp/replay.json
The replay extracts safely, validates sealed files, runs authored checks in
normal/optimized modes, exercises negative controls, and rechecks integrity.
It checks historical benchmark records but does NOT retime the benchmarks.

OPTIONAL BENCHMARKS (may take several minutes)
  python3 code/benchmark_balancing.py /tmp/balancing-benchmark.json 5
See code/CAUCHY_README.md for the exact Cauchy benchmark invocation and scope.
The delivered final timing files are results/balancing_benchmark.json and
results/fused_cauchy_benchmark_mask_all.json. The latter combines two
disjoint paired runs and records their hashes. Earlier raw runs and the
now-prior quadratic-table reproduction are labeled separately.
Do not compare wall-clock samples across different machines as guarantees.

PDF BUILD
  sh build_report.sh
Requires a configured pdfLaTeX installation and packages named by report.tex.
No download or package installation is performed. All final pages were
rendered and visually inspected; details are in qa/visual_review.md.

PACKAGE ORGANIZATION
  code/                      Authored kernels, references and checks
  asym_schedule_checks/      Exact schedule certificates and controls
  results/                   Executed checks and raw benchmark samples
  qa/                        Independent finite audit and visual review
  sources/                   Pinned evidence and provenance, not executable
  *.md                       Supporting proof/review notes
  SHA256SUMS                 Hashes of all other packaged files

Checksums establish byte consistency, not mathematical correctness or
authorship. Compare the release ZIP SHA-256 with the separately delivered
identity before running any package script.

No GitHub branch, file, issue or pull request was changed or published.
