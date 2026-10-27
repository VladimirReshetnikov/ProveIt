CONTRACTION TREES AND STREAMED CAUCHY FEATURES FOR SUBEXPONENTIAL SAT
Research packet for Vladimir Reshetnikov — October 26, 2026 (Pacific time)

START HERE
  report/report.pdf    Complete 18-page mathematical report and review.
  report/report.tex    Editable master source; includes two adjacent .tex files.

REVIEW BOUNDARY
  Repository: https://github.com/VladimirReshetnikov/ProveIt
  Initial pin: ab2fbc9e03d5c3d0ad6dec8686960bfe498b0b06
  Closing pin: 474ddba696a5d385c091c23fb2995f69edd13e00
  Fifteen refinement packets were reviewed, plus the primary manuscript context.
  Seven incoming archives were moved during the review; an eighth matching-based
  packet was also checked. All 312 recorded closing Git blob comparisons passed.
  Canonical paths and complete source identities are in provenance/ and audit/.

RESULT 1: RELATIVE EXACT-CONTRACTION CERTIFICATE
  Let s count Boolean network wires and lambda=ceil(log2 s). For the common
  interface with max degree <=ceil(s^0.9), initial precision/truncation <=s,
  and the original entry-oracle conditions, the new cached algorithm has

    time  poly(s+description_length) * 2^[(C_T+o(1))*s/sqrt(lambda)]
    space poly(s+description_length) * 2^[(C_S+o(1))*s/sqrt(lambda)]

    C_T = pi*sqrt(24339)/(20*ln 2) = 35.354588058401...
    C_S = pi*sqrt(915)/(4*ln 2)    = 34.274803005023...

  The new ingredients are binary construction of cached subset tables and an
  exact coordinate/CRT bridge to a fixed fast field-multiplication algorithm.
  Every recursive child evaluation is charged. Canonical creation precision
  and all inherited exact identities remain explicit assumptions/imports.

  Matched analytical ablation at the SAME strict schedule:
    Strassen + old flat block construction           38.4844959057
    exponent-12/5 backend + old flat construction     37.5461655198
    exponent-12/5 backend + binary construction       35.3545880584

  The last step lowers the matched certified coefficient by about 5.84%.
  A compatible combination at the previously supplied r=16 schedule already
  gives 44.5375718550; it is not a global optimum of all possible retunings.

RESULT 2: IMPLEMENTED LOCAL KERNEL
  For packet length L, P requested ports, and B retained modes, factored prefix
  reuse changes Cauchy feature-generation work from O(L+P*B^2) to O(L+P*B),
  at unchanged working precision. Streaming requires constant auxiliary ring
  storage per port. Only units are inverted; valuations are kept separately.

  Paired 512-mode, 128-bit fixture (four final ports, three interleaved repeats):
    direct modular median  3.851839104 seconds
    prefix modular median  0.037780919 seconds
    ratio                 101.9519695643
    multiplications       2,093,066 -> 20,410
    unit inversions       1,044,489 -> 8,161

  Both methods use identical modular arithmetic, include the common prefactor,
  materialize outputs, and check exact output equality on every timed repeat.
  The full six-case data and raw timings are in results/prefix_benchmark.json
  and results/prefix_benchmark.csv. Hardware timing varies; operation counts
  and exact outputs are deterministic.

SCOPE AND LIMITS
  * The global SAT logarithmic order is unchanged. The coefficients above use
    network wires, NOT SAT variables.
  * The fast cached theorem uses subexponential space. It is not a new
    polynomial-space result.
  * No full SAT solver or full contraction engine is included.
  * The asymptotically fast matrix backend is an imported theoretical algorithm.
    Included CRT/matrix code verifies its arithmetic interface with naive finite
    products; it does not implement that fast backend.
  * The prefix prototype implements the unramified quadratic ring with
    U^2+U+1=0; its proof applies more generally.
  * No new Lean/Rocq proof or independent end-to-end certification of the ETH
    claim is asserted. The stronger conditional n/log n interfaces remain open.
  * Kernel timing is not an end-to-end SAT benchmark. No numerical dominance
    over unspecified big-O constants in the separate Claude manuscript follows.
  * The changes are new relative to the reviewed corpus. Prefix reuse, CRT,
    contraction trees and fast matrix multiplication are established techniques.

REPRODUCE (Python 3.10+ STANDARD LIBRARY)
  From this extracted directory:
    python3 code/verify_manifest.py
    python3 code/verify_all.py
    python3 -O code/verify_all.py
    python3 code/benchmark_prefix.py --repeats 3 --output results/reproduced_benchmark.json --csv results/reproduced_benchmark.csv

  Optional unchanged rational-baseline comparison:
    python3 code/verify_all.py --original /path/to/joint_cauchy.py

  The optional source is not redistributed. It is available at:
    https://github.com/VladimirReshetnikov/ProveIt/blob/474ddba696a5d385c091c23fb2995f69edd13e00/Computability/SubexponentialSAT/Research/eth_joint_cauchy/code/joint_cauchy.py
  The wrapper checks its exact SHA-256 before loading it. The recorded run
  checked 3,124 features against this unchanged Fraction implementation.
  The core offline run skips only that optional comparison.

  Ordinary and optimized Python results agree exactly. Explicit exception-based
  checks remain active with -O. Details appear in the JSON verification ledgers.

REBUILD THE PDF
    python3 code/build_report.py
  Requires pdfLaTeX and the standard packages named in report/report.tex.
  The build runs without shell escape in a temporary directory and places the
  PDF at report/report.pdf. Its deterministic source date is fixed. Different
  TeX versions can produce different bytes; this does not invalidate the proofs.
  A regenerated file may differ from the release byte manifest.

PACKAGE MAP
  report/       PDF, master LaTeX, full cached-tree proof, prefix proof.
  code/         Prefix implementation, paired benchmark, exact checkers,
                report builder and manifest verifier.
  results/      Recorded finite checks, paired benchmarks and report QA.
  provenance/   Initial/closing commit data, source hashes and baseline identity.
  audit/        Independent mathematical and implementation reviews.
  INTEGRATION.txt  Suggested repository placement and exact integration boundaries.
  CLAIMS.json     Machine-readable status of proved/imported/implemented claims.
  LICENSE         ProveIt's MIT No Attribution license for the new packet.

The archive contains no credentials, generated environments, source manuscript
copies, or remote-repository mutations. Its intended size is below 4 MB.
