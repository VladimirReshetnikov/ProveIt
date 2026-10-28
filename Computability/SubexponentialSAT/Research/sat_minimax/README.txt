EXACT MINIMAX CERTIFICATES FOR SUBEXPONENTIAL SAT CONTRACTION
Research packet prepared for Vladimir Reshetnikov, 27 October 2026 UTC

START HERE
  report.pdf is the complete research report.
  report.tex and sections/*.tex are its complete editable LaTeX sources.
  PROOF_STATUS.json separates new results, imported premises, and open claims.

RESULT AND SCOPE
For E(s)=s/sqrt(ceil(log2 s)), under the reviewed normalized Boolean-wire
contraction interface:

  Best displayed reviewed cached pair:      time 30.891018920366
                                            space 30.753912832055
  New menus, classical rectangular backend: time 30.087205603377
                                            space 28.852899414942
  New menus, additional 2026 matrix backend: time 28.972941603232
                                            space 28.972651876714

The coefficients mean poly(s+L)*2^((C+o(1))*E(s)), not time per SAT variable.
Safe eventual pairs are 30.09/28.86 and 28.98/28.98. Both use subexponential
memory. The earlier polynomial-space coefficient 46.184845586731 remains
a separate option. The logarithmic denominator power is NOT improved.

The new tool is an exact finite minimax/convex-hull characterization of a
menu of contraction strategies. The four explicit plans include the four
parallel classes of the affine plane over F_3 at nine groups. Sharpness is
only for the stated finite menu under its Euclidean entropy relaxation.

The classical result uses alpha>3/10, omega<19/8. The additional version
imports published characteristic-zero alpha>.465 and omega<=9/4, using
the conservative alpha0=9/20 and an explicit 1+10^-5 exponent allowance.
The report explains the exact number-field and coefficient-ring bridge.
The fast matrix schemes and a complete SAT solver are not implemented here.

FAIR COMPARISONS
The older three-plan method, upgraded with the classical rectangular
backend and the new multistage tail, gives time 30.615143564828 and space
29.966611399887. With the additional 9/4 backend and retuned tail it gives
30.273960451080 / 28.625470242822. The latter has lower memory than our
fastest construction, so the report retains that tradeoff. No global
optimization of all previous algorithms is claimed.

SOURCE CUTOFF
Initial ProveIt: 73dfb5e5ab6e91bd7375e5b97ef85d7e1cc8e81d.
Closing ProveIt: 7de9d09fecd17de776d712835ecb2011205c531d.
Anthropic:      1a6eee293b9e00cb432eef6018a21f523623a9af (user-supplied PR).
OpenAI math:   7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a.

Twenty placed packets plus nine incoming archives were reviewed. During
the review, the nine were placed under Research. All 443 newly placed
files match their archive bytes; 85 members were omitted by that placement.
No new mathematical source was introduced by that relocation. The latest
README also links the Anthropic formalization. Its sources and public
endpoint were inspected, but its Lean build/kernel checks were not rerun.

REPRODUCE (run from this directory; no network)
  python3 run_checks.py
  python3 run_checks.py --optimized

Both use Python 3's standard library and compare replayed JSON with the
delivered receipts. The mathematical checks must be identical. They cover
173,846,817 support tuples by rigorous pruning, compute exact rational hull
witnesses, certify the schedule with rational intervals, apply the same
backends to older plans, test finite nonfield-ring contractions, and check
the modular compiler and signed-CRT interfaces.

For all four independently written, unpruned tuple-norm enumerations:
  python3 run_checks.py --independent

This optional command requires NumPy. The independent schedule audit
requires mpmath and may also be run directly:
  python3 audit/independent/schedule_audit.py

To rebuild the PDF (pdfLaTeX plus standard packages required):
  python3 build_report.py

The build uses no shell escape, runs three passes, and rejects overfull
boxes or unresolved references. Rebuilding the PDF changes its timestamp
and checksum. Verify the original bundle before rebuilding:
  python3 verify_bundle.py

OPTIONAL INDIVIDUAL REPLAYS
  python3 code/adaptive_rectangular.py --output /tmp/certificates.json
  python3 code/schedules.py --output /tmp/schedules.json
  python3 code/comparisons.py --output /tmp/comparisons.json
  python3 code/check_algebra.py --output /tmp/algebra.json
  python3 code/modular_rank_compilation.py --output /tmp/modular.json

The modular checker uses trial division for small-prime validation; it is
a reference implementation of the finite identities. The theoretical
rank-factorization lemma takes a prime field as given. The conditional
SAT route uses only primes polynomially bounded in the original input.

CONTENTS
  report.pdf, report.tex, sections/  Complete research report and source.
  code/                            Exact finite certificate/selection code,
                                   schedule arithmetic, algebra checks.
  code/data/menus.json              Explicit ordered menus and rational data.
  results/                         Executed production and replay receipts.
  audit/independent/                Separately written proofs and checks,
                                   all four inputs/results, Boson probes.
  research/                        Conditional actual-rank route, complete
                                   proof obligations and LaTeX note.
  provenance/                      Pinned source hashes, closing commits,
                                   and bytewise relocation checks.
  INTEGRATION.txt                   Suggested placement and review sequence.
  MANIFEST.sha256.json              Hashes of the delivered files.

LARGER-BREAKTHROUGH RESEARCH
The separate research note proves a modular rank compiler and identifies
an open rank-product target for Anthropic's completed crossing pieces.
A uniform product bound 2^((8/3)*lambda)*lambda^O(1) would yield denominator
power log2(3/2)=0.5849625... instead of 1/2, under its stated interfaces.
THAT RANK BOUND IS NOT PROVED. Signed integer clique reconstruction must
precede the original two-adic recovery. The note and code include that
bridge and negative controls; no speculative faster SAT bound is claimed.

DEPENDENCY BOUNDARY
Imported: exact deformation, Hermite recovery, slope-four Cauchy modes,
weighted entropy, entry-oracle conventions, asymmetric padding, and SAT
reductions. New: finite support-hull identity, explicit menus/certificates,
paid schedules and compatible matrix composition. Open: stronger rank
theorem and a smaller worst-case logarithmic order. No measured SAT speedup,
polynomial-space improvement, full Lean check, or literature-wide novelty
claim is made.
