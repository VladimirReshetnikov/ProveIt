AFFINE GEOMETRY AND PAID RECURSION FOR SUBEXPONENTIAL SAT
Research prepared for Vladimir Reshetnikov, October 26, 2026 (Pacific).

MAIN RESULT

For the common normalized Boolean contraction interface with root degree
at most ceil(s^(9/10)), initial precision/truncation at most s, and the
reviewed entry-access and creation-precision contracts:

  Time  <= poly(s + input length) 2^((30.269872910441123... + o(1)) s/sqrt(log2 s))
  Space <= poly(s + input length) 2^((29.487537286921217... + o(1)) s/sqrt(log2 s))

Exact leading coefficients:
  C_T = (pi/ln 2)(sqrt(128000/5103) + sqrt(21920/7857))
  C_S = (pi/ln 2)sqrt(8000/189)

The strongest comparable prior cached pair is
30.891018920366... / 30.753912832055... .

The new idea is a four-plan affine-plane contraction menu, with all
intermediate operations bounded by geometry, plus a twelve-group menu,
punctured affine menus and a fully paid 9 -> 12 -> 8 -> 7 -> 4 schedule.
The support certificates are exact, finite and reproducible.

The result improves leading exponential coefficients, not the logarithmic
order of the unrestricted SAT exponent. It uses subexponential space and
does not replace the best polynomial-space branch. It is relative to the
explicit inherited deformation, recovery, packing and reduction interfaces.
There is no end-to-end SAT solver, practical SAT benchmark, new Lean proof,
or independent rebuild of the supplied Anthropic Lean project in this packet.

ADDITIONAL RESULT

The exact packet matrix action is Toeplitz convolution. The included
quadratic-ring prototype avoids division by nonunits. Its full-grid
convolution loses to a stronger Boolean-input baseline on sampled small
fixtures; the parity-strided specialization wins at the two largest sizes.
The raw negative and positive timing results are retained. The main
coefficient theorem does not rely on these measurements or on this kernel.

READ AND REPLAY

  report.pdf                         Complete mathematical report
  report.tex and review/*.tex        Complete LaTeX source
  PROOF_STATUS.json                 Claims, dependencies and limitations
  data/portfolios.json               Frozen plans and exact target certificates
  code/                             Standard-library Python implementations
  results/                          Normal/-O certificates and raw timings
  provenance/                       Immutable source URLs, hashes and commits
  review/*.txt                      Source review and independent audit notes
  MANIFEST.json                     SHA-256 package integrity manifest

From this directory:

  python3 code/run_checks.py
  python3 code/verify_manifest.py
  bash build.sh

Python 3.10+ suffices; validation used Python 3.12. No third-party Python
packages are required. The PDF build needs latexmk/pdflatex and the normal
AMS, TikZ, Latin Modern, hyperref and microtype packages. Building a new PDF
can change its metadata and therefore its manifest hash. Verify the
delivered manifest before rebuilding if you want to check original bytes.

Optional fresh timing run:
  python3 code/check_toeplitz.py --benchmark --output benchmarks_rerun.json

SOURCE SNAPSHOTS

Mathematical intake: VladimirReshetnikov/ProveIt at
73dfb5e5ab6e91bd7375e5b97ef85d7e1cc8e81d: twenty filed packets plus nine
incoming archives. A closing review covers the relocation and public Lean
link updates through 7de9d09fecd17de776d712835ecb2011205c531d. The nine
archives are now filed, giving twenty-nine packets; docs/incoming is clear.

User-supplied Anthropic revision:
1a6eee293b9e00cb432eef6018a21f523623a9af, anthropics/formal-math/eth.
The current public paper is a different revision from the earlier PDF
filed in ProveIt. The report uses the public supplied paper for its crossing
interface discussion and distinguishes static source review from rebuilding.

The ZIP is self-contained for its new finite checks and PDF build.
The complete upstream proofs remain external, pinned dependencies.
