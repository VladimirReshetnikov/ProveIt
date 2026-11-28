FOUR RESEARCH ADVANCES FROM THE PROVEIT GRH ANALYSIS
Prepared for Vladimir Reshetnikov, 27 November 2026

START HERE
  research_report.pdf  -- overview followed by all four complete papers
  research_report.tex  -- combined-report source (includes the standalone PDFs)

The archive contains mathematical proofs and reproducible computations, not a
Lean formalization. It does not claim to prove a prominent general conjecture.
Newness is assessed relative to the pinned project and targeted searches, not
certified worldwide priority. The source's RH/Dirichlet-GRH build was not replayed.

PAPERS
  01_endpoint_filters/paper.tex and paper.pdf
    Necessary coefficient b <= pi*d/Q*, a factor-two improvement; endpoint
    exclusion when A >= 0; an exact feasible interval for zeta-beta products.
    verify.py; verification.json.

  02_psl2_detectors/psl2_detector.tex and psl2_detector.pdf
    Optimal maximum degree of a spectrally detecting family for PSL2(q),
    q == 1 (mod 4); positive Hecke identities give unconditional actual zero
    detection. The q=9 exception and a three-field all-odd identity are included.
    verify_psl2.py; verification_psl2.json.

  03_sparse_padic/sparse_padic_jump.tex and sparse_padic_jump.pdf
    Exact deep-disk root maxima at 2p+2, 2p+3 and 2p+4 terms for every p >= 5;
    integer squarefree extremizers of degree p^2+p at the final threshold.
    new_phase_checks.py; modp_scan.py; new_phase_certificates.json.
    The JSON retains exact integer coefficient lists, Taylor-valuation root
    counts, squarefreeness checks, and finite residue-profile results.

  04_mirror_hessian/paper.tex and paper.pdf
    Explicit variance formula for the full width Hessian at strictly positive
    reflection-paired filters; exact normal kernel and quadratic rigidity.
    verify_mirror_hessian.py; mirror_hessian_checks.json.

REPRODUCE
  Requirements: Python 3.10 or newer; SymPy and mpmath; pdflatex with standard
  AMS, geometry, booktabs, microtype, hyperref, pdfpages, fancyhdr and Latin
  Modern packages (e.g. a full TeX Live distribution).

  python -m pip install -r requirements.txt
  python build.py                 # compile all five PDFs, twice each
  python build.py --checks        # regenerate checks, then compile
  python build.py --checks-only   # regenerate checks only

The sparse script uses --large through build.py to retain all five witnesses.
Its p=5 residue scans can take several minutes. No internet is required after
installing the dependencies. Each paper can also be compiled separately by
running pdflatex twice in its folder. Numerical checks in the endpoint and
Hessian scripts are illustrations, not interval-arithmetic proof certificates.

AUDIT AND STATUS
  SOURCE_AUDIT.txt       -- source scope, prior results, dependencies, limits
  source_manifest.json  -- immutable snapshot, source paths and content hashes
  REVIEW.txt            -- mathematical cross-review and verification scope
  SHA256SUMS.txt         -- checksums of delivered files except this manifest

The four main theorems are unconditional in the precise formulations given.
Only the real-zero-ordinate reading of the completed-divisor filter theorem
uses the stated Dirichlet-GRH input. The detector results give RH equivalences,
not RH for the remaining nonabelian fields. Please consult the precise domain,
multiplicity, positivity and locality assumptions before applying a theorem.

The external repository sources are cited rather than repackaged. All scripts
and manuscripts needed to reproduce the new work are included here.
