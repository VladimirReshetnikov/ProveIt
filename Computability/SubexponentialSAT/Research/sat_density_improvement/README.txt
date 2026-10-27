IMPROVING THE CLAUSE-DENSITY DEPENDENCE OF EXACT k-SAT COUNTING
Prepared for Vladimir Reshetnikov, October 26, 2026.

MAIN RESULT

Using the cited OpenAI preprint's tensor-contraction theorem, parity-lift
identity, and existing high-density counter, the report derives a
deterministic polynomial-space exact counter with bound

  poly_k(n,m) * 2^{ O_k( n/sqrt(log n) *
                      min{log(2+m/n), log log n} ) }.

The constants are uniform in clause density. For m = Theta(n log log n),
the exponent improves from O_k(n log log n / sqrt(log n)) to
O_k(n log log log n / sqrt(log n)).

SCOPE

This improves the density dependence. It does not improve the unrestricted
worst-case n-only exponent or the fixed-density n/sqrt(log n) exponent.
The full extension has not been formally verified. The explicit constants
are very large, and no practical-speed claim is made.

FILES

density_aware_sat_improvement.pdf
    Complete mathematical report: theorem, explicit construction, proofs,
    uniform complexity accounting, comparisons, limitations, and further
    research questions.

density_aware_sat_improvement.tex
    Complete editable LaTeX source, including bibliography.

code/verify_components.py
    Standard-library-only exact finite verification and reference routines.
    These are new-component checks, not a complete SAT solver.

verification_results.json
    Results of the executed check suite, including exact spectral pivots,
    test ranges, and all parameter calculations for B = 1,...,1000.

source_manifest.json
    Exact upstream repository commit, Git blob hashes, source URLs, and
    references. The original source manuscript is not repackaged here.

PROOF_STATUS.txt
    Imported theorems, new derivations, finite-test status, and scope.

Makefile
    Reproduction commands for the PDF and finite checks.

CHECKSUMS.sha256
    SHA-256 hashes of the delivered files, excluding the checksum file itself.

REPRODUCE

  python3 code/verify_components.py --output verification_results.json
  latexmk -pdf -interaction=nonstopmode -halt-on-error density_aware_sat_improvement.tex

Alternatively use `make verify` and `make pdf`. The Python script requires
only Python 3.10+ and its standard library; no pip packages are required.
The report uses common TeX Live packages. If latexmk is unavailable, run
pdflatex on the .tex file three times to resolve the references and contents.

TEST INTERPRETATION

All tests relevant to correctness use exact integers or fractions.Fraction.
Finite spectral tests cover only the recorded small graphs. The general
Margulis-Gabber-Galil spectral theorem is cited, not proved by testing.
Likewise, neither the source tensor engine nor the asymptotic theorem is
validated by timing these small tests. Their proofs and dependencies are
separately stated in the report.

SOURCE SNAPSHOT

Repository: https://github.com/openai/math
Commit: 7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a
Preprint: The Exponential Time Hypothesis is False, revised October 25, 2026.

The report proposes a refinement relative to this snapshot. It does not
claim priority over all other work or report changes to the repository.
