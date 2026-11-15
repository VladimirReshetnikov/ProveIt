STIRLING'S FORMULA IN INTUITIONISTIC PRIMITIVE RECURSIVE ARITHMETIC
================================================================

Prepared for Vladimir Reshetnikov, November 14, 2026.

Start with stirling_ipra.pdf. The matching LaTeX source is
stirling_ipra.tex. The document contains the complete human-readable
argument, finite rational estimates, an induction audit, and a concrete
Lean implementation plan.

MAIN RESULT
-----------
For n >= 1, let R_n = n! e^n / (n^n sqrt(2 pi n)) and r_n = log R_n.
The proof establishes the Robbins bounds

  1/(12n+1) < r_n < 1/(12n)

and the relative-error bound

  0 < R_n - 1 < 1/(12n-1).

Thus n >= 2^p implies |R_n - 1| < 2^(-p).

The literal iPRA statement uses the explicitly defined primitive recursive
rational algorithm Q(n,p), not arbitrary real-number variables:

  n >= 1 implies
    1/(12n+1) - 2^(-p) <= Q(n,p) <= 1/(12n) + 2^(-p).

The paper proves a strengthened version with explicit positive strictness
margins, and also gives a direct rational approximation H(n,p) to R_n.
All integral-like operations are finite rational sums with explicit error
bounds. Precision and finite lengths are fixed before every induction.

CONTENTS AND STATUS
-------------------
stirling_ipra.tex / stirling_ipra.pdf
  Complete written proof and formalization plan.

code/stirling_rational.py
  Executable exact Fraction implementations of logarithms, pi, Q, finite
  Wallis sums, and H. These are reference programs, not a formal proof.

code/run_checks.py
  Independent finite rational enclosures, polynomial identity checks,
  Wallis increment/recurrence checks, and endpoint checks.

code/build_pdf.py
  PDF build helper. Uses installed TeX sources; can generate a private
  pdflatex format and font map if those configuration products are missing.
  Requires pdfTeX/LaTeX and the packages used by the source. No network is
  required. All temporary build files stay outside the deliverable tree.

lean/ObjectLanguageTarget.lean
  UNCOMPILED SCAFFOLD, NOT A FINISHED FORMALIZATION. Includes concrete Rat
  algorithms, the PR-checker specification, the exact object-language
  statement, and conditional native-transfer wrappers. It contains no
  sorry and no newly asserted Stirling axiom, but the InternalProof record
  is deliberately not instantiated. A finished project must construct the
  actual Prf PRAAx derivation; standard-model truth is insufficient.

provenance/repository.txt
  Inspected ProveIt revision, exact source URLs, API notes, and search scope.

validation/checks.json
  Results and source hashes for the exact-rational validation run. The
  recorded suite passed 10,974 assertions. The main ranges are n=1..25,
  p=0..12 for Q and n=1..10, p=0..6 for H. This is finite regression
  validation, not a universal proof, internal iPRA check, or Lean check.

validation/build.json
  PDF build details and checks for unresolved references and overfull boxes.

SHA256SUMS.txt
  SHA-256 hashes of the deliverables, excluding this hash file itself.

REPRODUCE
---------
From this directory:

  python3 code/run_checks.py
  python3 code/stirling_rational.py 25 12
  python3 code/build_pdf.py

The mathematical checks use only Python's standard library. Decimal output
is explicitly display-only; every assertion uses integer/rational arithmetic.
The sample Q(25,12) is approximately 0.00333315563672808840707940659912.

LEAN INTEGRATION
----------------
Sources were inspected at ProveIt revision
329161f8da0b319d51ba9f6246c4b19d243f7193.
Its root configuration pins Lean and Mathlib to v4.32.0.

The scaffold imports ConciseIPRA.NativeBiInterpretation. Work in a checkout
of that repository with the pinned toolchain. After building its ConciseIPRA
library, use lake env lean on the scaffold and implement the obligations in
the order given in Section 10 of the paper. No Lean/Lake executable was
available in the authoring environment, so compilation is not claimed.

The complete endpoint is an actual InternalProof stirlingApprox value.
The existing pra_iff_native theorem then transfers the resulting iPRA
derivation to the repository's native ConciseIPRA calculus. The ordinary
real-number interpretation should remain a separate, downstream module.

