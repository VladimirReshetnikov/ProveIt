FERMAT SPECIALIZATIONS IN INTUITIONISTIC PRIMITIVE RECURSIVE ARITHMETIC
==================================================================
Prepared for Vladimir Reshetnikov, 15 November 2026.

MAIN RESULT
-----------
The paper supplies complete human-readable proofs, with an explicit iPRA
audit, of Fermat's last theorem for every exponent n >= 3 satisfying

    3 divides n, or 4 divides n, or 5 divides n, or 7 divides n.

These are full, unbounded assertions about all positive x,y,z, not bounded
counterexample searches and not merely first-case restrictions. The family
occupies 276 residue classes modulo 420, with density 23/35.

Base proofs:

* Exponent 3: explicit Eisenstein-pair arithmetic, all six units checked,
  bounded factorization, and a strict descent in the coordinate divisible
  by 3.
* Exponent 4: the stronger statement x^4+y^4 != z^2, using two explicit
  Pythagorean parametrizations and descent on z.
* Exponent 5: both parity branches of Dirichlet's descent in Z[phi], with
  phi^2=phi+1. The paper proves the unit normal form and, crucially, gives
  bounded unit normalization before claiming bounded divisor search.
* Exponent 7: an elementary integer quartic descent, including Lebesgue's
  published repair of the missing third factor-allocation case.

Uniform exponent lifting gives the infinite family. Signed and rational
versions, mixed exponents with a common divisor among 3,4,5,7, and the
stronger family X^(4i)+Y^(4j) != Z^(2k) are included.

The package does not prove every exponent, all regular primes, or general
FLT in iPRA. The first omitted exponent is 11. No independence or
unprovability claim is made about omitted exponents.

THEORY AND FORMALIZATION STATUS
------------------------------
iPRA here is first-order intuitionistic logic with equality, all specified
primitive recursive function symbols and their defining equations,
successor separation and injectivity, and quantifier-free induction.

All descents are converted into a fixed-length primitive recursive
iteration or a bounded Boolean induction. Each search has a numerical
bound and each termination invariant is quantifier free after Boolean
coding. The text explicitly avoids a general least-counterexample axiom.

The mathematical argument is complete at the human-readable level.
The Lean deliverable is an OUTLINE WITH CONCRETE DEFINITIONS. It was NOT
compiled here, because no Lean executable was available. There is no
finished Lean proof of the four base exponents and no finished internal
Prf PRAAx proof certificate in this archive.

ArithmeticBlueprint.lean contains readable state definitions, pair-ring
operations, finite iteration, a generic ambient descent argument, and
exponent lifting conditional on explicit unfilled base-proof interfaces.
ObjectLanguageTargets.lean defines actual PR codes, terms, and first-order
formulas against the inspected ProveIt interfaces, plus the exact type of
the intended internal derivations. Its RequiredProofObjects structure has
no supplied inhabitant. No extra axiom or admitted proof is used to fill it.

The article gives the complete dependency plan for finishing both the
ordinary Lean arithmetic proofs and their separate internal iPRA proofs.
An ambient theorem about Nat is not automatically an internal iPRA proof.

CONTENTS
--------
flt_ipra.pdf                    Compiled 34-page paper.
flt_ipra.tex                    Main LaTeX source.
sections/*.tex                 Complete modular mathematical exposition.
lean/ArithmeticBlueprint.lean  Semantic definitions and proof interfaces.
lean/ObjectLanguageTargets.lean Exact ProveIt object-language targets.
lean/README.txt                Lean checking and completion instructions.
lean/lean-toolchain            Pinned Lean version matching ProveIt.
code/verify_cubic.py           Exact arithmetic and formula regression.
code/verify_quintic.py         Symbolic, congruence and bounded-loop checks.
code/verify_seven.py           Seven exact polynomial identities.
code/coverage.py               Exponent enumeration and reduction witnesses.
evidence/verification.txt      Recorded verification output and limits.
evidence/proof_status.json     Machine-readable completion status.
evidence/repository_snapshot.json Inspected ProveIt snapshot and blob hashes.
evidence/sources.txt           Mathematical sources and comparison roles.
evidence/coverage.json         Exact coverage data through exponent 200.
evidence/exponents_through_200.csv Exponents, status, base and multiplier.
requirements.txt              Python algebra dependency.
Makefile                      Reproduction commands.
SHA256SUMS.txt                 Hashes of all other package files.

REPRODUCING THE CHECKS
---------------------
Using Python 3.12 and SymPy 1.14.0, run from this directory:

    python3 -m pip install -r requirements.txt
    make check

The scripts use exact arithmetic. They check transcription and finite
tables. They are NOT an FLT proof checker and do not establish universal
iPRA derivability. The mathematical paper proves those uniform claims.

To rebuild the PDF in a working TeX Live environment with the standard
packages amsmath, amssymb, amsthm, geometry, booktabs, array, longtable,
microtype, xcolor, xurl, fancyhdr and hyperref:

    make pdf

The delivered PDF was compiled with pdfTeX/TeX Live 2025. All fonts are
embedded. The final log has no overfull boxes or undefined references,
and all 34 pages were rendered and visually inspected.

For Lean reproduction and the separate object-language completion target,
see lean/README.txt. Those commands are instructions, not recorded passes.

SOURCE SNAPSHOTS
----------------
ProveIt: bb4427b10219ad61e0d2875fdde04bcd23b47ec6
  Lean/Mathlib v4.32.0.
  Relevant source interfaces were read; the repository was not modified.

isomorphic-ai/fermat: 07b35d10984632caa14b1af26ec5dec2363ee920
  Fermat/Five was inspected as a comparison for the exponent-five argument.
  Its ambient formalization is not treated as a certificate of iPRA strength.

Lebesgue 1840 and his correction are cited in the paper. The correction is
part of the proof, not merely a bibliographical supplement.
