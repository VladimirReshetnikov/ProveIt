DIRICHLET AND KRONECKER APPROXIMATION IN iPRA
============================================
Prepared for Vladimir Reshetnikov, November 14, 2026.

START HERE
----------
paper/dirichlet_kronecker_ipra.pdf is the complete human-readable report.
paper/dirichlet_kronecker_ipra.tex is its self-contained LaTeX source.

The literal unrestricted classical statements cannot both be proved in plain
intuitionistic primitive recursive arithmetic. The report proves precise
logical obstructions and supplies explicit constructive theorems:

* Sharp scalar Dirichlet for rational input and integer N.
* Strict scalar Dirichlet for PR real names and integer N, with a fixed margin.
* Full simultaneous Dirichlet for every integer N, in the stronger strict form.
* Unbounded unreduced denominator pairs for every named real, with cubic bound.
* Distinct reduced approximants under a supplied positive irrationality modulus.
* Quantitative full-matrix Kronecker with explicit primitive recursive bounds.
* A finite rational compatibility certificate and an unconditional finite
  approximation-or-near-relation alternative.
* The exact classical criterion for rational generator matrices, and density
  from a PR separation modulus, including an explicit sqrt(2) example.

The sharp closed scalar endpoint implies LLPO. Letting the scalar denominator
bound N be an arbitrary represented real makes even the strict form imply LPO.
The general exact Kronecker relation criterion, and even one-dimensional
density from merely negative irrationality, imply primitive recursive Markov's
principle. None of those principles is silently added to the positive proofs.

CONTENTS
--------
paper/       Report source, compiled PDF, and portable Makefile.
code/        Exact-integer/Fraction reference algorithms, tests, and example maker.
examples/    Six reproducible JSON examples with exact rational error bounds.
lean/        Concrete specifications, a native-proof transport interface,
             detailed completion plan, toolchain pin, and formalization status.
verification/ Executed Python results, PDF build/visual verification, and audit.
sources.json Pinned ProveIt paths and external mathematical sources.
SHA256SUMS.txt Checksums for the delivered files (excluding this checksum file).

REPRODUCE THE NUMERICAL ARTIFACTS
-------------------------------
Python 3.10 or newer, standard library only, from this directory:

  python3 code/test_approximation.py --report verification/python_tests.json
  python3 code/make_examples.py

The tests use exact integer arithmetic and fractions.Fraction, not floats.
The large Kronecker bounds are proof bounds. Tests find witnesses early and
do not exhaust those boxes. kronecker_search assumes its mathematical modulus;
rational_compatibility independently checks that hypothesis for rational data.
The sqrt(2) modulus is proved in the report and independently spot-checked.

The callable real-name convention is name(k) in Q with error at most 2^(-k).
It does not supply a universal primitive-recursive evaluator for arbitrary
program codes; formal statements are schemas for fixed PR definitions or
uniform statements about finite rational tables and certificates.

REBUILD THE PAPER
-----------------
With a standard TeX Live/MiKTeX installation including latexmk and the listed
ordinary LaTeX packages:

  cd paper
  latexmk -pdf -interaction=nonstopmode -halt-on-error dirichlet_kronecker_ipra.tex

No bibliography download or external image is needed. The PDF in this archive
was compiled from the supplied source and visually inspected after rendering.

LEAN STATUS -- READ BEFORE USING
-------------------------------
No approximation theorem has been fully formalized in the supplied Lean files.
No Lean compilation or Lake build was run in this environment. There was no
Lean executable in the checked runtime locations.

FiniteSpecifications.lean defines concrete rational predicates only.
NativeBridge.lean transports an already supplied Prf PRAAx derivation through
the repository's verified pra_iff_native interface. It does not produce the
missing derivation. There are no sorry or axiom declarations masquerading as
completed approximation results.

The planned final target is an actual object-theory derivation

  Prf PRAAx [] encodedFiniteClaim

followed by its native-calculus translation. An ambient Lean theorem over
Nat, Rat, or Real is a separate semantic milestone. LeanPlan.txt identifies
the finite arithmetic, phase, error-budget, and syntactic compilation tasks.

REPOSITORY BASELINE
-------------------
VladimirReshetnikov/ProveIt
Commit: 6ad3d9f37184ac242a8946f1c5d45a5603cf57f2
Lean: leanprover/lean4:v4.32.0; mathlib v4.32.0.
Inspected ConciseIPRA foundation and native-translation sources, and the finite
grid proof in docs/drafts/minkowski_ipra.zip. The report is self-contained;
it does not require an unproved conclusion from another draft.

No change was made to the external repository.
