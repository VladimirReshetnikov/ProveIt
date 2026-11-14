UNARY POWER COVERING AT PA STRENGTH
Research prepared for Vladimir Reshetnikov -- 27 October 2026

START HERE
==========
Open report.pdf. The complete LaTeX source is report.tex plus sections/.
The paper is self-contained and explains the new theorem, its proof, the
relationship to all eight supplied drafts, and the numerical search interface.

The proposed theory U uses classical equality-free first-order logic over a
nonempty domain, with one binary relation written membership. Put

  Sub(x,a) := forall t (t in x -> t in a).

For EVERY formula phi(x) with no other free variable, take the single schema

  forall a exists b [
    forall x (x in b -> phi(x)) and
    forall x (Sub(x,a) -> (phi(x) -> x in b)) ].

There are no other nonlogical axioms. The matrix cannot mention source a
freely. Bound variables may be arbitrarily numerous; this is not one-variable
logic. The upper and lower clauses specify a weak cover, not an exact power
filter over arbitrary sources.

MAIN RESULT AND SCOPE
=====================
The paper proves mutual interpretations of U and full PA and gives uniform
finite-proof construction templates establishing

  PA proves Con(U) <-> Con(PA).

The new lower proof derives induction before successor existence, then uses
globally least failed numerical tuples to obtain bounded constructions with
unary matrices. Numerical powers and canonical finite histories supply PA.
An explicit infinite two-atom orbit model separates U from the stronger
source-only theory in the drafts. The corresponding zero-free-matrix theory
has a two-object model and is provably consistent in PA.

These are conventional mathematical proofs with independent mathematical
reviews. This package does not contain a Lean, Rocq, MM0 or other kernel
certificate of the unbounded interpretation, an implemented general PA-proof
translator, or a newly compiled literal Turing machine. Finite tests below
check code and local mathematical cases; they do not prove consistency.

The primitive closed wrapper remains 20 schematic nodes, or 18+2m for an
m-node matrix. No absolute minimum, 19-node wrapper, or TM state saving is
claimed. Restricting free matrix roles and reducing arithmetic generation
cost are different optimization objectives.

NUMERIC INTERFACE
=================
The second deliverable combines inherited positive local falsity, low-code
collisions and sharing with a bijective mixed dyadic grammar. The preferred
axiom emitter accepts every natural number and has a division-free polynomial
implementation with nine nonlinear multiplications, degree 128, and leading
coefficient 2^71. A fixed 21-bit guard is additional initialization cost.

The complete eight-case positive theorem stream halts on target code 0 exactly
when PA is inconsistent, with the algorithmic equivalence proved in PA by the
paper's finite-proof transformations. Its raw axiom theory deliberately allows
arbitrary free matrix variables: the machine-oriented version avoids a unary
free-variable validator. After adding the stated seed, its ordinary closure
is unrestricted power covering plus global irreflexivity.

The Python stream executes emit_polynomial() in its AX branch. The separate
certificate checker checks AX using the constructor-reference emit(), and the
exact-target replayer specifies conclusions independently as syntax trees.
Decoding, substitution and other proof-engine operations are not claimed to
be division-free. Three persistent arithmetic registers exclude multiplication
workspace and the rest of the proof engine.

REPRODUCE
=========
Python 3.10 or later; standard library only. From this directory:

  python3 -B reproduce.py

This validates SHA256SUMS before and after execution, runs six diagnostic
suites with and without Python -O, compares fresh results to saved receipts,
regenerates and independently replays the exact 16 named certificates, and
checks a 4,096-description bounded search. It writes only to a temporary
directory. Assertions needed for correctness remain active with -O.

To check release hashes only:

  python3 -B reproduce.py --verify-only

To rebuild the paper (also requires pdflatex and the packages in report.tex):

  python3 scripts/build_pdf.py

The default rebuilt PDF is ../report-rebuilt.pdf; --output can select another
path outside this release. The sealed report.pdf is not overwritten. Different
TeX versions and PDF timestamps can change PDF bytes.

To run the reference bounded search directly:

  python3 -B code/positive_stream.py --search --limit 4096

This reports unknown on the delivered prefix. It does not infer consistency
from a bounded run. Omitting --limit requests the abstract semidecision search;
no termination is promised, and actual Python runs have memory, integer and
recursive syntax-tree resource limits. The paper's unbounded algorithm is a
mathematical specification independent of those host limits.

CONTENTS
========
report.pdf / report.tex / sections/  Complete paper and its source.
code/frozen_positive_emitter.py    Codec, two emitter implementations,
                                  three-register program, AST checks.
code/frozen_positive_polynomial.py Exact full coefficient reconstruction.
code/positive_stream.py            Complete theorem stream, certificate
                                  checker and proof-description compiler.
code/replay_certificates.py        Exact independent target inventory replay.
code/unary_diagnostics.py          Finite local numerical/induction checks.
code/check_unary_orbit_model.py    Finite levels of the infinite orbit model.
results/                          Saved receipts and 16 proof certificates.
sources/input_manifest.json       Exact hashes of all 240 input archive files.
sources/external_sources.json     Read source URLs and Git blob identities.
sources/review_scope.txt           Mathematical/code audit boundaries.
reproduce.py                      Non-mutating integrated replay.
scripts/build_pdf.py              Isolated three-pass LaTeX build.
SHA256SUMS                        SHA-256 hashes of the release contents.

ATTRIBUTION
===========
The eight input drafts are the mathematical and algorithmic starting point.
The paper's Table 1 and references assign their contributions individually.
Numerical representatives, saturated ordered-pair coding, deterministic
histories, positive local falsity, useful low-code collisions, arithmetic
sharing, and the total-stream architecture are inherited and adapted.
The new unary proof, separation model, and calibrated dyadic combination are
claimed relative to those eight drafts; no wider historical priority claim is
made. Original draft files and external repository files are not redistributed.
External formal developments were read but not rebuilt.
