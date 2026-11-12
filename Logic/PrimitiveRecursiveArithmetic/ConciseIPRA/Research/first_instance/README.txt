IPRA FIRST-INSTANCE WITNESS DISCHARGE
===================================
Prepared for Vladimir Reshetnikov, November 11, 2026.

START HERE
----------
ipra_first_instance.pdf is the complete mathematical report.
ipra_first_instance.tex is its standalone editable LaTeX source.
The proof removes the separate equality-proof premise from the current
witness-discharge rule and preserves every open sequent. The report includes
the normalization, full logical, and scalar-arithmetic bridges to first-order
iPRA, with whole numerical domains, actual equality, and identity numerical
composites. Both formula composites are supplied as well.

The construction is a local reduction relative to the current witness-discharge
presentation. It is not an absolute minimum and does not beat the repository's
516-byte compact checker. The matched checker is smaller in normalized bytes
and AST nodes, but uses three more significant tokens; see the measured table.

  python3 reproduce.py       Verify hashes, replay proofs and rerun measurements.
  python3 build_pdf.py       Rebuild the standalone LaTeX report.
  python3 build_report.py    Reassemble LaTeX after editing the paper/ sections.

A TeX installation is needed only for rebuilding the PDF. Python acceptance
and verification use only the standard library. The complete bounded variants
are code/checker_fuel.py and code/control_fuel.py; they add an exact nonnegative
integer fuel field. See paper/fuel.tex and evidence/fuel_verification.json.
SOURCE_PROVENANCE.json pins the repository; CLAIMS.json states claim boundaries.
MANIFEST.json records every other delivered file. Inherited materials retain
the included MIT No Attribution license; new material may be used likewise.

DETERMINISTIC WITNESS DISCHARGE: EXECUTABLE ARTIFACTS
=================================================

The standalone checker is code/checker.py. It has three instruction families:
clause use, paired introduction, and paired elimination with a substitution
read deterministically from the opened clause. The fixed initial axiom clause
is universal reflexivity. Full iterator normalization is part of the trusted
syntax implementation and is included in the measurements.

This is a reduction of the mathematical interface: paired elimination no
longer receives a separately proved equation or an independently selected
substitution target. It is not an absolute minimality claim and does not beat
the 516-byte compact or 788-byte public-goal-validated upstream profiles.

QUICK START
-----------

  python3 code/checker.py < tests/positive/successor_congruence.json
  python3 verify.py
  python3 measure.py

Python 3.12 or newer and its standard library are sufficient. No external
package, network request, supporting proof compiler, or reference file is used
by the standalone checker. Acceptance is exactly exit status zero and ACCEPT
on stdout. Exceptions, REJECT, nonzero exits, and resource exhaustion do not
constitute acceptance. The checker has no assert-based acceptance checks, so
python3 -O preserves its checks.

CONTENTS
--------

code/checker.py              selected standalone deterministic checker
code/control_old.py          matched old-Name control with equality proof
reference/                  pinned comparison modules, unchanged
measure.py                  reproducible tokens/AST/bytes/gzip9 measurements
verify.py                   proof translations, independent replay, subprocess tests
tests/positive/             16 selected packet certificates
tests/negative/             57 exact-grammar and soundness attacks
tests/source_proofs/        13 inherited annotated old-Name certificates
tests/support/              untrusted compilers, macros, and independent replay
evidence/metrics.json       all counted metrics and hashes
evidence/verification.json  reproducible finite validation results
evidence/provenance.json    source attribution and pinned repository commit

The support directory includes both explicit goal checking and forward
synthesis interfaces for reproducing the earlier representation comparison.
They are outside the trusted standalone checker. Only one complete module is
counted per row; coordinates from different programs are never combined.

CERTIFICATE FORMAT
------------------

The input is exactly a JSON object with keys "goal" and "proof".

Numerical terms:
  integer 0                 zero
  negative integer -j      free numerical parameter allocated at level j
  positive integer j       de Bruijn bound index, nearest binder numbered 1
  [0,t]                    successor
  [n,a,h]                  initialized iteration; h binds one previous state

Formulas:
  [s,t]                    equality of terms
  [B]                      D(x,y).B, inner y index1 and outer x index2

D(x,y).B means exists x (B(x,0) -> forall y B(x,y)). All terms and formulas
supplied as syntax must already be in full iterator computation normal form.
Every substitution used by a rule is followed by the same normalization.
The contradiction is 0=S0, encoded [0,[0,0]]. The formula H is 0=0, encoded
[0,0]; the numeral ONE has the same raw array shape, disambiguated by its sort.

Every *used* proof node is a triple [code,arg,branch]. The initial context has
one unconditional clause forall y, y=y, at index zero. At a context of length
n, free parameters -1,...,-(n-1) are available, and the next fresh parameter
is -n. This equality between clause depth and scope is maintained by both
scope-extending instructions.

1. [j,t,p], j a nonnegative integer: clause use

   Select clause j, instantiate its one-bound-variable body at t, and return
   that formula. If the clause has an antecedent, p must prove it. For an
   unconditional clause, p is deliberately unused and may be any JSON value;
   the examples use null. The index and the term t are checked.

2. [B,t,p], B a nonempty formula matrix: paired introduction

   Introduce D(x,y).B at witness t. Let b be the next fresh parameter and
   C(y)=nf(B(t,y)). Under an unconditional assumption C(eta), p must prove
   C(Sb). Here eta=b exactly when C is an equation and t is literal0;
   otherwise eta=0. The result is the original D formula, whose complete
   syntax and scope are checked before this inference can succeed. Validation
   visits erased subtrees before it contracts computations.

3. [[],p,q]: deterministic witness discharge

   p must prove D(x,y).B in the outer context. Open x at fresh b and write
   C(y)=nf(B(b,y)), C0=C(0), and C1=C(1). q proves F under the additional
   clause C0 -> forall y C(y).

   If C0 is literally H and C1 is literally b=t, replace all free occurrences
   of b in F by t, in one pass, and normalize. In every other case leave F
   unchanged. The returned formula must be well formed in the outer scope,
   so b cannot escape. The target t may itself contain b, but the final
   normalized result must eliminate every occurrence of b.

   Since formula normalization preserves the outer constructor, C0=H implies
   C1 is an equation. The implementation therefore needs no separate test
   for the length of C1. The substitution test is performed on integer leaves
   only and applies exclusively to the current fresh parameter.

The main simplification is the third instruction. In the selected branch,
its missing equation proof is reconstructed by using the new clause at ONE
with reflexivity H. In the default branch it is reflexivity b=b. The new
proof-to-old-proof compiler implements exactly that expansion.

The matched old control has the same three-field packet format, except its
Name instruction is [[],p,[e,q]], where e separately proves b=t in the extended
context. This is the only relevant logical difference between that control
and the selected checker.

MEASUREMENTS AND LIMITS
-----------------------

Measurements remove string-expression documentation, use ast.unparse, append
one LF, and count the entire standalone module, including parser, sort/scope
validation, normalization, inference checking, and final acceptance. They were
reproduced using CPython 3.12.14. gzip uses level9 and timestamp0 and is reported
for information only.

Selected:           2157 normalized bytes, 704 tokens, 804 AST nodes, 870 gzip9
Matched old triple: 2228 normalized bytes, 701 tokens, 813 AST nodes, 894 gzip9
Incoming old goal:  2273 normalized bytes, 732 tokens, 813 AST nodes, 903 gzip9
Uniform binding:    2238 normalized bytes, 693 tokens, 764 AST nodes, 866 gzip9
Compact profile:     516 normalized bytes, 265 tokens, 306 AST nodes, 332 gzip9
Public-goal profile: 788 normalized bytes, 358 tokens, 413 AST nodes, 460 gzip9

Thus the mathematical rule change saves 71 normalized bytes and nine AST
nodes in the matched triple interface, while using three more tokens. It
saves 116 bytes, 28 tokens, and nine AST nodes against the incoming original
witness-discharge implementation. It is shorter in bytes than the current
uniform-binding implementation but has more tokens and AST nodes. These are
separate comparisons, not a claim of universal dominance.

verify.py replays 16 positive certificates, translates 13 inherited proofs
through the separate-transport control, checks the reverse expansion of new
Name to old Name, and rejects 57 malformed/forged certificates. Its 178
standalone runs include ordinary and optimized Python. These are finite
implementation checks. The universal correctness, logical equivalence and
bi-interpretation arguments are written mathematics in the accompanying
paper; this package claims no new Lean or Rocq formalization.
