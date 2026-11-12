FIVE-RULE iPRA WITH A SINGLE EVALUATION SCHEMA
Prepared for Vladimir Reshetnikov, November 11, 2026

START HERE

report.pdf   Complete mathematical report, with inherited arithmetic proofs
             and the full standalone checker listing.
report.tex   Standalone editable LaTeX source for that PDF.
code/checker.py
             Selected complete acceptance checker; Python standard library only.

RESULT

The theory C5 has normal scalar-iterator terms, equality and D formulas,
reusable clause contexts, and five inference patterns:

  Refl, Eval, Use, Elim, Intro.

Only I(0,a;u.h) is contracted by the term syntax. Successor computation
remains explicit. The one evaluation scheme is

  I(n,a;u.h)=t,  I(Sn,a;u.h)=r  ==>  r=h[t/u],

with every expression understood in zero-normal form. It recovers both
computation and all equality reasoning. There is no separate equality-only
context parameter; the update h is supplied as the iterator's computation
data. A validated reflexive goal closes immediately. The other four
patterns have certificate tags.

The written proof establishes exact consequence equivalence with the
existing zero-normal native kernel. Composing the explicit formula
translations and both round trips with the inherited scalar/iPRA bridge
gives full first-order intuitionistic PRA, equiconsistency, and
bi-interpretability. Both numerical domains remain whole, equality remains
actual equality, and both numerical composite graphs are x=y.

The construction combines existing clause and single-evaluation reductions.
The report credits both. A shorter congruence derivation uses two Eval and
two Refl nodes, and crossed transport uses four Eval and three Refl nodes.
Each supplied proof is used once in the one-template expansion.

EXACT SIZE COMPARISON

Complete modules, CPython 3.12.14; remove the module docstring, apply
ast.unparse, add one LF. Gzip uses maximum level 9 and timestamp zero.

Program                    Bytes  Tokens  AST nodes  Gzip-9
Selected single Eval        2283     741        826     818
Matched raw CE5             2416     744        842     855
Matched zero + root case    2426     765        865     862

This is a strict improvement in all three normalized source coordinates
against these matched complete controls: 5.50% fewer bytes than the raw
control, with 3 fewer tokens and 16 fewer AST nodes.

Readable selected source: 2717 bytes, gzip-9 1036 bytes. Readable raw control:
2698 bytes, gzip-9 984 bytes. Thus the original formatted file is not shorter
than the raw control. The normalized metric removes comments/formatting.
The auxiliary forward implementation improves only bytes and is not the
selected coordinatewise result.

This does not beat the repository's separate 516-byte compact codec. There
is no claim of absolute minimality, a new global compact-code record, or
new Lean/Rocq verification of this combination or the Python implementation.

EXECUTED VERIFICATION

  66 raw-to-normal proof translations with independent native replay;
  70 accepted and 20 rejected adversarial certificates;
  180 public command-line checks, in ordinary Python and python -O.

The source set contains 32 original CE5 examples, 32 distinct round-tripped
certificates for those examples, and two witness-normalization repairs.
These are 66 certificates, not 66 independent mathematical phenomena.
One repair example genuinely consumes the old base assumption. Additional
positive examples use an induction hypothesis and apply a closure at
three targets. These finite checks support the implementation; they do
not replace the general written proofs.

REPRODUCE

From the extracted package root:

  python3 reproduce.py
  python3 code/checker.py < examples/used_induction_hypothesis.json
  python3 code/checker.py < examples/witness_collapse_consumes_base.json
  python3 code/checker.py < examples/reject_false_equation.json

The first two example checks must print ACCEPT with exit status zero.
The last must print REJECT with nonzero exit status.

To build the PDF in a normal TeX Live installation:

  python3 build_pdf.py

All LaTeX source dependencies are embedded in report.tex. Python
reproduction needs only the standard library; PDF compilation needs
pdflatex and the standard packages named in the preamble.

CONTENTS

  report.tex / report.pdf        Complete report and compiled PDF.
  code/checker.py                Selected standalone checker.
  code/raw_control.py            Matched raw CE5 control.
  code/zero_control.py           Matched zero-normal root+Eval control.
  code/forward.py                Independent forward implementation.
  code/forward_raw_control.py    Its raw comparison source.
  reproduce.py                  Untrusted proof compilers and test driver.
  FORMAT.txt                    Complete public certificate contract.
  examples/                     Accepted and rejected target certificates.
  tests/raw/                    The source proof certificates.
  evidence/                     Exact metrics, normalized/gzip sources,
                                verification result, reviews, and PDF QA.
  reference/                    Attributed arithmetic foundations and
                                independently supplied checkers/Lean endpoints.
  CLAIMS.json                    Machine-readable claim boundaries.
  SOURCE_PROVENANCE.json         Pinned sources and artifact identities.
  SHA256SUMS                     Integrity hashes, excluding this manifest.

PINNED SOURCE

Repository: https://github.com/VladimirReshetnikov/ProveIt
Commit: 1eb151b8f40800aec569361e827d934cb77bd3e1
Path: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

The current comparison includes all four incoming archives in that snapshot.
The exact new combination was absent from the inspected specifications;
there is no wider priority claim. Existing Lean endpoints were inspected
but not rebuilt. Their dependent imports are not all copied here; they are
reference sources, not a standalone Lean project.

Inherited sources retain their MIT No Attribution license, supplied in
reference/LICENSE-ProveIt.txt. New code may be used under the same terms.
No repository modification, commit, or pull request was made by this package.
