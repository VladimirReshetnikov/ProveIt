CONDITIONAL COPY: A SMALLER iPRA AXIOMATIZATION
============================================
Prepared for Vladimir Reshetnikov, November 12, 2026.

START HERE
----------
ipra_conditional_copy.pdf is the complete mathematical report.
ipra_conditional_copy.tex is its standalone editable source, including the
complete checker listings. It needs no external figures or TeX inputs.

WHAT IS NEW
-----------
The construction combines two restrictions that the current proposal treats
separately: introduction automatically uses the newest numerical parameter
(zero at a closed root), and discharge infers its replacement from two
normalized rows of the opened matrix. Three rule families remain: Use,
Close, Export. Only Use supplies a numerical instantiation term.

The new theorem making this combination possible is conditional copy:

  Delta_t(H) = D_{x,y} Sel(y, H(t), H(x)).

This is uniformly provable without equality transport. Applying it to
H(x) = q_y B(x,y) recovers introduction at any supplied witness. The proof
regenerates source branches under injective numerical-scope embeddings;
it does not assume weakening of a completed newest-parameter proof.
The archive includes an executable general finite-proof translator that
implements this construction, not just special-purpose certificate fixtures.

Two discharge interfaces are supplied. The automatic Export version has no
replacement, equality proof or template input. The backward Name version
supplies those inputs but fixes the equality source to the freshly opened
parameter. Its complete checker improves all three size coordinates against
the current parameter_intro checker. The paper proves that both interfaces
present the same theory; its template lemma covers replacements that contain
the opened parameter and templates that explicitly mention that parameter.

THE MATHEMATICAL CLAIM
----------------------
The report supplies written proofs of exact open-consequence equivalence
with the liberal supplied-witness comparison calculus and of a whole-domain
bi-interpretation with full first-order intuitionistic primitive recursive
arithmetic. Induction is quantifier-free in iPRA and initially restricted
to literal equations in the ordinary recursor realization. Equality is
actual equality; both numerical composites have identity graph x=y.

The new metatheorems and the Python certificate format are not verified in
Lean or Rocq. The report distinguishes the inherited, formally verified
scalar comparison from the written extension and new restriction theorem.
There is no claim of absolute minimality or a proof inside iPRA of its own
consistency. Computation normalization is external canonical syntax, not
an object-language universal primitive-recursive evaluator.

SIMPLICITY AND MEASUREMENTS
--------------------------
Complete standalone modules; CPython 3.12.14; docstrings/comments removed,
ast.unparse, and one final LF. Tokens omit layout; AST counts include context
and operator nodes. The complete normalizer and active syntax validation are
included.

                                     Bytes    Tokens    AST
Selected automatic Close/Export       1844      646     748
New backward Name                    1907      619     686
Matched supplied-witness Close        1863      651     755
Matched explicit equality Name        1835      634     742
Selected, with explicit fuel          1995      685     796
Current parameter_intro               1925      630     701
Current uniform_recursion             1950      662     741
Existing compact scalar control        508      267     302

The backward Name version saves 18 bytes, 11 tokens and 15 AST nodes against
parameter_intro, a strict improvement in all three coordinates. It fixes
the discharge equality source to the opened witness and uses an exact-zero
introduction guard.

For automatic Export, removing the introduction witness saves 19 bytes,
5 tokens, and 7 AST nodes against the otherwise matched liberal control.
That implementation is 81 bytes smaller than parameter_intro, but has more
tokens and AST nodes.
The explicit-Name control is 9 bytes smaller than inferred Export; it needs
an extra equality-proof input. These are distinct tradeoffs: no one delivered
version dominates every competitor. The 508-byte scalar artifact uses a different
certificate/public-validation contract and remains much smaller in bytes.

QUICK CHECKS
------------
Python 3.12 reproduces the recorded metrics. The scripts use the standard
library only. Run these commands from this directory:

  python3 verify_manifest.py
  python3 reproduce.py
  python3 code/checker.py < validation/fixtures/positive/universal_successor_congruence.json
  python3 code/checker.py < validation/fixtures/negative/false_equation.json
  python3 code/checker_backward_name.py < validation/fixtures/backward_name/universal_successor_congruence.json

A valid certificate prints ACCEPT and exits zero. Rejection exits nonzero
(the minimal checker leaves the exception diagnostic visible).

Translate a liberal proof, then check its generated restricted proof:

  python3 code/translate_witness.py < validation/fixtures/source/explicit_witness2.json > translated.json
  python3 code/checker.py < translated.json

The ordinary checker reads [goal, proof]. The bounded checker reads
[goal, proof, fuel]. See FORMAT.txt for all constructors, scopes, and rules.
Any sufficiently large finite budget accepts a valid unbounded certificate;
too little fuel is a rejection, not a mathematical counterexample.

To rebuild the paper with TeX Live or another pdflatex installation:

  python3 build_pdf.py

The build uses a temporary directory and disables shell escape. Rebuilding
may change PDF metadata and its digest. The manifest describes the delivered
files; check it before regenerating evidence or the PDF.

EXECUTED EVIDENCE
-----------------
The packaged replay passed 24 positive and 16 negative certificate fixtures,
80 normal/optimized Python checker CLI runs, three open-scope checks, six
source-to-target translations, and one translator CLI check. All 24 positive
fixtures also replayed against both matched controls. The bounded checker
passed 48 exact/one-short budget tests and nine malformed-budget rejections.

An independent named-variable implementation agreed on 400 normal forms,
1200 numerical evaluations, 480 binder openings, 320 successor contractions,
and two capture regressions. A separate 25-case syntax suite includes attacks
that overlap the main negative fixtures; these are not 41 distinct attacks.

Backward Name additionally passed 24 translations of the main positive
fixtures, two erased-template acceptances, ten negative cases, and 72 CLI
checks across normal/optimized Python. A 5000-template oracle found 149 valid
endpoint pairs and confirmed the exact Name endpoint identity for all 149;
64 used a replacement containing the fresh parameter, and ten erased an
auxiliary raw parameter. These bounded checks supplement the written proof.

Examples include quantified successor congruence, nested D binders, actual
use of an induction hypothesis, an inferred nontrivial export substitution,
and a replacement containing the fresh variable when the exported formula
ignores it. Finite tests are implementation evidence, not general proofs.

FILE MAP
--------
ipra_conditional_copy.tex/.pdf  Complete paper and editable source.
FORMAT.txt                     Numerical/formula/certificate contract.
code/checker.py                Complete selected acceptance checker.
code/checker_backward_name.py  Smaller backward Name checker.
code/checker_fuel.py           Primitive-recursive bounded-certificate version.
code/control_*.py              Otherwise matched comparison checkers.
code/proof_tools.py            Untrusted proof constructors.
code/translate_witness.py      General source-to-target translator.
validation/                    Reproducible independent audits and fixtures.
evidence/                      Actual validation results and measured sizes.
reference/                     Three unchanged comparison programs.
SOURCE_PROVENANCE.json          Pinned source locations and hashes.
CLAIMS.json                    Exact claim boundaries.
MANIFEST.json                  SHA-256 hashes of delivered files.

PROVENANCE
----------
Repository: https://github.com/VladimirReshetnikov/ProveIt
Commit: 8fa5ade009b5cceba7b68f07b6a834fe77cf10c1
Path: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA
The pinned README lists 84 packages. The report compares the newest packages
as well as the inherited native calculus. No repository files were changed.
The inherited MIT No Attribution license is included; the new material is
offered under the same terms.
