THREE RULES AND ONE NUMERICAL CONSTRUCTOR FOR iPRA
Prepared for Vladimir Reshetnikov, November 11, 2026

START HERE
----------
report.pdf is the mathematical paper. report.tex is the editable source;
its two generated table/summary inputs are included in evidence/.

RESULT
------
The new presentation has numerical variables, zero, and one counter-aware
successor-seeded recursor R(n,a;i,u.h). Successor is R(0,a;i,u.0), so it is
not an additional constructor. Both R and the paired logical binder D bind
two variables in their last child. Retained clauses still have one implicit
specialization variable; no claim is made that all unary binding disappears.

Formulas are equations and D_{x,y}B, read as
exists x (B(x,0) -> forall y B(x,y)). The primitive proof interface has one
fixed universal reflexivity clause and three inference families: Use, Close,
and Name (substitution at fresh witness discharge). Full computation
normalization is part of the trusted syntax and is counted in the checker.

The paper derives equality transport, the missing case introduction at zero,
all intuitionistic logical connectives and quantifiers, equation induction,
actual-equality reflection and full quantifier-free induction. It gives a
direct compiler for all primitive recursion without pairing. The two
interpretations use whole numerical domains and actual equality. Their
numerical isomorphisms have graph x=y, and both formula round trips are proved.

SIMPLER IN A PRECISE COMPARISON
-----------------------------
Complete standalone checker       Bytes  Tokens  AST  Gzip9
Scalar Name control                1983     663  751    812
New uniform-recursion Name          1950     662  741    806
Scalar Name with explicit fuel      2169     711  810    880
New uniform recursion with fuel     2136     710  800    873

The exact main control is the incoming inferred_witness output_control.py.
The scalar fuel control is constructed by applying the same budget
instrumentation; it is not an unchanged upstream file. Only the main
unbounded control's arithmetic representation/normalizer and binding/successor
operations are changed. The saving is modest: 33 normalized bytes (1.66%),
one significant token, and ten AST nodes. It is a compositional reduction,
not a claim that its inherited ingredients were independently discovered.

A SEPARATE STRICT-NATIVE CHECKER IMPROVEMENT
------------------------------------------
The native/ folder refines the existing scalar calculus without changing it.
It combines public grammar validation with the existing first scope traversal,
using depth parity to recover the sort. The entire certificate is unchanged
in both translation directions.

Current native public checker       780     360  409    458
Clearer fused native checker         685     340  385    409
Optional integrated-case variant    661     336  381    390

Use native/fused_native.py for the clearer interface implementation.
The 508-byte compact control has a different public-validation contract and
remains smaller in bytes. No absolute minimum or corpus-wide smallest
axiomatization is claimed. The native refinements are not implementations
of the new R theory, and their sizes must not be attributed to it.

VALIDATION
----------
Main code: 44 positive certificates; 44 separate-dispatch goal replays;
36 existing-fixture translations; 25 invalid documents rejected; 8 invalid
fuel annotations rejected; 88 exact/one-short fuel checks; 60 ordinary/-O
CLI checks; 846 independent numerical comparisons; 250 normalization
idempotence checks; 60 selector/recursor checks. A two-free-parameter sequent
and the regression for a captured ambient bound variable also pass.

The fixture translator deliberately skips one case where normalization
changes the witness to zero. A direct proof of that same final formula is
included separately. It is not advertised as a universal proof compiler.

Native refinement: 143580 generated syntax positions, 430740 program checks,
zero mismatches and zero RecursionError outcomes; 108 ordinary/-O CLI checks
of 18 upstream proof fixtures, against their declared expectations.

Finite executions support the implementation. The general equivalence and
bi-interpretation arguments are written proofs, not new Lean/Rocq proofs.
The inherited Lean project was not rebuilt. Full normalization is not claimed
uniformly primitive recursive; the included fuel-bounded checker supplies a
primitive-recursive certificate predicate with the same theorem set.

RUN
---
Python checks require only Python 3.10+ and its standard library. Sizes were
measured with CPython 3.12.14; ast.unparse can vary between versions.

  python3 reproduce.py
  python3 code/counter_name3_matched.py < code/examples/transitivity.json
  python3 native/fused_native.py < native/fixtures/native/transport_under_D.json

Acceptance means exit status zero and exactly ACCEPT on standard output.

To rebuild the PDF with an installed TeX Live distribution:

  python3 build_pdf.py

FILE MAP
--------
report.tex / report.pdf       Mathematical report and compiled PDF.
code/                        New R checker, fuel checker, exact controls,
                             proof constructors, examples, and main validation.
native/                      Separate native refinement, controls, audit,
                             and pinned fixtures.
evidence/                    Combined metrics, review, validation, PDF QA.
reference/                   Attributed inherited arithmetic and Lean sources.
PROVENANCE.json               Pinned repository and exact source map.
CLAIMS.json                   Supported claims and explicit exclusions.
MANIFEST.json                 SHA-256 and byte size of delivered files.
LICENSE.txt                  MIT No Attribution license.

BASELINE
--------
https://github.com/VladimirReshetnikov/ProveIt
Commit 11814771b7490dfbea0ed5fcf0f5b23586334764
Logic/PrimitiveRecursiveArithmetic/ConciseIPRA
Includes all six incoming archives present at that commit.

No remote repository was modified for this deliverable.
