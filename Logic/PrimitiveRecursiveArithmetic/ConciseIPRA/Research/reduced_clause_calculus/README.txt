A SMALLER COMPLETE CLAUSE CALCULUS FOR iPRA
Prepared for Vladimir Reshetnikov, November 11, 2026.

START HERE
ipra_reduced_clause_calculus.pdf is the complete mathematical report.
ipra_reduced_clause_calculus.tex is its standalone LaTeX source, including
the complete checker listing and inherited arithmetic reference proofs.

RESULT
The current raw clausal calculus has three evaluation cases. The root
case s=t, s=r => r=t is redundant. Keep only zero and successor evaluation:

  V0: a=t, I(0,a;u.h)=r                 => r=t
  VS: I(c,a;u.h)=t, I(Sc,a;u.h)=r       => r=h[t/u].

Together with reflexivity, clause use, paired elimination and the existing
witness-directed introduction, these give a smaller complete presentation.
There remain five serialized instruction families; Eval has two cases.
Raw terms, ordinary capture-avoiding substitution, Eq/D formulas, clauses,
all validation, and the public certificate format are unchanged.

For W(s)=I(0,s;u.0), the deleted rule has the exact derived implementation

  Root(p,q) = V0(p, V0(q, Refl(W(s)))).

The two calculi derive exactly the same sequents. Identity translations
compose with the inherited full first-order iPRA bi-interpretation: both
numerical domains are whole, equality is actual equality, and the numerical
composite isomorphism has graph x=y.

MATCHED MEASUREMENT (CPython 3.12.14)
                                normalized bytes  tokens  AST nodes
Exact current raw clause control       3046          853      993
Reduced raw clause checker             2999          848      986

The complete programs include validation, substitution, the rules, JSON
input and acceptance/rejection output. All numbers count the whole module.
This is a strict local improvement, not a repository-wide size record.
The other compact guarded codecs are smaller and use different interfaces.

ATTRIBUTION AND LIMITS
This package combines two reductions already in docs/incoming:
ipra_raw_clausal_2026-11-11.zip supplies the raw clause interface;
ipra_equality_from_iteration_2026-11-11.zip supplies the identity-frame
deletion of root evaluation. Neither component is claimed as a new result.
The new deliverable integrates them, gives an effective checked compiler,
measures the exact unchanged-interface deletion, and supplies the complete
proof presentation and limitations. No absolute-minimality theorem, large
mathematical breakthrough, or new Lean/Rocq verification is claimed.

REPRODUCE
From this directory:
  python3 reproduce.py
  python3 code/reduced.py < examples/explicit_root_0.reduced.json
  pdflatex -interaction=nonstopmode -halt-on-error ipra_reduced_clause_calculus.tex
  pdflatex -interaction=nonstopmode -halt-on-error ipra_reduced_clause_calculus.tex

The verifier prints ACCEPT and exits zero for a valid certificate; it prints
REJECT and exits nonzero otherwise. The top-level JSON object must contain
exactly goal and proof. The public interface checks closed Eq/D theorems.

CONTENTS
code/reduced.py                Proposed standalone verifier.
code/baseline.py               Exact raw-clausal control.
code/translations.py           Compiler and reverse inclusion (untrusted).
reproduce.py                  Reproduces measurements and validation.
examples/                     Baseline and translated proof certificates.
evidence/                     Executed checks, metrics, exact diff, reviews.
reference/                    Source audit, inherited proofs and provenance.
baseline/                     Unchanged comparison code and test corpus.
companion/                    Zero-normal single-Eval experiment;
                              not the recommended size profile.

SOURCE SNAPSHOT
831081033253cca2115196cf86bb99c77ed2aeae
https://github.com/VladimirReshetnikov/ProveIt/tree/831081033253cca2115196cf86bb99c77ed2aeae/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

The final source and PDF are also available separately from the ZIP.
See the report's Further research questions for the remaining mathematical
and formalization targets.
