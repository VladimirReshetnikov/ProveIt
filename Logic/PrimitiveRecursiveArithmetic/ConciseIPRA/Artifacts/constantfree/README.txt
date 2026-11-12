A CONSTANT-FREE ONE-CONSTRUCTOR PRESENTATION OF iPRA
Prepared for Vladimir Reshetnikov, 12 November 2026
=================================================

RESULT AND LIMIT

The new numerical term grammar is

    t ::= x | J(n; i,r.h).

No numerical constant, successor, initializer, pairing constructor or equality
test is primitive. Define

    K(t) = J(t; i,r.i)
    U(t) = J(t; i,r.K(r))
    Z(t) = J(U(t); i,r.r)
    S(t) = J(t; i,r.Z(r)).

The explicit anchored graph axioms and equation-induction rule prove
U(t)=S(Z(a)) and Z(t)=Z(a) for all a,t. Thus z=Z(z) defines zero uniquely.
The theory is bi-interpretable and equiconsistent with full first-order iPRA:
both numerical domains are whole, equality is actual, and the graph of each
composite isomorphism is x=y. The report gives the interpretations and the
internal operation and formula round trips.

This DOES NOT achieve the user's requested complete-checker complexity target.
The observed prior compact envelope is 251 tokens / 273 AST nodes / 499 bytes,
attained by different programs. The new transparent ordinary-logic checker
has 3072 tokens / 3349 AST nodes / 13723 normalized bytes, versus its matched
register-graph control's 2811 / 3054 / 12626. It is a genuine reduction of
numerical syntax with a larger reference checker. No claim of absolute
minimality or of one program beating all coordinate minima is made.

There is a sharp LOCAL term-size theorem: two raw J occurrences suffice and
are necessary for constant one; three suffice and are necessary for constant
zero. This is not a checker-size lower bound.

START HERE

ipra_constantfree.pdf      Compiled mathematical report.
ipra_constantfree.tex      Complete, self-contained LaTeX source.
code/checker_constantfree.py
                          Complete strict proof checker, standard library only.
code/make_certificates.py  Untrusted builder of the four delivered proof trees.
code/verify_certificates.py
                          Reproducible validation and source measurements.
certificates/             Four explicit closed theorem certificates.
evidence/                 Validation, source audit, and independent review.
reference/                Pinned register manuscript and exact checker control.
compact/                  Separate small refinements of the old scalar checkers.
PROVENANCE.json            Snapshot, exact references, claims, and boundaries.
MANIFEST.sha256            SHA-256 hashes of all delivered files except itself.

EXECUTABLE PROOFS

The checker reads a JSON object with goal and proof fields. A proof is a tree
of explicit primitive inference instructions. It validates syntax, bindings,
alpha equivalence, capture-free substitution, assumptions and eigenvariables.
Its only numerical constructors are v and j. It expands zero and successor
as raw J terms, and checks each arithmetic schema against an explicit anchor.

    python3 code/checker_constantfree.py < certificates/anchor_independence.json

Acceptance means exit status zero and exactly ACCEPT followed by a newline.
The supplied certificates establish U(t)=S(Z(a)), Z(t)=Z(a), existence of a
fixed point z=Z(z), and uniqueness of that fixed point. The certificates are
checked by this Python implementation; the full bi-interpretation is a written
proof, not a new Lean/Rocq formalization.

There are no closed numerical terms. The parameter rule is explicit because
ordinary intuitionistic first-order domains are nonempty. It lets a proof use
a fresh arbitrary number and discharge it from a conclusion that does not
mention it, without introducing an assumption. It is used in zero existence.

REPRODUCTION

    python3 verify_manifest.py
    python3 reproduce.py
    python3 reproduce.py --pdf

The reproduction script verifies exact upstream reference bytes, regenerates
the theorem certificates, replays the main and compact validation suites, and
measures the complete modules. The PDF option uses installed TeX Live only.
If system format caches are missing, build_pdf.py creates a private format
from installed TeX sources. No network access or global TeX changes are needed.

Measurements use CPython 3.12.14, strip genuine docstrings, normalize using
ast.unparse plus one newline, and charge the full standalone module including
JSON input and verdict. Evidence may change under a different Python version;
verify the delivered manifest before rebuilding.

The main suite has 19 cases in normal and optimized Python (38 executions)
plus six capture/substitution checks. The compact appendix has 244 candidate/
control executions over 61 inherited fixtures. All recorded checks passed.
Finite regression checks supplement the written arguments and do not prove
universal correctness of arbitrary implementations.

SEPARATE COMPACT APPENDIX

Two compositions for the INHERITED scalar calculus give 250 tokens and
498 normalized bytes in different programs. They do not implement the new
constant-free J theory, do not improve the 273-node AST record, and assume
the inherited canonical public-goal contract without a separate public
grammar validator. Their exact controls and preservation arguments are
included. Do not combine their numbers into a fictitious single checker.

PROVENANCE

Repository: https://github.com/VladimirReshetnikov/ProveIt
Pinned commit: 5c6c2d8d68da11f89cf2937cf7aca3b85805fd41
Path: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

The J instruction mechanism, arithmetic bootstrap, primitive-recursion
compiler, and equality-reflection argument are inherited from register_graph.
New mathematics: constant elimination via U and Z, anchor-independence,
unique-zero interpretation in a constant-free language, and the sharp local
2/3-occurrence bounds. Inherited material retains the included MIT-0 license.
No repository file or GitHub discussion was modified.
