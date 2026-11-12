iPRA with variable-only equality substitution
Prepared for Vladimir Reshetnikov, November 11, 2026 (America/Los_Angeles).

START HERE

report.pdf is the complete paper. report.tex is standalone and can be compiled
without any other local source file. The paper gives every primitive rule,
the new equality proof, the protected translation for the newest-variable
restriction, both iPRA interpretation composites, measurements, limitations,
and further research questions.

RESULT

The primitive equality inference only substitutes for a numerical variable:

       x = t     u = v
       -------------------
       v = nf(u[t/x])

The source can even be restricted to the newest numerical parameter.
A two-row existential witness package recovers arbitrary crossed transport
s=t, h(s)=r ==> r=h(t), with one restricted substitution inference.
The newest-source proof uses a protected proof-translation invariant;
it does not assume naive weakening for arbitrary restricted proofs.

The five-rule Eq/D clausal calculus and its six-rule Eq/Q/D native companion
are equiconsistent and bi-interpretable with full first-order iPRA.
Numerical domains are whole, equality is actual, and both numerical
composite isomorphisms have graph x=y.

MEASURED IMPROVEMENT

Complete module, CPython 3.12.14 ast.unparse normalization plus one LF:

                         Bytes   Tokens   AST nodes
Native upstream Tr        2529      908         965
Native newest variable    2499      899         951
Clausal matched Tr        2856      907         982
Clausal newest variable   2826      898         968

The native control is the exact full_expression_checker.py from the pinned
ProveIt commit. The clausal control is newly constructed and matched.
The improvement is 30 bytes, 9 significant tokens, and 14 AST nodes in
each profile. Smaller arity-encoded programs exist in the repository;
this is not a global record or an absolute minimality theorem.

CONTENTS

- code/native_goal_latest.py: selected six-rule complete checker.
- code/scalar_latest.py: selected five-rule complete checker.
- code/native_original.py: exact upstream native control.
- code/scalar_transport.py: matched clausal transport control.
- code/scalar_variable.py: arbitrary-variable intermediate control.
- code/verify_scalar.py: primitive proof compiler and derivation tests.
- code/verify_semantics.py: independent scalar evaluator and binding checks.
- code/measure.py: complete-module size measurements.
- code/certificates/: positive and negative JSON certificates.
- code/*verification.json and selected_metrics.json: reproducible evidence.
- FORMAT.txt: complete certificate contracts, including unused native hints.
- CLAIMS.json: precise claims and exclusions.
- evidence/: provenance and mathematical audit summary.
- reference/: exact inherited proofs and license.
- paper/: editable section sources.
- build_source.py: reassemble the standalone report.tex.
- reproduce.py: rerun verification, metrics, CLI checks, and optionally PDF.

REPRODUCE

Python 3.12.14 is the reference size-measurement environment. The checkers
use only the standard library. An ordinary TeX Live installation is enough
for the paper.

    python3 reproduce.py --check-manifest
    python3 reproduce.py --pdf

To rebuild the standalone source after editing the section files:

    python3 build_source.py

To verify one closed example:

    python3 code/native_goal_latest.py < code/certificates/native/accept_00.json

The native checker accepts exactly "ACCEPT" with exit status zero on success.
Its hypothesis/reflexivity leaves intentionally ignore unused hint payloads,
matching the source control. Every final formula and used rule argument is
checked. The forward clausal checker traverses its entire proof tree.

VALIDATION

57 derivation/rejection checks, 804 independent normalization/substitution
semantics checks, and 74 command-line replays (normal Python and -O) passed.
No semantic cases were skipped. The tests include nested translated
transports, two additional eigenvariable scopes, context extension, initial
parameter permutation, and multiple nested iterator binders.

These are implementation checks, not proof-assistant verification.
The mathematical equivalence proof is written in the report. No new
Lean or Rocq formalization is claimed.

PROVENANCE

The comparison is pinned to ProveIt commit:
5d85023b0688e03b75f0ec3a04bb43ef0bb51705

https://github.com/VladimirReshetnikov/ProveIt/tree/5d85023b0688e03b75f0ec3a04bb43ef0bb51705/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

Full computation normalization, clauses, the D connective, and the
arithmetic/logical bi-interpretation bridge are inherited and attributed.
The new result is the variable-source restriction and its newest-source
refinement. Five incoming archives were inspected to avoid repeating their
existing computation and clause reductions.

The inherited MIT No Attribution license is included under reference/.
