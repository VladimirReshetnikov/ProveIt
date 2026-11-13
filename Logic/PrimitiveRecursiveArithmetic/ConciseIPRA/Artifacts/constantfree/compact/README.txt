TWO SMALL COMPOSITIONS FOR THE EXISTING SCALAR CHECKER

These programs implement the repository's inherited guarded scalar calculus.
They are not implementations of the constant-free J theory in the main report.
They delete no logical or arithmetic axiom. Their small changes are included
as separate implementation results, with exact matched controls and fixtures.

COMPLETE-MODULE MEASUREMENTS

Program                   Tokens     AST nodes     Normalized bytes
controls/tokens251.py         251           283                  605
code/tokens250.py             250           283                  603
controls/bytes499.py          265           301                  499
code/bytes498.py              264           299                  498

The measurement convention is CPython 3.12.14 ast.unparse plus one LF;
significant tokens omit comments, newlines, indentation and encoding markers.
The entire standalone acceptance module is counted. Neither candidate
achieves the current 273-node AST minimum, and no single program in this
appendix is smaller than every coordinate of the previous envelope.

INPUT CONTRACT

The compact contract is a finite integer/list certificate with a canonical
closed guarded Eq/D public goal. Internal administrative formula aliases have
the inherited sorted interpretation. These modules do not separately validate
the public grammar. They must not be compared with fully validated public
checkers as if their input contracts were identical. Some frozen regression
fixtures intentionally exercise auxiliary or malformed syntax; acceptance of
an auxiliary spelling is not a claim that it is a canonical public formula.

Input is a JSON array used as a stack, with the advertised goal last. Packets
are read from the right. Unused prefixes are permitted by the inherited
format. Acceptance requires exit status zero and exactly ACCEPT followed by
one newline. Exceptions reject. Token-profile and byte-profile certificates
use different scope conventions and are not interchangeable.

THE 250-TOKEN COMPOSITION

The 251-token control uses the packet-tail reuse from progress_independence:
after m,*r=q(), the tail r contains [s,u,t]. The new program additionally
uses the variadic immutable context convention from context_order.

The state map is literal: old c(a,g) corresponds to new c(a,*g). At entry,
the new g is exactly the old tuple. An augmented tuple assignment creates
a new local tuple in either version; neither mutates a parent's context.
The same recursive major goal is checked, the same global floor is read and
updated, and every opening and instruction-pop occurs in the same order.
An induction on completed calls and loop steps proves the same successful
traces, subject to sufficient ordinary implementation resources. This is an
exact representation change, not a new inference principle.

THE 498-BYTE COMPOSITION

The control is context_order's 499-byte program. The new program replaces
the introduction selector ~len(a)%2 by 3%len(a), using the remainder-selector
argument already supplied by smaller_envelope and progress_independence.
The new change is its composition with the newer context-first program.

For the meaningful formula arities, the Boolean selectors coincide:

  Arity                    1 (D)       2 (equation)       3 (Q resource)
  Boolean old selector        0                  1                    0
  Boolean new selector        0                  1                    0

With a nonzero major, m or ... bypasses either selector. With a zero major,
canonical goals and matrices have one of the three displayed arities, so
each canonical native-rule certificate still follows the same transitions.
At arity zero the new remainder is undefined and can only reject an alias.
At arity at least four, the decoded formula is administrative truth and its
opened version remains truth. The inherited sorted soundness induction may
therefore use either fresh or zero images in that branch. No new public
theorem results. This argument concerns the decoded public consequence
relation; it does not assert identical acceptance of all malformed JSON.

REPRODUCTION

Run from this directory:

    python3 verify.py

The script measures every complete module and replays the 40 inherited
global fixtures and 21 inherited local fixtures against candidate and control,
in normal and optimized Python execution. The resulting receipt is
evidence/validation.json. The fixture source paths and exact SHA-256 hashes
are in fixtures/cases.json; source archive identities are in
evidence/provenance.json. Finite tests supplement the preservation arguments.

PROVENANCE

Repository: https://github.com/VladimirReshetnikov/ProveIt
Snapshot: 5c6c2d8d68da11f89cf2937cf7aca3b85805fd41
Directory: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

Source packages are the incoming ipra_progress_independence.zip,
ipra_context_order_2026-11-12.zip, and ipra_smaller_envelope.zip.
The underlying native scalar calculus and its iPRA bi-interpretation are
inherited. The main report's constant-free theorem is a separate result.
Inherited code and fixture material retain the repository's MIT-0 license,
included at ../reference/LICENSE.txt.
