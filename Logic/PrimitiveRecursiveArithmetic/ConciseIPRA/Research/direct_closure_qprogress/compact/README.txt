DIRECT Q-PROGRESS: STANDALONE IMPLEMENTATION EVIDENCE
==================================================

This directory contains three COMPLETE, independently executable proof
checkers, frozen JSON proof certificates, and a standard-library-only runner.
The checkers import only json. They do not import the test runner, producers,
proof-tree descriptions, repository files, or mathematical report.

RUN OFFLINE

    python3 verify.py

To regenerate the execution and measurement receipts:

    python3 verify.py --write

The complete measurements include JSON input and verdict output. Source
normalization removes genuine docstrings, uses ast.unparse, and appends one
newline. Significant tokens exclude comments, indentation, line breaks and
end markers. AST nodes are counted with ast.walk. Gzip level 9, with mtime=0,
is informational only; its wrapper is included. Exact reported normalization
and gzip sizes use CPython 3.12.14 and zlib 1.3.2. Other runtimes may differ.

MEASURED PROGRAMS

Program                       Bytes  Tokens  AST  Gzip9
baseline_529.py                  529     266  310    333
qprogress_guarded.py             568     285  331    348
qprogress_extended.py            552     278  322    341

The baseline is an unchanged copy of the current neutral_scope implementation.
The two new profiles are larger in these measurements. They implement a
simpler primitive induction interface; they do NOT establish a smaller
complete Python checker or an absolute simplest axiomatization.

MATHEMATICAL CHANGE

Terms, computation, equality transport, Q-elimination, D-elimination and
D-case introduction remain unchanged. Replace D-progress by:

    Gamma, E(z) |- E(S z)
    -------------------- Q-progress
       Gamma |- Q_y E(y)

E must be a literal equation and z must be fresh for Gamma and fixed matrix
parameters. Q_y B(y) means B(0) -> forall y B(y). D_{x,y} B means exists x Q_y B.
The new induction rule has no existential witness or existential-coordinate
substitution. Q-progress was already a derived rule of the old calculus.

New Q-progress is simulated in the old calculus by D-progress with an unused
existential coordinate and witness zero, then D-elimination returning Q.
This adds two primitive proof-tree nodes. Conversely, simulate old D-progress
by new Q-progress on E(t,y), then D-case with witness t, using Q-elimination
and its local E(t,0) assumption. This adds three primitive proof-tree nodes.
Both simulations preserve end sequents literally. The arithmetic and the
existing full-domain bi-interpretation with iPRA are inherited.

PUBLIC PROTOCOL

Each executable reads a JSON array from standard input. The last element is
the goal. Earlier four-field packets [major, source, initializer_or_mode,
template_or_witness] are popped backwards. Acceptance requires normal exit
and exactly the line ACCEPT. Exceptions, nonzero exits, resource exhaustion,
and other output reject. Unused prefixes are allowed. Completeness has the
usual adequate-resource qualification for each finite derivation.

The inherited sorted arity representation is unchanged. At formula positions,
a two-element array is equality, a one-element array is D, and a three-element
array is Q with its last child as matrix. At numerical positions, a one-element
array is successor and a three-element array is the initialized iterator.
Other admitted representations include the inherited truth/zero aliases.
Canonical Q formulas repeat the matrix three times. Capture-free opening and
the same lexical fresh-name floor are used throughout.

Canonical introduction packets for the NEW profiles are:

  [[], 0, [], witness]  D-case introduction, goal [B].
  [[], 0, 0, 0]        Q-progress introduction, goal [E,E,E].

The latter packet has no witness. The final field is ignored by that branch.
Truthy initializer fields retain the original computation protocol; nonempty
major premises retain the original transport, Q-elimination, and D-elimination
behavior. The old baseline instead interprets mode 0 as D-progress.

The guarded profile requires a literal-equation matrix for its canonical
Q-progress packet. Its guard uses a non-JSON complex sentinel on failure.
Returning Boolean False on guard failure would be unsafe: it could introduce
scalar zero into the context and close the altered goal.

The extended profile admits Q-case for compound matrices:

    Gamma, B(0) |- B(S z)
    -------------------- Q-case
       Gamma |- Q_y B(y)

This is a derived rule, simulated by D-case with an unused existential
coordinate and D-elimination. Among canonical matrix forms, the shared arity dispatch chooses progress
only for literal equations; compound matrices receive their zero
instance. A trivial compound Q identity fixture is consequently rejected by
the guarded profile and accepted by the extended profile. The expected
outcomes record this difference explicitly.

EVIDENCE AND LIMITS

The frozen fixtures cover direct successor-iterator and identity-iterator
induction, induction with side assumptions, nonvacuous existential use,
transport below a closure, inherited positive examples translated to the new
rules, and translations back into the old baseline. They also cover malformed
roots, a scalar-context forgery, a context-leak forgery, compound-progress
rejection in the guarded profile, and wrong introduction-root rejection.
Both normal Python and python -O are exercised in separate processes.

proof_tree fields are explanatory, named syntax. Only packet (or the explicit
raw input string) is sent to a checker. The producer that constructed these
fixtures is not needed to run them, and is not a trusted dependency.

These finite tests are implementation evidence, not a proof-assistant
formalization of universal raw-input soundness, the arithmetic bootstrap,
or bi-interpretability. The new rules' equivalence has a direct written proof.
The compact raw encoding additionally inherits the existing decoder and
successful-trace arguments. In the extended profile, scalar truth aliases
require the refined invariant that a scalar hypothesis is added only when
the current goal is that same scalar; that continuation immediately closes
and cannot subsequently use the scalar as an elimination major.

SOURCE AND ATTRIBUTION

Repository: VladimirReshetnikov/ProveIt
Pinned commit: 8662bc0a00f4e77e482f7d141d7a4f919f70f9aa
Base: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Research/neutral_scope

The baseline checker and original fixtures come from that package. New
certificates were serialized using an untrusted adaptation of the attributed
witness_rule/tests/inherited_producer.py with lexical scopes, neutral majors,
and Q-progress support. The inherited MIT No Attribution license is included.
The new checker modifications and fixture translations are by ChatGPT for
the current comparison. No repository changes were made by this package.

evidence/source_manifest.json fixes the exact source and fixture bytes.
evidence/metrics.json records runtime-specific measurements.
evidence/validation.json records every complete-process outcome.
