THREE STRICT CHECKING PRESENTATIONS OF iPRA
========================================

RESULT AND SCOPE

These are smaller complete implementations of the inherited native scalar
calculus. They do not delete a mathematical axiom or prove a global minimum.
All three read one complete JSON value, validate its entire exact-integer/list
alphabet, validate the native Eq/D public goal, and check the certificate.
Unlike the compact guarded profiles, they impose no integer/list or public-
grammar promise on the caller. Their public numerical zero is encoded by 1.

Whole-source metrics, CPython 3.12.14:
                              tokens   AST nodes   normalized UTF-8 bytes
  code/strict_tokens.py           319         370                    630
  code/strict_ast.py              327         358                    642
  code/strict_bytes.py            335         380                    605

The selected current controls with the SAME public zero-as-one syntax are:
  controls/zero_alias625.py        331         373                    625
  controls/strict608.py            334         378                    608

Thus the observed zero-as-one coordinate envelope changes from 331/373/608
to 319/358/605, attained by DIFFERENT programs. No one candidate attains that
triple or beats all three prior coordinates at once. The prior numbers are
attained upper bounds, not theoretical lower bounds. The zero-as-zero
profiles are a separate serialization category; their exact 328-token and
368-node modules are supplied as implementation controls, not presented as
having the same public syntax.

The entire modules, including JSON parsing and ACCEPT output, are charged.
No compressed payload, mathematical evaluator, compiler, or project import
is hidden outside a checker. gzip figures are informational. The source is
normalized by ast.unparse(ast.parse(source)) plus one final LF; every AST
node counts, and significant-token measurement uses tokenize's named token
constants rather than version-dependent integer codes.

RUN

  python3 code/strict_tokens.py < fixtures/supply/207_direct_zero_supply.json

The numbered fixture prefixes identify source records and can vary if the
fixture set is rebuilt. A stable minimal supply certificate is:

  [[0,0,1,1],[[1,1,1],1]]

Pipe that JSON to strict_tokens.py or strict_ast.py. It proves I(0,0;u.0)=0.
The first two scalar zeroes are administrative instruction markers, whereas
expression leaves 1 represent numerical zero.

The terminal checker has a DIFFERENT protocol. The same minimal certificate
above is also valid because its single packet proves the goal directly, but
general certificates must be translated:

  python3 translate_terminal.py supply.json terminal.json
  python3 code/strict_bytes.py < terminal.json

For a substantial fixed example use:

  python3 code/strict_bytes.py < fixtures/terminal/168_guarded_induction_with_used_hypothesis_local.json

Consult fixtures/cases.json for authoritative filenames. A successful run
exits zero and prints exactly ACCEPT followed by LF. An exception, another
exit code/output, or physical resource exhaustion is nonacceptance.

REPRODUCE

  python3 verify.py

This needs only the Python standard library and no network. It recomputes
all complete-module sizes, replays 808 isolated ordinary/-O process runs on
141 fixture files, and regenerates 19 canonical supply-to-terminal proofs.
The delivered receipt records zero failed expected outcomes or translations.
No test assertion inside a checker disappears under Python -O.

INPUT AND PUBLIC FORMULA CODEC

The input is a JSON stack [p_n,...,p_1,A], consumed from its right. Its last
item A is the public goal. Unused prefixes are allowed, but every parsed
value in them still undergoes exact-integer/list alphabet validation.

Expressions are arrays and integers. Public formulas use equations [s,t]
and the two-variable binder D(B)=[B]. Terms use zero=1, successor [t], and
iterator [n,a,h]. Negative integer names are allocated rigid parameters.
A bound slot j is encoded as 3+2*j. The common traversal increments depth
by 5 minus array arity: equality changes from formula to term sort, D binds
two slots, and the iterator binds its state. Successor and some iterator
children have padding slots. Canonical encodings do not refer to those
padding slots. The public validator also permits certain redundant padding
references; the sorted reading interprets them as zero. Soundness is for
every accepted public goal under this reading; completeness is asserted
for the canonical encoding of every theorem, not every redundant spelling.

Internal proof formulas may additionally use Q(B)=[B,B,B]. Its ordinary
meaning is B(0) -> forall y B(y); D(B) means exists x (B(x,0) -> forall y
B(x,y)). The raw auxiliary decoding and ordinary iPRA bridge are inherited
and attributed in PROVENANCE.json.

The lexical alphabet gate is applied to str(parsed_JSON). A nonempty residue
after stripping decimal digits, '-', brackets, comma and space prevents the
packet reader from being called. Floats, booleans, null, strings and objects
are rejected even in unused prefixes. This test is valid for values produced
by the standard JSON parser, not arbitrary user-defined Python objects.

WHAT CHANGED

The token and AST profiles combine the already established zero-as-one
opener O+ with the context-phase implementation. O+ maps a protected scalar
zero to one, without changing its arithmetic reading. The empty context
selects public validation; before auxiliary work the context is made
nonempty. The new scalar validator is consequently just the odd-scalar
condition in odd sort. The candidates also avoid computing an unused target
image in the nonmatching elimination branch. The AST profile uses a
conditional integer multiplier in place of bool and arithmetic multiplication
with the same value. These are implementation and encoding refinements.

The byte profile instead gives every call a terminal packet. One membership
test closes either a retained goal or a scope-checked O+ image of the packet's
computation equation. The flag selecting strict public validation is reset
only AFTER the left-hand goal scan and BEFORE auxiliary computation. General
computation supplies are removed; their uses are inlined as terminal axioms.
This is the existing shared-leaf idea composed with the strict O+ interface.

The terminal profile uses marker u=2 for equation progress. Its test is

  (major is true-valued) OR (len(instantiated_matrix) == u == 2).

Thus a non-major introduction can be progressive only when its matrix is a
literal equation. Every other introduction is by numerical cases, including
compound matrices. The old len(matrix)%2==u test is NOT safe after removing
computation dispatch: u=1 would then select progress for compound formulas.
That preliminary error was caught before delivery; no unsound draft is
included as a checker. The repaired exact-arity gate and its role are stated
in the proof notes and checked at marker/arity boundaries.

THEORY AND PROOF STATUS

All logical and arithmetic strength is inherited from the native scalar
calculus: the iterator's two computation equations; hypothesis; equality
transport; conditional-closure elimination; witnessed-closure elimination;
case introduction; and literal-equation progress. Full first-order
intuitionistic logic and primitive recursion are recovered by the existing
bridge. Both numerical domains remain whole, equality is actual equality,
and both numerical comparison graphs remain x=y. Serialized raw 1 as the
constant zero changes the encoding, not the interpreted domain.

The correspondence claims are written mathematical transfer arguments.
Finite tests and the explicit translator supplement those arguments. No new
Lean/Rocq verification of the Python modules or rebuild of the inherited
formalized bridge is claimed. The unrestricted search for a substantially
smaller mathematical axiom basis remains unresolved.

The translator is UNTRUSTED and is not imported by a measured checker. It
supports canonical successful supply traces with closed computation supplies.
It removes those supply steps, substitutes canonical zero for unused scope
parameters allocated by them, renames the retained eigenparameters, inlines
the appropriate computation at each use, and inserts harmless terminal
packets for retained hypotheses. Unsupported/noncanonical traces may raise.
Completeness for all canonical theorems is the mathematical derivation
argument, not a claim that every raw old certificate is translated.

CONTENTS

  code/                 Three complete standalone candidate modules.
  controls/             Exact attributed earlier implementations.
  fixtures/cases.json   Fixed verdict expectations and source origins.
  translate_terminal.py Untrusted proof translator.
  verify.py             Untrusted metrics and process verification utility.
  PROOF_NOTES.txt        Universal mathematical arguments and limitations.
  PROVENANCE.json       Frozen source paths, archive identities and hashes.
  CLAIMS.json           Exact positive claims and explicit nonclaims.
  evidence/             Metrics, process receipts, translations, source screens.
  LICENSE.txt           Upstream MIT No Attribution license.

SOURCE SNAPSHOT

VladimirReshetnikov/ProveIt, commit
31e1e9220868788a85ca5fea351d7ab4097cfa4a,
Logic/PrimitiveRecursiveArithmetic/ConciseIPRA.
All twelve current incoming archive sizes and Git blob hashes were checked;
evidence/incoming_identity.json records the exact matches. A bounded source
screen and selected controls do not establish universal minimality.
No remote repository change or publication was performed.
