WHOLE-JSON FRAMING OF THE ESTABLISHED COMPUTATION-LEAF CHECKERS

This directory is a self-contained, attributed validation package. The only
new trusted-program changes replace the JSON-lines reader of two existing
checkers by one complete JSON-array reader. No mathematical rule is changed.
The complete function ASTs agree after replacing loads(input()) by q().

Provenance is fixed to VladimirReshetnikov/ProveIt commit
6c6a164d211f0af34e913d55c9f46f8ef7cb560f. Exact archive/member paths and SHA-256
identities are in provenance.json. The repository's MIT-0 license is copied
as reference/LICENSE-ProveIt.txt. Controls and the optional untrusted proof
producer come from the pinned computation-leaves incoming archive. Two legacy
proof sources come from the pinned three_field package.

TRUSTED ACCEPTANCE PROGRAMS

Profile                      Tokens     AST     Normalized bytes
controls/tokens_stream.py       243      271            616
candidate/tokens_whole.py       248      277            615
controls/ast_stream.py          248      264            613
candidate/ast_whole.py          254      268            613

The complete modules, including their JSON readers and ACCEPT output, are
measured after CPython 3.12.14 ast.unparse plus one final LF. Token counts omit
comments and layout tokens; AST counts include every ast.walk node. The two
whole-JSON candidates are different programs, with global and local freshness
policies respectively. Pair certificates with the indicated profile.

The whole-JSON token/AST gains are relative to the separately audited
whole-JSON envelope (249 tokens and 269 nodes). The existing line-stream
records, 243 tokens and 264 nodes, remain smaller. No byte record or single
program attaining every coordinate is claimed.

INPUT CONTRACT AND FRAMING THEOREM

Input is a finite list of exact-integer/list records with a canonical closed
guarded Eq/D public formula in the inherited arity codec.
The final record is the goal; preceding three-field records are consumed by
pop(). Unused prefix records are allowed. The compact checkers do not include
an independent validator for this promise.

Given old line-stream records [goal, packet1, ..., packetN], the new JSON value
is [packetN, ..., packet1, goal]. Only the OUTER list is reversed. Hence every
successive read produces the same tree, every proof-checking state is the
same, and both runs agree on success for finite valid records. EOFError versus
IndexError both reject an exhausted input. Parsing the whole new value before
checking does not preserve arbitrary malformed unread trailing text; no such
raw-byte equivalence is claimed. The public theorem set and its inherited
iPRA bi-interpretation are unchanged.

USAGE

    python3 verify.py
    python3 candidate/tokens_whole.py < fixtures/literal_zero_successor_repair.json
    python3 transduce.py to-array old.jsonl new.json
    python3 transduce.py to-stream new.json old.jsonl
    python3 regenerate.py

The last command reproduces four compiled fixtures from their retained legacy
source certificates. The ordinary acceptance programs do not import any
producer, transducer, verifier, theorem table or other local module.

FOCUSED VERIFICATION

verification.json records 14 fixture files and 80 independent subprocess
executions. Every selected control and candidate is run normally and with -O.
There are no failed expectations. The suite covers:

* Progressive induction with an actually used induction hypothesis.
* Compound case introduction and compound implication elimination.
* Equality transport used to establish reflexivity.
* Successor computation at a literal-zero predecessor, repaired by a
  nonliteral zero alias as detailed below.
* Rejection of a future witness parameter, context leakage, a wrong
  computation endpoint and the unproved contradiction 0=1.
* Unused valid records and a genuinely multiline whole-JSON document.

The verifier also checks exact control/candidate hashes, equality of complete
function ASTs after the reader replacement, both transducer directions and
exact whole-module size measurements. This is finite regression evidence,
not a machine-checked soundness or completeness proof. A separate dedicated
compound-progress mutant counterexample is not claimed; the unchanged mode
selector is covered by function-AST identity and the positive compound-case
fixture, together with the universal lockstep argument.

THE LITERAL-ZERO PREDECESSOR REPAIR

Let Z = I(0,0;u.0). Its raw tree is [0,0,0], which is nonempty and thus serves
as a permitted source in the successor-computation leaf. Let
F(v) be I(Sv,0;u.0)=0. The four chronological records prove F(0):

1. Goal F(0).
2. Equality transport from Z=0 and F(Z), using the template F(v).
3. The zero-computation leaf Z=0.
4. The successor-computation leaf F(Z).

The active-hole scalar 17 in the template lies beyond the protected depth;
it is replaced by Z or 0 before the fresh floor is allocated. This certificate
uses the inherited nonzero-source transport protocol and a truthy zero alias;
it does not add the missing literal-zero source case as a new axiom.

LIMITS

These checks do not establish an absolute smallest axiomatization, do not
remove an arithmetic or logical primitive, and do not lower the all-framing
243-token/264-node envelope or the 473-byte envelope. The ordinary arithmetic
and logic, raw sorted-array decoder, and bi-interpretation proofs remain
attributed dependencies of the pinned repository. Physical stack/memory limits
can reject sufficiently large finite proofs, as for the controls.
