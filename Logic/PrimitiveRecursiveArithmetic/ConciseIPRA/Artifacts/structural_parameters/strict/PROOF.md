# Correctness argument for the shifted strict checkers

## 1. Scope of the claim

These three programs are checking presentations of the pinned repository's
native scalar calculus. The claim consists of soundness for every accepted
public input and completeness for the canonical native encodings of theorems.
It is not equality of arbitrary raw certificate traces. In particular, the
parsed sorted grammar is broader than the canonical syntax; references to
constructor dummy slots are excluded from the completeness claim.

The proof below is a compositional mathematical argument from the pinned
native calculus and its proved opening and interpretation lemmas. It does
not claim an independent mechanization of Python or the full iPRA bridge.

## 2. Exact source changes

The token and AST profiles compose three changes to `scope_phase` entry
reservation:

1. Replace the lazy missing-image fallback
   `(d % 2 or not k) and i(t,d=3)` by the eager product
   `d % 2 * i(t,d=3)`.
2. Add the even offset two to every sorted depth: the formula root is 2,
   the term root 5, and the exposed one-slot matrix depth 4.
3. Replace the initial scalar-zero neutral by scalar one, represented by
   `b'\x01'` in the initial sequence of hypotheses.

For the AST profile, the initializer `k := 0` is moved from the lambda's
default to a preceding `k = 0` statement. The lambda's formula depth then
becomes the constant two. This preserves initialization order and values.

The byte control already has the eager opener. Its changes are only the
even depth offset and the initial context `[[]]` becoming `[1]`.

The floor decrement, global entry-reservation schedule, witness-before-major
evaluation order, exact atomic progress selector `len(a) == 2 == u`, direct
terminals, and inferred/explicit major mechanisms remain unchanged. The
runner verifies precisely these source rewrites and no others, modulo Python
AST normalization.

## 3. Shifted sorted reading

At a term position below p protected slots the depth is `5+2*p`; at a formula
position it is `2+2*p`. A term scalar from zero through four denotes numerical
zero. Slot j occupies the interval `[5+2*j,7+2*j)`. A scalar in `[k,0)` is the
rigid numerical parameter with that name. Upper scalars expose substitution
holes as in the inherited sorted reading. Formula scalars have the neutral
reading `0=0`.

Array meanings are unchanged. At term sort, unary arrays are successor and
ternary arrays are the iterator. At formula sort, binary arrays are equations,
unary arrays are the paired binder D, and ternary arrays are the auxiliary
closure Q. Unexpected auxiliary arities and empty arrays retain their neutral
readings. Successor protects two dummy slots; an iterator's counter and
initializer protect one dummy slot, while its body protects its state slot.
The arity increment `5-r` is the same in source and target.

The canonical syntax translation fixes scalars below three and adds two to
each scalar at least three. It fixes negative names. A genuine slot therefore
has the same index, a zero has the same value, and an exposed coordinate stays
exposed. Constructors and literal control values, including progress marker
two, are unchanged. For every canonical expression, source and translated
target have the same ordinary arithmetic reading.

## 4. Public validation and eager opening

Initially `k=0`. The first goal scan checks the same arity and scalar-parity
conditions at the shifted depth: arrays have arity 1 or `2+d%2`; scalars have
odd depth and odd value with `0 <= a < d`. Every permitted public scalar is
positive, so `a or 1` fixes it.

For an invalid array, the scalar comparison is undefined and checking fails.
For an invalid scalar, the fallback tries to validate the missing-image
sentinel, which fails. The eager product evaluates that image even at even
depth. Consequently a bad formula scalar cannot silently turn into truth
during the initial scan. The gate on the printed parsed JSON value admits
exactly finite integer/list trees and rejects a forbidden value even in an
unused prefix. Neither validation gate has been deleted.

After the first scan, entry reservation makes k strictly negative forever.
The same expression now performs the permissive auxiliary reading. At odd
depth the eager fallback inserts a validated term image. At even depth it
multiplies that validated result by zero. The result is either scalar zero
or the empty list, both of which denote truth at formula sort. This is a
semantic equality; it does not rely on the false Python equation `0 * [] == 0`.

At shifted formula depth two, administrative scalar zero is in range and
normalizes to one. One belongs to every context because it belongs to the
initial context and context extension retains existing hypotheses. Therefore
a neutral major supplied as zero closes immediately. The byte translation
changes its old empty major to this scalar-zero administrative major.

The usual structural proof of semantic opening is unchanged by an even depth
offset. Parity, the number and order of slots, arity increments, and negative
names are unchanged. Inserted images are checked at the shifted term root.
The uniform-zero convention `a or 1` preserves the numerical reading. Extra
eager checks may reject some formerly accepted noncanonical annotations;
soundness is proved from their readings, not by asserting literal equality
of every source and target run.

## 5. Freshness and evaluation order

Let K be the global floor on entering a call. Its goal is scanned at K before
the membership tuple evaluates its first element `k := K-1`. Write
alpha=K-1. Alpha is an additional arbitrary parameter available in packet
annotations; it is not the discharge eigenparameter for the current call.
Its absence from the old goal and context permits ordinary parameter weakening.

For a nonterminal call, the witness-dependent preimage of the new hypothesis
is formed at alpha, before the recursive major call. The major scans its own
goal before its own entry decrement. If beta is its returned global floor,
then beta < alpha. Every semantically active numerical parameter in the
already formed preimage, witness, old context, and old goal is at least alpha.
Beta is therefore fresh for all of them. The continuation can use beta and
its successor exactly as the inherited native inference requires.

The newly reserved first member of the membership tuple cannot by itself
discharge a goal: a successfully scanned scalar at floor K is an old retained
scalar or a neutral, never the new negative integer K-1; an array cannot equal
that integer. The member performs reservation only.

In the four-field program the replacement endpoint is evaluated after the
major returns. This is the inherited safe case distinction: a literal equality
or Q major supports its respective replacement, while a unary D major or a
false administrative major cannot match the equality/Q pattern. In the latter
cases the witness preimage was already formed at alpha. No witness-dependent
expression is first opened after beta becomes available.

These assertions concern semantically active positions, not a claim that
every integer in every discarded raw annotation is literally in scope. The
source's nested-template/exposure lemmas supply that qualification. Our changes
do not move or weaken any operation used by those proofs.

## 6. Soundness

Induct on the finite successful tree of recursive calls. Hypothesis terminals
are assumptions with their inherited readings. Computation terminals have
their inherited computation-equation readings and zero-instance argument
where needed for auxiliary aliases. A nonterminal's actual or reconstructed
major is checked recursively before use. The semantic opening/exposure lemmas
justify equality transport, Q specialization, and D elimination. The witness
preimage and fresh beta from Section 5 justify introduction. Progress remains
restricted to a literal binary equation by `len(a) == 2 == u`; case introduction
retains its existing mode. Neutral scalars/arrays always read as truth.

The initial public validation and whole-input gate establish the external
contract, and every subsequent step is an inherited native inference under
the shifted reading. Thus every accepted public goal has a native derivation
of its ordinary reading. Eager validation and added zero aliases introduce
no arithmetic axiom or inference rule.

## 7. Canonical completeness and certificate translation

Start with a canonical native proof tree and its entry-reservation compilation
from `scope_phase`. Its compiler assigns fresh negative names in the same
schedule as these candidates. Shift each upper coordinate by two and leave
negative names and flags zero, one, and two unchanged. Every actual canonical
term image is properly scoped, so the additional eager validations succeed.

For the three-field protocol, the source administrative major is zero; the
target opens it to its initial neutral one. For the four-field protocol,
replace the source empty-list major by zero. Genuine formula majors are not
changed. The relative packet order, inferred-major endpoints, and freshness
schedule remain the same. A direct terminal may prune subtrees; as in the
source compiler, emit only the consumed packet in that case, so no discarded
subproof packet is mistaken for a continuation packet. This is an inherited
branch-aware requirement of the direct-terminal protocol.

The source grammar's constructor dummy slots must not be confused with real
bound variables. Canonical encodings never refer to them. In the pinned
repository, `composition_and_dummy_slots` gives the old code `[[5],[1]]` as
an obstruction to extending completeness to every parsed alias under the
all-dummies-zero reading. The shifted spelling is `[[7],[1]]`. Completeness
here concerns canonical native representations only; no total equivalence
between all old and new raw certificate sets is asserted.

## 8. Transfer to first-order iPRA and limits

The ordinary realization is unchanged. It uses the whole numerical domain,
actual equality, and the established term translations whose composites are
provably identity. Both formula round trips are inherited. Composing the
preceding checking-presentation theorem with that native-calculus bridge
preserves bi-interpretability and equiconsistency with first-order iPRA.
This package supplies a representation refinement, not a replacement proof
of the foundational bridge.

The measured source sizes count the whole checker modules, including imports,
parsing, validation, and acceptance output. They do not count the test runner
as trusted code, because no checker imports it. The three component records
belong to different programs. Neither a global source-size optimum nor a
new complexity lower bound is proved. Finite regression evidence supports
the implementation; it does not substitute for the semantic argument.

## Pinned references

Repository: `VladimirReshetnikov/ProveIt`, commit
`0198424b74acc33db20c5180c8019ecd7d14a75a`.
All paths below are under `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/`.

* `Artifacts/scope_phase/evidence/PROOF_NOTES.txt`: public grammar, corrected
  atomic mode, entry reservation, delayed endpoint, canonical compilation.
* `Artifacts/scope_phase/evidence/entry_reservation_review.md` and
  `nested_template_lemma.md`: detailed scope and exposure qualifications.
* `docs/Article/chapters/ch11_cert.tex`: the sorted reading and opening,
  exposure, fresh-name, eager, uniform-zero, validated-terminal, zero-instance,
  and even-offset results.
* `Artifacts/composition_and_dummy_slots/proofs/independent_second_dummy_proof.md`:
  why raw-grammar completeness is stronger than canonical completeness.
* `docs/Article/chapters/ch01_base.tex`: the whole-domain iPRA bridge and both
  formula round trips.
