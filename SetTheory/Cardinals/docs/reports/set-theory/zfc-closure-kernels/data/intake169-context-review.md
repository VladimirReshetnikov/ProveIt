# Context-reuse and contextual-reuse: source comparison

Both primary machines are already represented by the current primary242A
construction. Contextual-reuse's inherited table is byte-identical to primaryA.
Its canonical file differs only by the added `#! start 0` header. Context-reuse
is the exact same transition system after renaming the retained state 15 to
27. Every one of the 484 transition rows agrees under that bijection.

The table comparison and all new derived table expressions were static:
no transition was executed, no delivered program was imported or run, and no
compiler was invoked. The source reviewer authored the pending Fold241 Lean
port and is not an independent author of that downstream proof.

## Exact machine changes and proof hypotheses

Relative to the pinned Combined243 table, contextual-reuse deletes 27, replaces
15/0 by `0 L 32`, and redirects 18/0, 47/0 and 65/0 from 27 to 15. Its invariant
is old15/18/47/65 imply a zero immediately left of the head, and old27 implies
the currently scanned bit is zero. The map 27→15 matches all old steps in one
new step except old15/read0, whose detour is 15→32→45→21 in three steps. This
is exactly the primary242A proof architecture already being formalized.

Context-reuse instead deletes 15, redirects 11/0 to27, and changes27/1 to
`1 R 22`. Its older callers still force27/read0. The new caller11 writes the
extra left zero, permitting27 to implement the deleted15's read-one branch
and its longer read-zero return. Its proof uses identical full-tape comparison
boundaries outside15/27: five cases, with old/new lengths2/4,2/2,2/2,2/2,2/2,
and478 ordinary rows. This is a sound alternative proof decomposition of the
same renamed machine. It does not imply that the27 invariant holds on all new
visits to27, and the manuscript correctly avoids that assertion.

The stronger exact isomorphism is important: these are not two independent
one-state savings. Deleting both15 and27 would remove the common control which
implements the shared behavior. Neither proof supplies a replacement for it.

Both descriptions permit the subsequent39→17 fold. In either242 table, the
only incoming17 row is12/1, writing1 and moving right; the only incoming39
rows are46/0 and50/0, both writing0 and moving right. All12 distinct transition
rows used by the four241 detours are unchanged. Applying the existing four
fold patches yields current241 from primaryA, and precisely its15→27 rename
from the context-reuse table. Thus this composition yields the same241 machine,
not240.

The underlying ordinary proofs allow arbitrary function tapes. The pending
Lean Core ports use arbitrary finite-support tapes. Neither report supplies
a fresh kernel proof or an internal PA calibration, and this review makes
no such upgrade.

## Useful distinct material

Context-reuse contributes a maximal power-of-two residue acceptance theorem
for the unchanged numerical calculus. A derived code may be accepted when
it is odd and is not3 modulo16. Membership atoms refute by irreflexivity;
off-diagonal equality atoms refute because the native theory forces at least
two objects. Diagonal equalities have code16·T(i)+3. Every remaining residue
class modulo2^k, k≥4, contains an unconditional theorem from implication-to-
truth, universally quantified truth or reflexive equality. The triangular
number permutation argument supplies the exact maximality proof. This goes
beyond the earlier membership-only criterion, but requires the full native
soundness/completeness bridge. No cheaper modulo16 detector or binary table
is supplied. It can coexist mathematically with the relative241 fold, but
changing the enumerator invalidates a direct reuse of the current literal
source/runtime certificate until a complete implementation and new proof are
provided.

Its162-layout screen considers four additional H-transfer loop rotations and
two QT associations, including surrounding control-flow checks. The best
6455-leaf source still has202 decoder subtrees. This is useful source-level
equivalence and sharing evidence; the census alone supplies no binary-state
saving. The 19 modulo4 layouts cost205 or206 decoder nodes in their actual
context, so they currently offer no measured decoder improvement. The broad
closure/finite-quotient formalism survey mostly identifies inherited work and
remaining compilation obligations.

Contextual-reuse contributes a precise selector-dispatch satisfiability
theorem. Four binary functions V/A/U/F are replaced by H(tag_f,x,y). The
selector coordinate remains outside interpreted Eq congruence, while the
two object coordinates respect Eq. A product model gives distinct actual
selectors even if they belong to the same Eq class; the reverse quotient
fixes each actual selector. No minimum model cardinality is required. The
delivered experiment reports a complete2194-bit packet, compared with2324
bits for the inherited packet, under its fixed family of203 partitions.
These are delivered results only; this review has not rerun them.

## Concrete combination with the detour report

The dispatch theorem is compatible with the detour report's membership
elimination and truth-constant fusion. Perform those finite clause/model
transformations with their original proofs, retain all remaining Eq/Inc
obligations, and then use object-coordinate dispatch. The packed membership
definition is

`Inc(C(C(d,d,x),I(d,d),y),H(tag_A,d,I(d,d)))`.

Its omitted membership-congruence law follows from C congruence, reflexivity
of that fixed H ground term, and Inc congruence; selector congruence is never
needed. However the reported130- and556-bit savings cannot be added: naïvely
retaining the1768 packet's alias with dispatch gives12 symbols plus5 local
variables, requiring17 opcodes and returning to five-bit encoding.

Two concrete source proposals avoid that threshold: omit the alias and use
11 symbols plus5 variables, or split C and H congruences into single-coordinate
laws, retaining the alias with12 symbols plus4 variables. The latter splits
are interderivable using reflexivity and Euclidean Eq. Their exact root-run
builder and ordinary proof are frozen separately under
`/tmp/zfc-joint-equational-packet`. Independent Horn certificates are supplied
by Opening. There is no measured joint bit count in this source-review record.
No equational packet size is converted into a Turing-machine state claim.

## Read and evidence scope

Read both complete top-level manuscripts and READMEs; the source-layout,
acceptance-residue and formalism proof sections; both local proof checkers,
the contextual induction checker, context constructor, residue arithmetic
checker, complete dispatch proof and packing program; and the detour1768
proof and two transformation programs relevant to composition. The inherited
codec/Boolean builder and ground-rewrite kernel were also read for the joint
proposal. Generated TM tables were independently parsed and compared exactly.
Runtime, blank and expanded results cited by the reports remain author evidence;
this task executed none of those suites and makes no comprehensive runtime-code
audit claim.
