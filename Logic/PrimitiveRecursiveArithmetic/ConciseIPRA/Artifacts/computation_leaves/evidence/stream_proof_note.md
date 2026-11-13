# Computation at leaves: proof and exact boundary

## What changes

The old compact supply checker has a third continuation alternative: construct
an iterator equation, put it in the retained context, allocate another fresh
numerical parameter, and continue checking the original goal. The new checker
recognizes precisely that constructed equation as its current goal and closes
that leaf. Its remaining continuation is either paired elimination/ordinary
transport, or paired introduction. It never adds a computation equation to the
context merely to make it available for later lookup.

This is a change of proof presentation and certificate protocol. It is not a
new arithmetic axiom and it does not reduce the underlying native logical
basis. It genuinely removes a continuation alternative and its dependency on
the initializer's truth value. In particular I(0,0;u.0)=0 now has the single
certificate record [0,0,0]; the old three-field supply interface cannot use that
record as computation supply because its initializer is falsy.

## Public contract and inherited interpretation

The small records are measured on exactly the incumbent compact contract:
finite trees made of exact integers and lists, with the closed public goal
restricted to the canonical guarded Eq/D language. No complete certificate
alphabet or public-goal grammar validator is included in these modules.
The arity decoder, the hole-opener i, the meaning of surplus arrays as 0 or
truth in their sorted positions, and the retained-context rules are inherited.
They remain part of the specification and are not omitted from the mathematical
argument. In particular these programs are not a claim to completeness for
all raw unguarded native D formulas. The root-dependent introduction treats
literal equations by progress and compound matrices by cases; the public gate
translation is indispensable.

Under the inherited sorted decoder, a numerical triple [n,b,h] denotes the
scalar iterator I(n,b;u.h), an equation is [s,t], a unary formula [B] denotes
D_{x,y} B, and a canonical closure is [B,B,B]. The increment 5-len(a) gives
exactly the protected-coordinate increments required by these constructors.
A fresh negative name is allocated only by a non-leaf logical continuation.

## The new leaf

At the current scope floor k, first check i(a) in the usual way. Given the
three supplied fields r=[s,u,t], form

    H(r) = [[s and [s],u,t], i(t,r,3) if s else u].

If a is literally H(r), close the goal. Thus the falsy-counter case is the
zero iterator equation, and the truthy-counter case is the successor iterator
equation. This does not decide a numerical term's semantic value. For example
a truthy term provably equal to 0 is still treated as a predecessor source,
while literal 0 selects the base equation.

The same source limitation as in the incumbent remains: the direct successor
leaf uses a truthy predecessor spelling. Successor computation at literal 0
can be recovered by the inherited proved-zero anchor and equality reasoning.
It is not silently assumed to be a direct instance of the raw leaf matcher.

### Soundness

Suppose the leaf succeeds. The equality a=H(r) enforces root equation arity,
and the prior successful i(a) check enforces all relevant numerical scope
conditions. If s is falsy, its accepted exact-integer/list representation
means 0, so the equation is an I0 instance. If s is truthy, its occurrence
inside the constructed singleton [s] is a successor. If the step body uses
its state, i(t,r,3) checks the entire recursive image at numerical root depth
3 before inserting it. This is exactly the recursive-image condition in the
inherited constructed-computation lemma. It ensures that the predecessor,
initializer and update of the right-hand recursive image have the same
meanings as those on the left. If the body does not use its state, the
right side is independent of that image and the successor equation is still
valid. Ignored numerical annotations and formula truth aliases retain the
inherited constant readings.

There is no fresh parameter introduced by this leaf. Consequently the old
supply argument's auxiliary simultaneous-zero substitution is unnecessary
here: H(r) is already the checked goal in the present scope. Successful raw
auxiliary aliases do not add an axiom; they decode to the same computation
schema. The other branches are literally the old retained-context logical
branches with the supply alternative removed, and their inherited soundness
proofs apply unchanged. Induction on the finite accepting call tree gives
soundness for every accepted input satisfying the public contract.

### Why the attempted leaf does not destroy canonical completeness

The implementation attempts H(r) before the logical dispatch, so it may
reject a noncanonical logical packet during this attempted computation.
We do not claim equality of raw accepted certificate sets.

Canonical formula templates use their first unprotected numerical slot
(or its paired alias) for the substitution hole. At a node whose ordinary
opener depth is d, those hole coordinates are d or d+1. In the attempted
computation, the very same tree t is opened at root depth 3, rather than 0.
Every recursive depth is therefore increased by exactly 3. All canonical
hole coordinates are now protected, so i(t,r,3) is defined and simply
preserves the template; it does not inspect r as an inserted image.
A canonical paired-elimination packet uses t=0. An introduction packet uses
s=0 and does not evaluate i(t,r,3). Thus every canonical logical instruction
has a well-defined preliminary leaf test. If it matches, the goal was already
a computation theorem and may safely be closed; otherwise the intended
logical continuation proceeds.

### Completeness and removal of supplies

At the mathematical proof-tree level, replace every use of a retained
computation theorem by its computation leaf. Remove the administrative node
that retained the theorem. Rename the eigenparameters of the remaining
logical nodes to their new allocation order. Hypotheses supplied by logical
rules remain hypotheses. This is ordinary substitution of an axiom derivation
for a hypothesis occurrence, not an appeal to consistency.

For canonical supplies, every retained formula is the actual computation
instance, and the transformation is a direct induction on the old proof
tree. There is no need to reproduce the enlarged raw alias alphabet of an
arbitrary old certificate. The inherited canonical completeness theorem may
be used to choose a canonical proof first. If a historical supply used only
a known-zero instance in auxiliary fresh names, first apply its proved
simultaneous-zero transformation at the ordinary native derivation level,
then choose a canonical guarded proof. The restricted raw syntax need not
be closed under arbitrary substitution for this argument.

Conversely, an axiom leaf is a native computation equation, while all other
new rules are inherited native-derived rules. Thus both presentations have
the same canonical guarded public consequences. Composing this equivalence
with the inherited guard translation and the whole-domain native/iPRA bridge
gives the intended bi-interpretation and equiconsistency. Neither numerical
standard-model agreement nor finite execution tests substitute for this
argument.

## Executable producer and validation

compile_leaves.py is an untrusted, independent producer. It first parses an
accepted certificate of the pinned local three-field supply checker into an
inference tree. It then closes recognizable computation goals directly,
erases unused supply nodes, replaces uses of computational assumptions by
leaves, and renames negative eigenparameters for either local or global floor
allocation. Its outputs are checked by the standalone measured modules.
The producer is evidence of the finite transformation on the supplied corpus,
not a claimed formalization of the universal completeness theorem.

The five inherited positive fixtures include both computation branches,
inferred equality major, equation induction whose hypothesis is actually
used, and implication elimination on a compound formula. All five produce
accepted certificates in both new modules. The last two shrink from 1541 to
268 records and from 664 to 100 records respectively. The five inherited
negative fixtures (false equality, altered computation endpoint, future
witness capture, context leakage, and future-scope attack) are rejected.

The two new profile measurements are:

    goal_compute_global.py : 243 significant tokens, 271 AST nodes, 616 bytes
    goal_compute.py        : 248 significant tokens, 264 AST nodes, 613 bytes

A separate byte profile is being maintained by the independent checker
reviewer. The coordinate envelope is not the size of one program. Normalized
source is ast.unparse(ast.parse(source)) plus one final newline; the measured
program includes its import, input/output driver and success print.

The packaged verifier additionally includes a shared-computation fixture.
Its old proof retains one computation equation and uses it twice to prove
S(0)=S(0). The producer erases that supply and replaces its two hypothesis
uses by two computation leaves. This example goes from two to three records;
it confirms that the result concerns checker size, with no promise of shorter
certificates in every case. The final stream receipt records 12 exact
producer replays and 56 checker processes, all passing.
