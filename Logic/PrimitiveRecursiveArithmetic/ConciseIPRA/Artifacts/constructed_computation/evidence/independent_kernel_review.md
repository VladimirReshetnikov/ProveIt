# Independent review of the constructed computation source

## Finding

The frozen compact checker is `code/checker.py`, with 279 normalized tokens,
314 AST nodes, and 682 normalized bytes under the unchanged corpus utility.
Its explicit arithmetic flag eliminates the need to validate a submitted
successor wrapper. The checker itself constructs that wrapper.

This is a proof-certificate and trusted-source reduction, not a new numerical
basis or a new arithmetic strength result. The ordinary semantic rules and
bi-interpretation are inherited from the scalar Choice-DI/Supply calculus.

## Generated computation

For a computation command, let the packet's fields be `[m,s,u,t]`, with
`m` and `t` falsy. Decompose `s=[n,a,r]`. The old unused `u` field now chooses
base mode (falsy) or successor mode (truthy). The generated raw equation is:

- base: `I(0,a;r)=a`;
- successor: `I(Sn,a;r)=r[I(n,a;r)/state]`.

Canonical flags are 0 and 1. The implementation builds the left counter as
`u and [n]`, hence a step command always creates exactly one successor
constructor. The packet carries a predecessor, not a purported successor
constructor. In base mode the predecessor field is inert and may even be
non-syntax JSON; it does not occur in the generated equation.

The raw source `s` in the successor right-hand substitution always has arity
three. The former eager normalization of `[ *counter, seed, update ]` served
as a check that the submitted counter was a singleton. That check is no
longer necessary: no submitted successor wrapper is accepted as authority.

## Why raw aliases do not invalidate the equation

The final common continuation normalizes the generated equation after one
fresh parameter `w` is allocated. Its zero instance suffices for the
inherited Supply rule: if `H(0)` is a computation theorem and `w` is fresh
for the end sequent, `Gamma,H(w) |- A` implies `Gamma |- A` by substitution
of zero followed by cut.

Base mode follows immediately from I0 after the inherited zero-extension
lemma aligns the two dummy slots on the initializer's left occurrence with
its occurrence on the right. The update can contain the new parameter;
I0 imposes no restriction on a passive parameter of its fixed update.

Successor mode has two distinct cases.

1. If the update opener demands the recursive image, its normal scalar
   substitution branch calls `i(s,d=1)`. This validates the entire recursive
   iterator source at the old scope floor, including its predecessor,
   initializer, and update. In particular it excludes exposed higher raw
   coordinates in the update: they cannot be silently identified with the
   recursive state. Successful opening is ordinary capture-free substitution
   of this checked image. The zero-extension lemma then aligns the added
   dummy zero under the constructed successor with the predecessor in the
   recursive image. The generated equation at `w=0` is IS.
2. If the opener never demands the image, the update is independent of the
   outer iterator state in the decoded numerical meaning. Exposed formula
   annotations may be discarded as truth, but such annotations have no
   numerical meaning. The recursive state's shape and scope are then
   irrelevant to the right-hand numerical value. The final traversal still
   checks the constructed left source. Substitution `w=0` gives IS for its
   state-independent update. Eagerly checking an unused recursive image
   would impose an unnecessary additional proof-format condition.

This case split is essential. Merely deleting the old eager check while
keeping a submitted successor wrapper is unsound: a binary numerical-zero
alias can otherwise be mistaken for a positive counter. The included
negative examples and mutation test demonstrate the distinction.

All other inference branches are unchanged. The two source-initialization
folds have identical Python evaluation order to their separated forms:
`d=(k := 0)` initializes the global floor once, when the lambda is created,
and keeps default depth zero; the assignment expression in the initial
check call binds `q` before popping the requested theorem. These folds are
inherited corpus implementation techniques, not mathematical novelty.

## Canonical completeness and comparison

A canonical old I0 packet becomes a base packet with predecessor 0. A
canonical old IS packet whose source counter is `S n` becomes a successor
packet carrying `n` and flag 1. The generated equation and the number and
order of continuations are unchanged, so all rigid labels and later
logical packets are preserved. The untrusted named producer implements
this transformation directly. No producer code is imported by a checker.

The unprofiled constructed-source checker measures 277/317/684. Folding
initialization yields the delivered 279/314/682 program. For a fair local
comparison, applying the same folds to the inherited checker produces
283/315/683. Thus the arithmetic source construction itself improves that
matched control by four tokens, one AST node, and one normalized byte.
The current corpus coordinate envelope 281/315/685 is attained by different
programs; the delivered program is strictly below each coordinate.

The savings are small. They establish an attained implementation improvement,
not an absolute minimum, not a proof-checker lower bound, and not a large
mathematical breakthrough.

## Executed checks

- 33 realistic and malformed certificate cases on both complete programs,
  in default and `-O` mode, plus malformed input controls: 144/144 passes.
- Three mutation controls expose the successor construction, major-proof
  check, and literal-equation restriction on progress introduction. Each
  corrupted kernel accepts its selected invalid proof; each genuine kernel
  rejects it.
- All 28 legacy fixtures are accounted for: 26 canonical conversions, with
  24 identical to already replayed packets and 4 additional CLI runs for
  the two differing packets. Two obsolete counter-wrapper negatives are
  replaced by legal predecessor examples and requested-false-equation
  negatives. All applicable outcomes pass.
- Independent raw-generator audit: 76,960 attempted packets, 57,640 successful
  generations, and 518,760 standard-model valuations at fresh variable zero;
  all equalities hold. This includes fractional serialization aliases,
  nested iterators, missing or future labels, and dummy slot boundaries.
  No resource-bound exceptions occurred in this fixed audit.

The finite tests support the implementation. They are not a formal proof of
universal soundness, canonical completeness, or bi-interpretability.
