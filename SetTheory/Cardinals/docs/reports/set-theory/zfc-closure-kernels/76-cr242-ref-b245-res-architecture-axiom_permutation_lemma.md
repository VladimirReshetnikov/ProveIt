# Arbitrary axiom-row permutation: the exact proof-program translation

This observation preserves all eight published logical axiom schemes, the
fourth parameter of the Lukasiewicz scheme, GEN, and the gated theory bundle.
It is independent of any conjecture about a smaller propositional basis.

## Source convention

Write the push order of the eight logical schemes as a permutation
`pi = (pi_1,...,pi_8)` of `{1,...,8}`.  The published order is
`(8,7,6,5,4,3,2,1)`.  AX first pushes the old current formula, then GEN of the
incoming cache, then the eight rows in order `pi`.  The gated theory bundle
becomes the new current formula.  Thus the theorem stack after AX, from top
down, is

`rho_(pi_8), ..., rho_(pi_1), GEN, old_current, old_stack`.

The high-level register semantics is exactly the one in the pinned
`ZF/m254/coq/logic/Enum254.v` and `L1_Comp254.v`, with only `ax_stack` changed.
The source builders must still preserve the scalar parameters and restore
their scratch registers.  The unique read of `u` may move with rho8 because
the other seven rows leave the unconsumed command list unchanged.

## Selector formula

Let `pos_pi(j)` be the one-based position of `j` in the push order.  Define

`k_pi(j) = 9 - pos_pi(j)`.

Then `k_pi(j)` pops select rho_j into the cache.  Replace the published leaf
block

`DISCARD ; AX(c,a,b,u) ; NIP^j ; DROP ; NIP^(11-j)`

by

`DISCARD ; AX_pi(c,a,b,u) ; NIP^k_pi(j) ; DROP ; NIP^(11-k_pi(j))`.

Starting at `(current=T, stack=W, counter=0, cache=0)`, DISCARD produces
`(0,W,0,0)`.  AX pushes exactly ten stack entries.  After the first `k` NIPs,
the cache contains the desired row and the stack has `10-k` new entries.
DROP installs that row as the current formula and pushes the gated bundle.
The final `11-k` NIPs remove this bundle and all remaining new stack entries,
ending at `(rho_j,W,0,0)`.  All intermediate axiom-row and GEN codes differ
from the halting code F=1.  The final cache is the saved zero.

Both leaf blocks have exactly 25 commands and 54 encoded fields, including
DISCARD.  Thus permutation changes the selector position, without increasing
the syntactic length of the proof compiler's output.

## The other compiler blocks

The published DISCARD block removes all ten new stack entries, so its proof
does not depend on their order.  The bundle leaf removes ten entries.  GEN
selects stack slot nine, because exactly eight axiom rows remain above GEN.
The MP cleanup also removes ten entries.  Therefore those blocks retain their
published definitions and contracts.  START and the final
`DROP ; NIP ; NIP` suffix also retain their definitions.

Induction over a `thm254` derivation D now gives a compiler C_pi(D) with the
same block contract as the published compiler: from `(T,W,0,0)`, it either
halts early or returns `(formula(D),W,0,0)`.  Only the eight logical-axiom leaf
clauses use the new selector `k_pi`.

## Exact candidate number

For the dual Cantor pairing `P(a,b)=(a+b)(a+b+1)/2+b`, retain the exact
published encoding:

* `fields(MP x)=[0,x]`, `fields(DROP)=[1,0]`, `fields(NIP)=[2,0]`, and
  `fields(AX(c,x,y,u))=[3+c,x,y,u]`.
* `enc_fields(fs,r)=fold_right P r fs`.
* `enc_tail([])=0` and
  `enc_tail(k::L)=1+enc_fields(fields(k),enc_tail(L))`.

For a derivation D of F, the explicit witness number is

`N_pi(D) = enc_fields(fields(START), enc_tail(C_pi(D) ++ SUFFIX))`.

This is a primitive-recursive function of a finite derivation and pi.  The
scheduler's existing reachability proof is unchanged: either it halts before
reaching `N_pi(D)`, or it reaches the start of that candidate.  The block
contract then forces a halt.  Conversely, the soundness invariant is
unchanged because AX pushes the same formulas in a different order.

Consequently the permuted high-level enumerator halts iff `thm254 F`, and its
nonhalting has the same ZFC-consistency calibration as the published
enumerator, provided the existing theory bridge is retained.

This does **not** assert a stepwise simulation, a permutation of all arbitrary
candidate numbers, or a binary-machine theorem for an unverified compiler.
It gives the precise witness translation needed for completeness, on the
image of the derivation compiler.  A new binary table still needs its own
compiler/runtime and blank-bootstrap verification.

## Related, distinct compression opportunity

The actual246-state machine has 127 transparent binary grammar states and
119 other states.  Its AX word uses 702 semantic-atom calls.  Expanding each
of the 44 existing semantic atoms into maximal closed control atoms gives a
word of 1,270 atoms.  The same expanded word admits a 533-call spelling in the
same 44-atom vocabulary.  This is exact word equality, not merely an
extensional arithmetic equivalence; it was independently checked from the
immutable 226-node semantic AST.

The shortest atom spelling is not automatically the smallest machine.  The
533-call spelling's initial shared grammar required147 rules, whereas the
published702-call spelling uses127.  A useful next search therefore keys
grammar nodes by their expanded closed word and jointly chooses (i) an
existing composite atomic implementation, including its incoming-bit
restriction, and (ii) a new binary grammar production costing one state.
Mandatory non-AX entry roots plus the exact blank-bootstrap rows force51
existing grammar states; the original AX adds76 private grammar states.
This provides a concrete cost target: at most75 additional states with the
119-state framework would yield245 working states.
