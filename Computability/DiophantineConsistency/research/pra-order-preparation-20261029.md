# Preparing the remaining Robinson Q order clause

`PRASubtraction` proves in the candidate PRA the universally closed recursion
laws `x−0=x` and `x−succ(y)=pred(x−y)` for the actual represented subtraction
code. `PRANonzero` proves `nonzero(0)=0` and `nonzero(succ(x))=1` for the actual
nonzero-test code. Their proofs derive the equations in arbitrary equality
models of the candidate theory and use Foundation completeness.

`PRANonzeroCharacter` strengthens this to a closed proof of the exact sentence
`∀x, nonzero(x)=1 ↔ x≠0`. In every equality model it uses the theory's
successor-nonzero axiom and its induction-based predecessor exhaustion theorem,
so this covers nonstandard elements as well as natural numbers. This connects
the actual order-bit's nonzero test with inequality; the separate arithmetic
argument connecting truncated subtraction to an additive successor witness
remains necessary for the omitted Robinson Q order clause. No full Q
interpretation, PRA conservation or consistency equivalence is claimed.

The subtraction and nonzero main/check pairs compiled privately using Lean
4.32, `-M6000 -j1 -DElab.async=false`, with respectively seven and six
standard-only axiom reports. Subtraction used
`/tmp/pra-subtraction-author-ngo4rz90/lib`; nonzero used
`/tmp/pra-nonzero-current-5guhyltg/lib`, based on the later
`/tmp/pra-q-current-refresh-5t4dxi2l/lib` source refresh. Its six initial
scratch snapshots, including admitted trace probe 6, are preserved under
`/tmp/pra-nonzero-author-2wzd1rfn/logs`; the final current-provider source has
no admitted proof. All subtraction attempts and checks are preserved in its
private `logs`; neither subtraction attempt used `sorry`.

After the subsequent PRAExhaustion source change, that exact module was
freshly rebuilt and the nonzero-character main/check pair compiled under the
same flags in `/tmp/pra-nonzero-character-current-ri0f5k9b/lib`. Four axiom
reports use only `propext`, `Classical.choice`, and `Quot.sound`; the complete
final main log is empty. The initial seven character snapshots and diagnostics
are in `/tmp/pra-nonzero-character-author-sn02ocqx/logs`; attempts 2–5 were
admitted goal-inspection probes, not accepted evidence. Foundation and Mathlib
remain inherited provider boundaries. Independent review and replay of the
new pairs are separate.

## Open induction and left addition zero

The [independent replay](../reviews/pra-open-induction-root.md) validates an
open-induction interface for arbitrary parameters in candidate-PRA equality
models and a closed candidate-PRA derivation of `0+x=x`. Addition
commutativity and the additive-witness definition of order remain to be
derived; these are prerequisites for the full Q compatibility route, not
proof of standard PRA equivalence or Parsons conservation.

The [left-successor law](../reviews/pra-addition-succ-left-root.md) is now
a closed candidate-PRA derivation, with an independent current-source replay.

The [addition commutativity law](../reviews/pra-addition-commutativity-root.md)
is also a closed candidate-PRA derivation. The subtraction and additive
witness arguments needed for the Q order clause are still separate work.

The independently replayed [subtraction laws](../reviews/pra-subtraction-laws-root.md)
now provide closed candidate-PRA derivations of simultaneous-successor
cancellation and `(x+y)-x=y`. The reverse direction from nonzero
subtraction to an additive order witness still requires proof.

The [reconstruction law](../reviews/pra-sub-reconstruct-root.md) now derives
`y-x=0 ∨ x+(y-x)=y` in the candidate theory. The full Q order clause still
requires composing this with the nonzero and successor witnesses.
