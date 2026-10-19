# Logical foundation and decoder-associativity audit

This note records a source audit, not a fresh Rocq or Lean compilation.
The fetched upstream snapshot is `c132d7eae8158cd3a9850ea3eb7251158c3dd821`;
the ProveIt snapshot is `8e012a51d6e7fdad4d903089536427a813009a4f`.

## What the original 254 endpoint actually proves

`ZF/m254/coq/e2e/E2E254.v` composes these exact propositions:

1. `halts tm c0 <-> rm_halts p254 ([], R0)`.
2. Register-program halting iff the numeric enumerator halts.
3. Enumerator halting iff `thm254 1`.
4. `thm254 1 <-> SIR ⊢TC ⊥`.
5. `SIR ⊢TC ⊥ <-> ZFc ⊢TC ⊥`.

The code literally declares both `zf254_halts_iff_ZF` and
`zf254_halts_iff_ZFC`, and requests `Print Assumptions` for each. The upstream
README reports closed global context; this session has audited the code but
has not independently rerun the Rocq compiler.

The set-theoretic bridge is syntactic. `S_main.v` uses `qt_tprv`, a
falsity-preserving atom-substitution translation of natural-deduction proofs.
`S_sound.v` uses a syntactic relativization of a finite SIR derivation to L
inside ZF plus Regularity, then applies syntactic relative consistency of
Regularity. `ZF/stdzf_r3/zfc/Z_main.v` handles Choice in the same manner.
This route does not assume the existence of a model of ZFC or Con(ZFC).

The exact named endpoint called ZFC uses `ZFc + ax_ac`, with ZFc not including
Regularity. For ordinary ZFC including Foundation, use
`ZFC.Z_main.ZFCReg_equicons`, whose left theory is
`fun phi => (ZFc phi \/ phi = ax_reg') \/ phi = ax_ac`.
This yields an immediate additional corollary by composing with
`zf254_halts_iff_ZF`.

## Distinguishing external proof from internalization

The exact 252-state Lean endpoint is explicitly documented by ProveIt as an
external metatheorem. `choice_calibration254.md` states that no internally
serialized ZFC machine statement is supplied there, and that PA proof-code
and finite-trace internalization is separate work. The Lean endpoint uses
external completeness after constructing an L submodel of any ZF model.
It retains no model-existence, Choice, startup, or coverage hypothesis.

An axiom report proves the theorem relative to a proof assistant's kernel
and foundational axioms. It does not by itself exhibit a first-order ZFC
proof code of the arithmetic equivalence, and it is not a proof of
nonhalting or Con(ZFC). The original syntactic Rocq route offers a direct
mathematical route to an ordinary ZFC proof: finite syntax, finite
transition traces, induction on derivations, and the explicit syntactic
relative-consistency translations can all be represented in ZFC. Claiming
a serialized internal proof requires actually supplying that representation
and the associated arithmetic statement.

## Conditions for changing a decoder bracketing

In Wade's structured semantics, a binary node first executes its car, then
its cdr; but it also catches breaks from its car and continues from its cdr.
Thus arbitrary reassociation is false. In particular, if A emits Break1,
A;(B;C) skips B,C, whereas (A;B);C skips B but executes C. Continue1 can
likewise restart a different enclosing node.

A sufficient condition for reassociation is that every finite execution of
each component A, B, C exits only normally or by halting, with no external
break or continue. Total termination is unnecessary for the equivalence of
finite normal/halting executions. If the components terminate normally,
both bracketings are simply relational composition; if one halts, both
stop at the same component and register vector.

A later, strictly weaker sufficient condition is proved in
`generalized_associativity.md`: **A has no escaping Break, C has no escaping
Continue, and B is unrestricted**. The proof computes the complete finite
exit relations, including arbitrarily many Continue(1) restarts. Both
bracketings have common restart relation `A_Normal ; B_Continue1`. This
is an ordinary mathematical proof; no proof-assistant build was run here.

The syntactic exit bounds used by `rebracket_axioms.py` are sound for this
purpose. For a node (A,B), with each bound a pair (break,continue), its bounds
are `(max(pred break_A,break_B), max(continue_A,pred continue_B))`.
An increment has bounds (0,0), a decrement (1,0), Break k has (k,0), Continue k
has (0,k), and halt (0,0). Structural induction shows that a (0,0) result
excludes all externally escaping control exits. These bounds may overestimate
possible exits; zero bounds remain sufficient.

## The attractive but unvalidated 178/208 rotation

Literal original labels in the 246 table are:

- 178 = (23,208)
- 208 = (24,206)
- 16 = (23,24)

All six rows preserve the bit and move right. The tempting rewrite is
178 = (16,206), deleting 208 if it has no remaining incoming edge. The three
semantic routines 23,24,206 have zero external control bounds. A finite
4,533-operation path-bisimulation certificate verifies the associated
abstract source reassociation, including both outcomes of every decrement.
That fact alone does not establish the concrete binary machine.

The actual table also reaches 178 through backward detours inside other
microinstructions. A failing changed-table symbolic case has PC
`11101001001010100111000000`, a zero decrement of logical topwff (physical
register 2). Its literal trace reaches
`235 -> 231 -> 237 -> 218 -> (L)154 -> (R)178` before running the padding
microcode. Rotating 178 changes that microcode too. The first guarded
arithmetic step completes, but a further unanticipated operation selects
physical register 0 and cannot satisfy the one-instruction target contract.

A pure right-moving source-to-table map saw eight occurrences of the
178 source subtree. Structural signature equality finds a ninth at source
node 4364 with inner node 4383. Adding that ninth rotation does not remove
the first literal affine failure (1,166 cases pass before it). Therefore
neither the eight-occurrence nor the nine-occurrence rotated source is a
verified specification of the 245-state table.

This is useful search evidence: semantic associativity is valid, but the
shared binary decoder is also part of runtime microcode. Any reduction must
account for every use of the edited rows in all phases or give a replacement
macro-simulation proof. Failure of this affine contract is not by itself a
proof that the table has the wrong final halting language; it is enough to
withhold a new consistency-machine claim.

## Independently checked local move-to-front arithmetic

`kernel_reduction/mtf-local.tex` presents a distinct 245-state local mutant.
Independent parsing and simulation confirm exactly three changed rows,
deletion of old state 255, 245 working states, and 490 binary transition
rows. The single former external incoming edge to 255 was 75/0.

The unbounded local proof is valid. With `B(v)=01^(v+1)` and `C(v)=101^v`,
the changed return implements `C(v) B(0) -> B(0) B(v)` using v instances of
a three-step adjacent `10 -> 01` swap and one two-step leading `10 -> 01`
swap. This gives `3v+2` steps and leaves both exterior tapes untouched.
Induction on the preceding register list A, combined with the unchanged
forward carry and the nine-step selected-zero boundary identity, yields
`B(A)00B(S) -> B([0]++A++S)` in `4*sum(A)+4*len(A)+9` steps, from state 95
at the first block to state 112 immediately to its left. S must be nonempty.

Positive decrement never enters the changed return rows. The increment
blank-end closure is replaced by a literal four-step sequence with exactly
the same endpoint. Its original local arithmetic contract therefore holds.

The independent audit also confirms the explicit header obstruction:
from state 112 at head -1 with one-set {-1,1,3}, the baseline reaches state
48 at head -4 with ones {-2,-1,1,3}; the mutant reaches that state and head
with ones {-3,-2,0,1,3}. The local result is therefore not a simulation of
the old full conditional instruction. Changing register names alone cannot
fix the additional control-region difference. Evidence is in
`mtf_local_audit.json`; no complete interpreter or ZFC equivalence is claimed.

## Primary source paths

- https://github.com/jeff87654/busy-beaver/blob/c132d7eae8158cd3a9850ea3eb7251158c3dd821/ZF/m254/coq/e2e/E2E254.v
- https://github.com/jeff87654/busy-beaver/blob/c132d7eae8158cd3a9850ea3eb7251158c3dd821/ZF/m254/coq/settheory/S_main.v
- https://github.com/jeff87654/busy-beaver/blob/c132d7eae8158cd3a9850ea3eb7251158c3dd821/ZF/m254/coq/settheory/S_sound.v
- https://github.com/jeff87654/busy-beaver/blob/c132d7eae8158cd3a9850ea3eb7251158c3dd821/ZF/stdzf_r3/zfc/Z_main.v
- https://github.com/jeff87654/busy-beaver/blob/c132d7eae8158cd3a9850ea3eb7251158c3dd821/ZF/m254/coq/tm/RM.v
- https://github.com/VladimirReshetnikov/ProveIt/blob/8e012a51d6e7fdad4d903089536427a813009a4f/Computability/BusyBeaver/Research/ZFC/choice_calibration254.md
- https://github.com/VladimirReshetnikov/ProveIt/blob/8e012a51d6e7fdad4d903089536427a813009a4f/Computability/BusyBeaver/Research/ZFC/candidate-prefix246/README.md
