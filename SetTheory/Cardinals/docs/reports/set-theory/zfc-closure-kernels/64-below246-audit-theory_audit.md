# Independent theory and inheritance audit

Audit base: ProveIt commit `8cdc55ff9281b0aaba49bf74b0b225d57f12b893`.
Audited incoming package: `context246/zfc-context246`.

## Findings

The ordinary mathematical proof route used by the incoming context246 report is sound in outline and appropriately distinguishes its proof status. I found no new logical gap in that route. It does **not** claim a newly compiled Lean/Rocq endpoint for the 246-state table. Its claim of ZFC-provable equivalence is justified by reconstructing the specific finite-computation and set-coded-model arguments inside ZFC, not by invoking a blanket interpretation of Lean universes in ZFC.

All 32 Lean source snapshots supplied in the context246 package are byte-identical to their current counterparts in the pinned ProveIt checkout. No source drift in this supplied dependency selection needs repair. This comparison is not a fresh kernel build of the complete inherited dependency closure.

I freshly executed, without modifying the supplied package, its four block induction checks, finite-word identity, three complete register-macro induction checks, and nine marking checks. I then freshly parsed the complete 6,459-node `Prog254.v` tree and reran all 8,391 instruction cases, together with 342 guard/oracle checks. All passed. The whole execution took 5.42 seconds. Each site has at least 13 literal steps; there are three overflow cases; the largest accepted symbolic trace uses 497 rules. These are replayed ordinary symbolic-induction certificates, not proof-assistant kernel certificates.

## Exact logical chain

For a new candidate that preserves the original register program:

1. Prove its exact blank bootstrap reaches a complete related runtime frame with a safe logical root.
2. Prove its guarded binary instruction contracts universally, including complete tape support, arbitrary nonnegative register values, arbitrary permitted gap, and arbitrary finite nonempty spare suffix.
3. Compose these contracts with positive progress to obtain binary halting iff halting of the literal register program.
4. Use `Bisim254.prog254_halts_iff` to transport to the structured 219-node program.
5. Use the appropriate `DirtyProgram254` theorem to obtain halting iff `Code254.C254 Code254.F`.
6. Use `NativeTheory254.c254_refutation_iff`, `WFTheory.native_refutation_iff_zf`, and `ChoiceCalibration254.zf_refutation_iff_zfc` for the exact syntactic calibration.
7. Negate both sides.

The safe condition is exactly

`C254(T) and C254(H) and Good(W)`.

The six remaining fields `(N,A,D,X,Y,L)` may be arbitrary. The currently supplied context246 root specializes `DirtyProgram254.six_nonformula_path_iff` to `(3,0,3,0,0,0)`. Its physical-register vector `(0,0,0,3,0,0,3,0,0)` must first be read through the fixed logical-to-physical map `(6,2,0,4,3,7,8,5,1)`; logical register positions and physical block indices must not be conflated. Starting at `N=3` retains completeness because `EnumSafeStart254.complete_from` handles arbitrary starting counters via unbounded padded encodings.

## Why the model argument fits inside ZFC

The native theory consists of the literal CP axiom, the GIC scheme over syntactic first-order formulas, and raw irreflexivity. It does not assert Collection for every external binary relation.

The syntax and derivations form sets of finite codes. ZFC proves soundness and the countable-language Henkin completeness theorem, so consistency supplies an inhabited set-coded model. No transitivity or external well-foundedness hypothesis is introduced.

From a ZF model, the internal rank-container construction and internal Collection prove the native axioms; Foundation proves raw irreflexivity. Conversely, the native model has the specified set-sized bisimulation quotient, with the required extensional axioms and Power Set. Its Foundation subdomain is defined by the model's **internal** well-foundedness predicate. In `WellFoundedPart.lean`, that predicate quantifies over subsets represented in the model. It is not the external mathematical assertion that the membership relation is well founded. The exact GIC instance supplies the required closure, and the formula relativization lemmas establish Separation and Replacement on the interpreted subdomain.

The Choice comparison forms the internal constructible subdomain of a set model of ZF. Although that model regards its L as a class, its external domain is a set, so the interpreted carrier is a subset of that set in the ambient ZFC argument. The source provides both an explicit inhabitant and the ZFC model theorem. All satisfaction predicates are for set-coded structures and finite syntax; there is no truth predicate for the ambient universe.

This yields the claimed ordinary ZFC proof of the refutation comparison. It does not automatically yield a PA proof or an effective proof-code translator whose total correctness is proved in PA. The existing repository explicitly leaves that stronger internal arithmetic formalization open.

## Universal tape proof checks

The induction checker is small enough to audit directly. Its important safeguards are:

- A non-loop literal rule requires a positive constant term in the run length, so it cannot read an unknown possibly empty unary run.
- A state-preserving scan has a unary induction proof, including length zero.
- Opaque arbitrary contexts cannot be read by a literal transition.
- List traversal is allowed only after a checked one-block theorem with the same state and orientation and arbitrary preserved contexts.
- The word equation `C(A)1 = 1B(A)` is proved by structural induction before it is used as a rewrite.
- The zero-decrement contract exposes a following block `01^(y+1)`, retaining the indispensable nonempty-suffix premise.
- Increment appends a value-one spare; the other operations retain the suffix. Arbitrary spare values are permitted.
- The affine oracle checks that the decrement guard names the very physical register currently marked.
- A second register operation cannot silently erase an earlier register effect.
- The complete target tape retains trailing zero path cells and overflow effects, with the head-to-header distance interpreted consistently.

The global halting converse needs positivity. If a nonterminal logical instruction has a positive binary segment of length `k` to another active related frame, a binary halt at time `t` implies `k < t` by halt absorption. Strong induction on `t` then yields a logical halting run. Thus neither an infinite sequence of choices nor an unstated fairness assumption is needed.

## Conditions for reviewing an additional state deletion

For any additional edited state/read pair, one of the following must be supplied:

1. A universal recurrent invariant showing the old pair cannot be read, together with a compatible state map on all remaining pairs; or
2. A whole-frame macro identity implementing the same logical action with explicit positive progress, including arbitrary operands and exterior contexts.

Finite execution samples, graph reachability, and the failure of exact bisimulation do not establish such an invariant. The blank initializer can legitimately violate the runtime language, so it needs its own complete finite bootstrap after any edit. The initial state counts among the working states. Halting retains the final write and movement in the chosen semantics.

## Claims to keep separate

- `ZFC proves (not Halt(M) iff Con(ZFC))` is the intended mathematical equivalence.
- A closed Lean/Rocq theorem is a different, machine-checked status.
- A serialized first-order ZFC proof object is a third deliverable, not supplied by the existing 246-state package.
- Under the metatheoretic assumption that ZFC is consistent, the equivalence implies actual nonhalting, and the second incompleteness theorem rules out a ZFC proof of that nonhalting.
- Mere consistency does not rule out a ZFC proof of the false existential halting claim; two-sided independence needs an additional hypothesis such as Sigma-1 soundness.

## Primary source pointers

- [ProveIt 252-state status](https://github.com/VladimirReshetnikov/ProveIt/blob/8cdc55ff9281b0aaba49bf74b0b225d57f12b893/Computability/BusyBeaver/Research/ZFC/candidate-permutation252/README.md)
- [Exact binary/ZF endpoint](https://github.com/VladimirReshetnikov/ProveIt/blob/8cdc55ff9281b0aaba49bf74b0b225d57f12b893/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/BinaryPerm252.lean)
- [Choice calibration](https://github.com/VladimirReshetnikov/ProveIt/blob/8cdc55ff9281b0aaba49bf74b0b225d57f12b893/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ChoiceCalibration254.lean)
- [Native theory](https://github.com/VladimirReshetnikov/ProveIt/blob/8cdc55ff9281b0aaba49bf74b0b225d57f12b893/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/NativeTheory254.lean)
- [Native/ZF comparison](https://github.com/VladimirReshetnikov/ProveIt/blob/8cdc55ff9281b0aaba49bf74b0b225d57f12b893/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/WFTheory.lean)
- [Internal well-foundedness](https://github.com/VladimirReshetnikov/ProveIt/blob/8cdc55ff9281b0aaba49bf74b0b225d57f12b893/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/WellFoundedPart.lean)
- [Safe dirty roots](https://github.com/VladimirReshetnikov/ProveIt/blob/8cdc55ff9281b0aaba49bf74b0b225d57f12b893/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/DirtyProgram254.lean)
- [Upstream 254-state verification README](https://github.com/jeff87654/busy-beaver/blob/zf-254/ZF/m254/README.md)
- [Upstream closed Rocq endpoints](https://github.com/jeff87654/busy-beaver/blob/zf-254/ZF/m254/coq/e2e/E2E254.v)

## Additional partial-result and detector review

The 245-state table with `75/0=0L112` and state 255 deleted has freshly
proved universal positive and zero decrement contracts, including arbitrary
left and right exterior tape. Its zero duration is `2*width(prefix)+5`;
positive remains `2*width(prefix)+4`. The complete 16-transition increment
counterexample is generated beside the proof in `experiments/tail` of the
delivery. This is a partial local result, not a smaller consistency machine.

The separate 244-state forward-carry checker was independently replayed and
its three block/list-based macro derivations reviewed. The exact collision
is sound: zero input with suffix S and positive input 1 with suffix S+[1]
produce identical complete state 48/head 0 configurations. It persists with
all spare values equal to 1, because the permitted spare counts differ.

There is a subtle limit to the deterministic-continuation corollary. Equal
configurations have equal future runs, so a **single designated return
event** (for example, the first subsequent dispatcher entry, or a common
deterministic stopping rule) cannot yield different decoded successor PCs.
However, equality of future runs alone does not exclude one future run
visiting two target frames at different times. The inherited affine checker
does not generally reject an earlier non-target dispatcher entry. Therefore
the collision alone does not disprove every possible existential-segment
simulation. Any stronger corollary needs that extra return convention or a
separate argument excluding multiple candidate target frames.

For detector replacement, every external entry to the old eight-state region
is 4/0. Every row entering state 4 writes 1 and moves left; thus4/0 establishes
the exact right guard `tape(+1)=0,tape(+2)=1` at the following state 6 entry.
The exact old last zero row is `74/0=0L84`, so replacing its long run by an
exit to 84 at -6 needs an additional zero at -8 before transport through the 84
scan. Without that zero, a 1 at -8 gives a concrete mismatch.

The additional assertion-only affine replay in `audit_detector_entry.py`
checks all 8,391 arbitrary-parameter instruction cases. Among 191,434 symbolic
state 6 entries, every entry has the right guard and either a first leftward1
at distance 0..7 or known zeros at every position-8..0. There are21,316 long
entries and 36 distance-seven entries. Macro-internal detector use is only
the unchanged induction-support row 6/1, a distance-zero case. This proves
the recurrent detector input partition through the inherited universal
frame argument; it is stronger than the separate finite-value census.
Blank startup remains a separate finite verification obligation.

