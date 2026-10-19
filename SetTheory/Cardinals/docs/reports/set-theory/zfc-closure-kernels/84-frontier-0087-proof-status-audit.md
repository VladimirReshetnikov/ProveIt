# Source-level logical calibration audit

Snapshot: ProveIt `79957d7b290ec807d434959a0c6ecc06ee90b419`.
This is an audit of checked-in source and accompanying proof documents. This
session did not have a Lean executable and did not rerun kernel compilation.

## Existing exact machines

The prior 254-state machine has a published closed Coq endpoint
`zf254_halts_iff_ZFC`. The ProveIt 252-state permutation machine has the closed
Lean endpoint `ChoiceCalibration254.nonhalting_iff_zfc_consistency`, composed
from the literal binary bootstrap/runtime theorem and the ZF/ZFC calibration.
These are external metatheorems; their existence does not by itself constitute
a serialized ZFC proof of their arithmetization. An ordinary argument inside
ZFC can nevertheless supply the user's requested strength without the stronger
PA internalization now being developed in the repository.

Primary source paths:

- Upstream `ZF/m254/README.md` and `ZF/m254/coq/`
  at <https://github.com/jeff87654/busy-beaver/tree/zf-254/ZF/m254>.
- ProveIt `Computability/BusyBeaver/Research/ZFC/candidate-permutation252/README.md`.
- `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ChoiceCalibration254.lean`.

## The 246-state baseline

`candidate-prefix246/README.md` describes a complete ordinary mathematical
ZFC proof and an incomplete exact-machine closed Lean endpoint. The later
checked-in source substantially advances the individual pieces:

| Layer | Source endpoint / current remaining premise |
|---|---|
| Exact boot | `BootPrefix246Chunk008.bootstrap410735`, `bootstrap_tape`, `bootstrap_active_through` |
| Complete initial frame | `BootstrapFrame246.bootstrap_frame` |
| Register seed calibration | `LogicalSeed246.halts_iff_zfc_refutation` |
| Whole-frame binary runtime | `RuntimeInstancePrefix246.register_halts_iff_binary` requires `Covered`; the alternate endpoint requires `allSites` |
| Remaining closed composition | Actual-tree coverage and final composition to the exact binary machine |

The exact ordinary baseline table is
`Research/ZFC/candidate-prefix246/zfc_prefix246.tm`, SHA-256
`89cda615b3ea9fcac07ad6b08e0351faa34841a56935b6f5846d3920f13bc0fc`.
It has 246 working states, start 0, dispatch 88, halt 246, and 492 rows.
The original-label table has start 95, dispatch 96, halt 254, and SHA-256
`303911c554284c49ce09042d8127feba4da260baae766e32260034aa3bdb82ee`.

At its exact 410,735-step bootstrap endpoint, the head is at -5, marker at -6,
header at 176, and head-to-header distance 181. The complete frame gives
logical `(N,T,W,A,D,H,X,Y,L)=(3,0,0,0,3,0,0,0,0)`; the physical primary vector is
`[0,0,0,3,0,0,3,0,0]`, followed by 167 spare values 1. There are 351 one cells.
The ordinary runtime proof must retain the whole tape frame, not just its
register values or a finite observed prefix.

## Internal ZFC proof obligations, with no universe soundness shortcut

The desired internal proof chain has the form

```
Halt(exact blank binary machine)
  iff Halts(exact register program at the proved seed)
  iff C254(F)
  iff Ref(NativeAx)
  iff Ref(ZF)
  iff Ref(ZFC).
```

Every object can be coded as a set in ZFC. First-order completeness applies to
nonempty set-coded structures, including possibly nonstandard and externally
ill-founded ones. The native-to-ZF interpretation uses a set-sized quotient
and an internally well-founded definable subdomain; it must not replace
internal definable well-foundedness by external well-foundedness. The reverse
interpretation uses the usual internal rank and Collection arguments. The
ZF/ZFC transfer uses the definable constructible class *inside a set model*,
which is an external subset of that set model's domain. Satisfaction is always
for a set structure and formulas coded in omega. No truth predicate for the
ambient universe or reflection principle for ZFC is required.

A binary reduction transfers the old theorem only after a complete, positive
whole-frame segment simulation has been established. A clean program counter,
the full register region, a nonempty finite spare suffix, the zero exterior,
and a sufficient head-to-header distance belong to the invariant. Positive
segment lengths give reverse halting by strong induction on a finite binary
halting time. Such a proof does not need a fairness or infinite-choice premise.

## Additional findings from this audit

1. The broader target `H % 4 == 1` is logically sound. The full proof and exact
   source macro are in `atomic-target-note.tex`. Its raw Wade implementation
   costs four extra states, as recorded by the portable experiment.
2. The weaker test “H is odd” is unsound: tag 3 encodes equality, and code 3
   is the theorem `v0 = v0`.
3. A seven-total-state read-only detector cannot distinguish gap 7 from the
   long case even with unbounded time. The full ordinary proof is in
   `read-only-detector-note.tex`; temporary tape writes and uncounted shared
   caller states are outside its scope.
4. Static review of `detector_sat/search_sym.py` and `search_shared.py` found
   no mismatch between the CNF and the literal replay semantics. The active
   state/head constraints, one-hot state/head variables, read/write equations,
   restoration constraints, and absorbing exits implement the stated finite
   contracts. The BFS target-order symmetry is complete up to renaming under
   the unrestricted `first='free'` search. In the shared template, fixed old4
   and old2 introduce no target to a fresh state except entry 0, preserving
   that argument. The bounded 12-step UNSAT remains a solver report without
   a DRAT/LRAT certificate; it is distinct from the unbounded read-only proof.

The five latest incoming research archives reviewed in this task contain no
validated machine below 246 states. This audit likewise establishes no such
machine. It supplies precise semantic and local obstruction results that can
guide subsequent searches.
