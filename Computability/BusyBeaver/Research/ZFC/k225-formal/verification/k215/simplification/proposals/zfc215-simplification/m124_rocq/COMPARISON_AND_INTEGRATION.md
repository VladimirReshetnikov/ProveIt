# Candidate comparison and the M124 proof transfer

Inspected repository snapshot: `e0b8f9cb8c496ff2d6e43f478021fc14d42bbfad`.
The recommendation below concerns the cost of certifying an additional literal
machine **after importing the already verified primary K215**. It is not a claim
that the transitive proof dependency closure becomes smaller.

## Recommendation

Use the existing **M124** predecessor-marker presentation from
`docs/incoming/DR215_research_2026-10-21.zip`, member
`DR215_research_2026-10-21/markers/marker_family/m124/`.

The machine is an existing 215-state candidate, not a construction newly found in
this investigation. The new contribution here is a compiled, assumption-free
Rocq theorem transferring halting between its exact table and the exact primary
K215 table, for every initial binary tape from control state zero. It has only
four modified transition rows and needs two immediate-predecessor facts. The
proof avoids source semantics, natural-number register invariants, proof-stack
credit, primitive runtime certificates, and blank-bootstrap replay.

| Native row | Primary K215 | M124 |
|---|---|---|
| 110 / 0 | 0 R 127 | 0 R 124 |
| 124 / 0 | 0 R 62 | 0 L 127 |
| 127 / 0 | 0 R 14 | 0 R 8 |
| 127 / 1 | 1 R 138 | 1 R 59 |

The incoming edge to old 124 is uniquely `104/1: 1 R 124`; the incoming edge
to old 127 is uniquely `110/0: 0 R 127`. Consequently old 124 has left marker
one and old 127 has left marker zero. Both roles share read-one action `1 R 138`.
The state map sends old 127 to new 124 and fixes all other labels.

For a zero under the old head, the new three-step blocks are

* old 124: `124 -> 127 -> 59 -> 62`;
* old 127: `124 -> 127 -> 8 -> 14`.

Both preserve every tape cell and finish one cell to the right. Every other
old transition has a one-step image. A strict positive clock prevents the
invalid inference that a zero-length simulation alone preserves divergence.
The checked theorem gives a matching time `m` for every source time `n`, with
`n <= m <= 3*n` and exact head/tape equality at the boundary.

## What is checked here

The sources are independent of the large repository proof closure:

* `M124Table.v`: generated exact native K215 table, 215 working labels, 430 rows.
* `M124Facts.v`: exact four-row M124 definition; kernel-reduced finite incoming
  and outer-transition certificates, and proof that their quantified use covers
  all natural-number state labels.
* `M124Transfer.v`: whole infinite tape semantics, pointwise correctness of
  writes, inductive marker invariant, positive simulation, and halting equivalence.
* `check_inputs.py`: reproducible byte pins, exact generated source binding,
  four-row patch, state count, target closure, and dense/native relabeling.

The two main closed theorems are

```coq
all_tapes_equihalting h t :
  Halts K (C 0 h t) <-> Halts M (C 0 h t).

blank_nonhalting_iff :
  ~ Halts K (C 0 0 (fun _ => false)) <->
  ~ Halts M (C 0 0 (fun _ => false)).
```

All three printed assumption reports, including the generic
`calibration_transfer`, say `Closed under the global context`.
Coq 8.18.0 / OCaml 4.14.1 was used. `build.log` and `facts-build.log` preserve
the actual successful compiler outputs. `coqchk.log` is the recursive kernel
check log; its process exit status is recorded by the reproduction runner.

The tape type is `Z -> bool`. A write of the already-present symbol returns
the original function object; `put_standard` proves pointwise equality with
the ordinary update formula. This avoids needing functional extensionality.
Halting is entry into native label 254. The finite input check establishes
that every other transition target is a working label, so no missing working
row is silently treated as a legitimate halt.

## Precise integration boundary

This is a new kernel-checked **table-to-table theorem**. It does not yet import
the repository's actual ZFC endpoint into this standalone configuration model.
The proposition-polymorphic theorem `calibration_transfer` makes the remaining
dependency explicit. Passing `Con(ZFC)` as its proposition is justified only
after connecting the existing baseline endpoint to this `Halts K` predicate.

The minimal Rocq integration point is

`Computability/BusyBeaver/Research/ZFC/k225-formal/rocq/rocq-extension/coq/215/`

where `CorrectDense215.v` proves

```coq
Dense.halts dense_tm Dense.c0 <-> StandardZFC ⊢TC ⊥.
```

`Dense215.v` already supplies the dense-to-sparse transition identity and
halting equivalence. Its core uses BusyCoq configurations consisting of a
state and `(Stream bool * bool * Stream bool)`. Its legacy sparse normalization
maps native 301 to 102, native 302 to 120, and native halt 254 to 230. All other
present native working labels are retained. These details matter when binding
the imported theorem; native label 127 itself is unchanged by this normalization.

Two clean integration routes are available:

1. Prove once a generic stream-zipper-to-integer-tape simulation, using the
   relation that the zipper's nth left/right symbols equal the integer tape
   at the corresponding offsets. Combine this with the existing finite
   label map and import `all_tapes_equihalting`.
2. Port the short marker invariant and the two three-step calculations
   directly to BusyCoq's existing `step` / `multistep` relation. This avoids a
   second tape model and should be the smaller repository patch.

Neither route requires re-proving numerical-calculus consistency, the strong
proof compiler, command enumeration, general register arithmetic, or all 6,176
primitive runtime cases. The baseline endpoint's already compiled dependencies
are reused, not removed. A changed physical table cannot be certified merely
by renaming that existing endpoint.

## Comparison with the other inspected 215-state alternatives

These are engineering judgments about proof obligations, not lower bounds on
formal proof length. The first two rows are especially attractive for a small
additional endpoint.

| Candidate | Candidate-specific new proof obligations | Assessment |
|---|---|---|
| M124, M160 (DR215 marker appendix) | Four rows; two one-step predecessor facts; two 3-step blocks | Smallest obvious incremental transfer |
| CM215 / conditional-marker | Six rows; predecessor markers plus a special two-step history through 189/1 and 156/1 | Also small, but less simple than M124 |
| Context-return machine (Context Transfers archive) | Five edited rows; several distinct history-dependent local blocks | Reusable local-transfer framework, more cases |
| commands120 | Command-tag permutation, source correspondence, changed physical decoder/runtime | Clean inherited calculus, larger physical proof |
| composed allocation | Same source; different binary transition graph and bootstrap | No logical savings; reuses source proof |
| rebalanced R41 | Same ordinal graph; 4,120 changed instruction addresses and 19 rows | Smaller source depth does not prove smaller verification cost |
| NW215 | Four physical rows but 352 source register operands; exchange counter and stack; changed bootstrap | Simple source conjugacy, still needs a frame/runtime bridge |
| ZC215 | New zero-credit tag-lowering injection; zero spares; changed refill/bootstrap | Attractive fresh scheduler proof, not the shortest inherited endpoint |
| ST215 / direct-transfer | A shorter primitive transfer command, strong compiler adaptation, protected opaque tail | Potentially simpler future command layer; substantial current transfer cost |
| DR215 | ST215 plus rho6 parameter symmetry and repaired selector | Two changed rows do not eliminate compiler obligations |
| GC215 | Command-tag generalization, altered compiler, conditional physical merge | New semantic interface; no immediate proof-size advantage established |
| FT215 | One changed scheduler row, forced transfer before each candidate, debt-seven theorem | One row can entail a substantial infinite-schedule proof |
| SB215-AB | Adaptive skipped-candidate scanner, synchronizing-word completeness, source and sampler calibration | Most intricate scheduler obligation among these examples |

The cleanest candidate to prove *from scratch* is less clear: M124 inherits
the same substantial K215 logical/compiler proof. ZC215's injection argument
looks especially attractive for replacing a scheduler-credit proof, but it
does not remove the rest of the stack. The primary K215 remains the only
inspected repository candidate with its full existing Lean and Rocq ZFC endpoint.

## Relation to the 214-state target

M124 merges two old roles into one boundary role and reuses the other state as
a selector. The net saving is zero. The exact selector requires rows
`0 R 8` and `1 R 59`; no other current state has both literal rows. The supplied
input checker exhausts this direct reuse test. This narrow fact does not exclude
contextual reuse, longer matching blocks, different providers, joint mergers,
or any 214-state consistency machine.

The two clauses of `Inv` provide a compact, independently checkable contract
for a future selector-sharing search. Every proposed additional reduction should
export a local positive-length simulation under that contract, then invoke
the same whole-run theorem rather than regenerate the complete proof stack.

## Provenance

The old table is the primary `candidate-k215/k215.native.tm`, SHA-256
`9683d6ed9628e6ce407c315b08f5da3d063da94e92706f275ca0f33e8272e4b2`.
The M124 native table is SHA-256
`8e0ccb4b631c4e4c1c02c4b52a6fe382984e67557dd1dcd949065479e38d07b9`.
Its dense table is SHA-256
`fa15e120366da90e74aac43f3b808b27c0187960d373d4a95e425f8c73259e2b`.
The incoming archive supplies `upstream_marker_proof.md`, `verification.json`,
and `state_map.json` unchanged. Their ordinary proof and machine invention
remain attributed to that earlier packet. The new Rocq proof, input checker,
comparison, and integration guidance are contributions of this investigation.
