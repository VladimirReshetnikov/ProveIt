# Batch 170: source rotation enables the 240-state fold

The report delivered in `e5c2b3337e8f38a54a1dbd2ad7e8feb7d5996d6a` becomes Source 80 of this host. It is pinned to the 241-state companion introduced in `8c41b1fb7d7bb8cd0612e37848181fe4a2f5d569`. The reconciliation-note workflow preserves the base article, its labels and PDF, and every delivered file. The host reaches 80 sources; the collection remains 290 reports. No merged article PDF is built.

Placement `0841b55a14` preserves the original bytes and retires the committed incoming ZIP. The separate fresh ten-job replay is terminal PASS; its exact result, raw outputs and scoped reviews are retained below.

The [placement map](data/intake170-placement.json) accounts for 79 original outer members: 61 new exact ancillary files, seven aliases to existing files, five aliases within this source, and six archive-only manuscript/PDF/delivery-README members. The 73 ancillary occurrences resolve to 67 targets, including six existing targets introduced in placements `5513e77ff1`, `696c150e84` and `c3339d150f`. The embedded 241 companion ZIP is one exact data member, byte-identical to the archive in its cited arrival commit. Only the new 240 ZIP was retired; twenty older archives remain outside this batch. [Fresh recovery](data/intake170-recovery.json) restores all 79 originals and matches all 73 ancillary occurrences through 67 targets. [Reproduction](intake-170-reproduction.md) preserves the original layouts before any execution.

## The new machine and the earlier ingredients

The exact canonical table has 240 working states, start 0, dispatcher 84 and a separate halt state 240. It has 480 rows, two symbols, a two-way infinite tape and a left or right move on every transition. Blank initialization is included. The inherited-label version starts at 95, dispatches at 96 and halts at 254.

| Change from the pinned 241 table | Result |
| --- | --- |
| `142/0`: `0 R 37` → `0 R 72`; `142/1`: `1 R 72` → `1 R 17` | Rotate all four occurrences of the transfer-plus-one macro. The intermediate table still has 241 states. |
| `72/0` → `0 L 144`; `72/1` → `1 L 36`; `79/1` → `1 R 72` | Use the strengthened tape context to merge the role of old state 90 into 72. |
| Delete the two rows of old state 90 | The final table has 240 states; all 475 other retained rows are unchanged. |

The rotation and predecessor-bit technique are earlier ideas, not newly claimed general methods. In particular, the complete new 6,455-leaf source list is byte-identical to Source 74's `rotate_h` list, preserved at [the earlier source file](data/74-ret242-res-srcrot-rotate_h-sites_logical.json). Source 80 contributes the precise composition that makes another binary-state fold possible, its concrete table, and the accompanying source/local/runtime arguments. A smaller source list alone would not establish the smaller machine.

The canonical table's identity is `508b55a6dfdf96a42f09c49e410e078ae7478a1d0257d78d25503b4da24541cd`; the inherited table is `547dd69da66f66dd48238a53d34b52a3ce85bb6c7d01534dd1cfb815507f248f`. These identify this candidate independently of its state count.

## Two separate equivalence arguments

At each of four source prefixes, the old fragment transfers logical register 6 into logical register 5 and then increments register 5. The new fragment increments first, tests/decrements register 6, and repeats. For every natural pair `(R5,R6)=(a,b)`, both finish at `(a+b+1,0)`, preserve all other registers and take exactly `3b+2` source instructions. Their termination proof is induction on `b`. The source-graph proof checks all 8,370 outside guarded edges, unchanged outside instructions, paired entry points, no entry into fragment interiors, common exits and unchanged root/halt. This yields root halting equivalence for every natural register file. It does not assert equal intermediate binary tapes for the original and rotated machines.

For the subsequent binary fold, the rotated table has a four-state invariant: states 55 and 142 have a left-hand one; state 72 has `10` in its two preceding cells; state 90 has a left-hand one. The complete incoming-edge list proves this invariant from inherited state 95 for every complete binary tape and integer head position. The state map sends 90 to 72 and fixes all other labels. Four exceptional old steps are implemented by positive new blocks of lengths 9, 3, 3 and 3; every other old step takes one new step. All intermediate reads/writes stay in the proved finite footprint, so the endpoint equality includes the arbitrary tape exterior.

The exact clock is `N(n)=n+8 V72,0(n)+2(V72,1(n)+V90,0(n)+V90,1(n))`, hence `n≤N(n)≤9n`. Positive progress transports halting in both directions. This all-tape theorem compares the rotated 241 intermediate machine with the final 240 machine. The preceding source transformation and its binary realization have their own premises and certificates.

The delivered independent local checks enumerate 7,640 invariant implications and 7,640 whole-tape blocks. The rotated startup is 408,941 transitions; exceptional visit counts `(74,37,18,24)` give a further 750 transitions and the final 409,691-step startup. Separate sparse and dense implementations compare the complete tape: head −5, marker −6, header 176, logical registers `(3,0,0,0,3,0,0,0,0)`, 167 value-one spare blocks and exactly 351 one-cells, zero elsewhere.

## Runtime evidence and formal boundary

The delivered final runtime certifies all 8,386 instruction guards, 2,322,575 symbolic rules and all 480 rows, with minimum certified instruction duration 13. Its induction rules cover arbitrary natural register values and gap, arbitrary first spare value, and an arbitrary finite remaining spare list. The 4,000-step certificate-construction cap is not a bound on those mathematical values. The inherited runtime engine changes only the exact source-list count, source identity and receipt field name; its transition, affine and list rules remain unchanged.

**Fresh replay:** all ten jobs in the [terminal root record](data/intake170-fresh-replay.json) pass on an unchanged disposable copy, with persistent raw logs and a 1,200-second process-group bound per job. The rotated 241 runtime covers 8,386 cases, 2,318,435 rules and all 482 rows; the final 240 runtime covers 8,386 cases, 2,322,575 rules and all 480 rows. Their checker-reported durations are 267.567 and 263.633 seconds respectively; the record separately retains process wall times. Every final per-case record matches delivery, and all input bytes remain unchanged. The [machine review](intake-170-review-machine.md), [theory/driver review](intake-170-review-theory.md) and [lossless replay history](data/intake170-replay-history.json.gz) distinguish ordinary proofs, fresh execution and reusable-tool limits. No aggregate wrapper, manifest audit, nested predecessor suite, search campaign, Lean/Rocq compiler or TeX build is part of that replay. Earlier predecessor runtime evidence retains its historical status.

The report's ordinary consistency calibration composes its new arguments with the pinned 241/242/243 source-theory chain and its proof predicate. It claims an equivalence provable in ZFC, not a newly checked exact-table Lean/Rocq endpoint or an internal PA equivalence. The current best ordinary candidate is 240 states; the smallest closed external Lean consistency baseline remains the different [compensated 244 machine](../../../../../../Computability/BusyBeaver/Research/ZFC/compensated244_binary.md). No absolute consistency, unconditional nonhalting, global minimality or two-sided independence from mere consistency is inferred.

## Current-tree gap check

The pinned report does not start from an empty formalization. At the intake checkpoint, `Computability/BusyBeaver/Research/ZFC/candidate-fold241/README.md`, lines 16–18, says: “The complete 241-state Lean consistency theorem and the internal PA equivalence remain open.” Source 80 supplies an ordinary 240-state construction and fresh Python evidence; it does not fill those Lean or internal-PA gaps.

The different formal baseline is already closed. `Computability/BusyBeaver/Research/ZFC/compensated244_binary.md`, lines 4–8, says that blank-tape halting “is equivalent to a ZF refutation and to a ZFC refutation” and calls these “closed external Lean theorems”; it then says, “The proof inside PA remains open.” These statements are retained rather than reverting to the report's older formal frontier.

There is also an existing reusable source result. `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/SourceRotation244.lean`, lines 718–720, states:

```lean
theorem program_halts_iff (R : RegisterPath.Registers) :
    RegisterPath.Halts ProgramRotation244.program ⟨[], R⟩ ↔
      RegisterPath.Halts ProgramRouting245.program ⟨[], R⟩
```

This covers every natural register file for the earlier source rotation. Its generic loop/context machinery can support the next source transformation, but the theorem does not identify the new binary table or prove its runtime and blank startup. Subsequent source-only or separately checked Lean additions retain their own evidence; they are not a complete 240-state endpoint.

## A theory obstruction and a calibrated alternative

The separate theory contribution interprets membership as strict order on the nonnegative rationals, with native equality. Rational cuts satisfy CP, every weak Collection instance, Extensionality, Empty Set, Union, ordinary Foundation, irreflexivity and transitive membership. A piecewise rational affine automorphism fixes the finite parameters and input while moving an existing witness below a uniform bound. Structural invariance of satisfaction proves the entire Collection schema; it is not inferred from finitely many regression formulas.

Full GIC fails for the matrix requiring an empty output: coverage forces a positive cut, while support would require all its members to be zero, contradicted by a positive midpoint. Pairing, exact Power Set, ordinary Infinity and the corresponding Separation instance also fail. Ordinary Foundation here is an internal first-order axiom; it does not make the external rational order well-founded. Since ZFC constructs this model, assuming Con(ZFC), the weakened theory cannot have the desired ZFC-provable consistency equivalence with ZFC.

For nonempty native-equality membership structures, the full GIC schema is equivalent to full weak Collection plus full Separation, without CP or Extensionality. GIC gives Separation by a matrix selecting the desired members; conversely Separation removes unsupported elements from a weak-Collection witness set. Sharing those two emitters is a concrete future compiler experiment, but its extra dispatcher, syntax/freshness machinery and complete binary cost remain unmeasured.

The exact infinite-model evaluator uses finitely many automorphism orbits at each quantifier. The bundled checks include the stated axiom values, thirteen Collection regressions and 516 rational automorphism regressions. Two reusable-tool input limitations remain: `separation()` does not reject conflicts with its generated variables 2 and 3, and the optional JSON parser does not strictly validate constructor arity/names. For example, parameter 3 in `eq(0,3)` can be captured by the helper's existential variable; `['true','ignored']` is accepted. The bundled formulas are fresh and well-formed, so these caveats do not invalidate their results or the ordinary model proof. Delivered files are preserved unchanged; external callers must enforce freshness and syntax validation. The delivered `theory/dense_order_filter.py`, line 7, points to `dense_order.tex`; the actual supplied orbit/Collection proof is `report/sections/theory.tex`. This is a navigation correction in the reconciliation, not an edit to delivery.

## Bounded searches and remaining work

The archive preserves the successful coupled synthesis on the rotated table and four restricted negative controls: an earlier direct-offset search, generalized head-offset synthesis (52,560 pairs and 69,580,800 actions), predecessor-cell complement synthesis (52,560 pairs and 50,457,600 actions), and variable-block/stuttering overlays (115,680 proposals, radius four and at most 32 steps). These are exclusions within their stated sufficient certificate families, not semantic lower bounds. They were not rerun by intake merely to reproduce larger counts.

Further directions remain source rotations scored by the entry patterns they enable; simultaneous folds with proved finite tape transformations and positive progress; a kernel-checked exact 240 endpoint; total-cost comparison of the calibrated LC/Separation presentation; and model filters for proposed weaker axiom packets. Rejecting the rational-cut model alone would not prove ZFC strength. The new work retains Mira-Cult's calculus/program attribution, Jeff Ketchersid's upstream formalization, Andrew James Wade's compiler framework, and ProveIt's earlier reductions. No author identity is inferred from tooling or filenames.
