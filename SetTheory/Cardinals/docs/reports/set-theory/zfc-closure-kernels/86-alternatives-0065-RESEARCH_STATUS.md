# Research toward a binary blank-tape consistency machine below 246 states

Baseline: ProveIt `7ba1598461c6e485c5aeb8f673c0b1d571f8012b`.
Target: fewer than 246 working states, a separate halt state, one two-way infinite binary tape initially zero; ZFC proves that nonhalting is equivalent to Con(ZFC).

No complete sub-246 construction has been established in this research so far. Internal PA certification is not a requirement of this task. A stronger theory is not an acceptable substitute for the specified consistency equivalence.

## Independently checked same-count composition

`joint_controls/joint246_old.tm` combines the alternative detector from source 64 and source 67's rotated source-202 decoder. The 14 edited rows are disjoint. The table still has 246 working states.

SHA-256: `29377d9d8abc876187cb3fdac430f9dc92999802a848c0c2403874763214951f`.

The independent audit checks the source program's entire guarded transition graph against the literal original program, all 16 inherited induction contracts, 352 oracle tests, all 8,391 arbitrary-size symbolic instruction cases, and an independent whole-tape sparse bootstrap. It reaches the same calibrated seed in 409,449 transitions; a separate dense simulator agrees. See `verification/joint246_independent_audit.json` and `joint_controls/joint246_check.json`.

The selected uniform and mixed one-state folding families have completed: 54,390 uniform recipes with 126,577 affected-case checks, and 49,695 mixed recipes with 651,209 checks, with no survivor. The 42 induction-support rows were fixed and the symbolic budget was 1,000 rules per check. These results are not semantic impossibility proofs or general state lower bounds.

## Source-depth control

A closed-component reassociation has 205 active source nodes, maximum zero-prefix length 6, and maximum path length 42. Complete ordered normal form, guarded graph, and root-entry comparisons pass. This saves one potential detector phase at a cost of four source nodes relative to the 201-node source. It is not a binary-machine improvement. See `joint_controls/depth205_audit.json`.

## Active independent approaches

- Smaller quantified logical bases and axiom generation, retaining exact consistency strength.
- Compiler-aware sharing of arithmetic and decoder traversals.
- A slower detector using reversible temporary tape storage and existing helper states.
- Branch-preserving redesign of the arithmetic core.
- Direct template-query verification instead of unrolled register-level template matching.

All runtime candidates must satisfy the proof obligations in `verification/acceptance_checklist_and_transfer.md`. Finite regression tests alone do not establish unbounded simulation, and a locally smaller core is not a complete machine until its entry/exit conventions and blank initialization are proved.
