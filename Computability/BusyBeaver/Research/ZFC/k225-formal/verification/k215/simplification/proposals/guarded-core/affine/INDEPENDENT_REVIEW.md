# Independent review of the guarded arithmetic contraction

Reviewed 2026-10-21. Verdict: no mathematical flaw found in the stated 367-to-189 guarded arithmetic contraction. This is an ordinary mathematical review plus independent finite corroboration, not a Lean/Rocq build or a formally checked endpoint theorem. No received archive program was executed or imported.

## Scope and independent checks

I read `NEW_LOOP_PROOF.md`, `review_owned.py`, `OWN_AUDIT.json`, and the updated self-contained `GUARDED_CORE.json`. I wrote a separate small checker using only JSON parsing and elementary arithmetic; it did not import or execute the reviewed checker or any received archive script.

Starting independently from `structural/input_graph.json`, the check recognized the 1,059 elementary drains and rebuilt all 732 outgoing edges of the 367-node affine graph, including complete homogeneous 10-by-10 products, targets, and drain paths. These match `structural/affine_graph.json`. This review does not independently reestablish the source-Tree-to-input-graph compiler theorem.

For the new layer, the checker:

- Compared every effective positive-branch matrix, including decrement-before-affine, against the complete nine-register triangular or conditional-clear map. There are exactly 174 triangular and four clear occurrences.
- Checked every retained node, branch matrix, finite summary path, and target against the updated circuit. There are 189 retained nodes, 188 tests, one halt, and 376 outgoing edges.
- Checked 182 summary references, maximum path length seven, and coverage of all 178 removed nodes. The derived ranks agree with path lengths but are not required for soundness.
- Replayed the stated 26,166 occurrence cases independently, comparing all nine outputs with the original checkpoint graph, the affine graph, and the formulas. This reproduced exactly 3,138,765 original checkpoint-graph transitions and the claimed outer-affine counts.
- Checked all 178 embedded zero-exit definitions and both source SHA-256 bindings in the updated self-contained circuit. Its reviewed SHA-256 is `15a315b4e87f966bd8d7bde577fa18d06e4d750720bd3e9d4404d9547605bd86`.
- Checked the five local current-source files against their supplied Git blob pins, including `L2Lib222.lean` and `Code254.lean`. This checks byte identity, not kernel elaboration.

## Arithmetic and counter-zero boundary

For a triangular node, put `a = R1`, `n = R6`, and `z = R7`. Its stored nonzero matrix is applied after the register-6 decrement. Consequently one positive outer step is exactly

`R1' = 0`, `R6' = a + n - 1`, `R7' = z + a + n`,

with R0, R2, R3, R4, R5, and R8 unchanged. The effective constant in the R6 row is -1, but the branch premise n > 0 makes the natural subtraction valid. The R7 affine body has the compensating constant needed after decrement; dropping the decrement changes the formula.

If n > 0, let s = a + n. The first body adds s and leaves `(R1,R6) = (0,s-1)`. The remaining s-1 bodies add s-1 down to 1. Thus exactly s bodies execute, with final R1 = R6 = 0 and R7 = z + s(s+1)/2. The measure R1 + R6 decreases by one on every positive body. After the first body R1 is zero, which rules out early termination at a positive remaining measure.

If n = 0, no body executes, regardless of a. The pre-exit state is the entire original register vector. This cannot be replaced by the positive formula. The documented node-36 example with R1 = 2 and all other registers zero is valid: its true zero exit produces R6 = 2 and R7 = 0, whereas the invalid unconditional triangular formula produces R6 = R7 = 3.

For each clear node, every positive body decrements R6 and clears R5, preserving the other seven registers. There are exactly n such bodies. If n = 0, R5 must be preserved before the zero-edge map. In fact, all four actual zero-edge maps preserve the R5 contribution, so each admits a post-exit counterexample: input R5 = 5 with every other register zero retains R5 = 5, while unconditional clearing gives zero. Their exit targets are respectively 4578, 0, 0, and 4737 for nodes 4567, 4585, 4668, and 4733. The original weaker pre-exit-only regression has now been strengthened accordingly.

Every complete local summary also applies the literal zero-edge affine map once. The exact counts are one outer affine step for triangular n = 0, a + n + 1 for triangular n > 0, and n + 1 for clear loops. These are not primitive register-machine or Turing-machine transition counts. The 3,138,765 regression transitions are checkpoint-graph transitions, not a newly derived primitive runtime bound.

## Termination, entry, halt, and ranks

Each removed local loop is total on arbitrary nine-register natural inputs. Its zero exit has a fixed graph target, although its output registers depend on the input. A checked finite list of such summaries therefore suffices to compose a total normalization run; a separate ranking certificate adds no soundness information.

Entry 0 is retained. The unique halt is 4736, is retained, and has no outgoing edges. Every compressed edge starts with an original retained test step, so its expansion is nonempty. Intermediate removed vertices are tests rather than halts. Determinism plus cancellation of these finite positive prefixes yields halting equivalence and identical final registers. For the inverse direction, induction can use the length of a finite original halting run: each expanded compressed step consumes at least one transition and cannot hide an internal halt. This does not claim that the whole program terminates.

For arbitrary removed starts, no new entry-path data is needed in this concrete packet: all 178 removed nodes occur in the existing checked paths, and the suffix beginning at any occurrence is its valid normalization path. I also checked that the first-level recorded paths cover all 1,059 removed drains, so the same suffix argument applies there. In a different packet with uncovered nodes, one would need additional checked paths or a suitable accepted fuel-bounded normalizer. Coverage is essential to the all-start statement, but not to the retained-start statement.

The resulting graph must be called a guarded arithmetic macro core, not an affine core. Its local triangular maps are piecewise quadratic, and composed circuit expressions need not remain quadratic or affine. Keeping the expressions factored is appropriate.

## Existing-library reuse

The supplied `L2Lib222.lean` really states `pair162` on arbitrary nine-field records and proves it by induction on the sum of its two input fields. It begins with `loop215`, transferring old R1 into both R6 and R7 before the register-6 test. Its full result adds `P(R6,R1)`, including the old-R1 contribution to R7. This is not the same entry boundary as the new checkpoint map, especially when checkpoint R6 = 0 and R1 > 0. Reuse requires a boundary/path adapter, not merely a renamed application.

`enc` maps indices at least 9 to zero, so an application to arbitrary unbounded register files additionally needs a frame argument for untouched higher registers. This is distinct from the already-valid arbitrary-nine-register claim.

The available `RMDag.while_loop` statement explicitly requires the body to preserve its tested counter. The triangular body adds old R1 to that counter on its first pass, so unrestricted direct instantiation fails that premise. A direct induction on R1 + R6 is small and avoids this mismatch; alternatively, initialization and an appropriate invariant-aware adapter would be needed. Reusing `Cantor.tri`/`P_step` is reasonable. The IOpen-model arithmetic interface is unnecessary for this ordinary natural-number loop.

## Remaining formal boundary

The finite checks validate concrete data and binding hypotheses. They do not replace the generic loop-induction proofs, source-graph semantics, or positive-macro halting transport inside a proof assistant. Subject to those explicit boundaries, the current document accurately describes the contraction and avoids the state-count, runtime, and endpoint overclaims considered in this review.
