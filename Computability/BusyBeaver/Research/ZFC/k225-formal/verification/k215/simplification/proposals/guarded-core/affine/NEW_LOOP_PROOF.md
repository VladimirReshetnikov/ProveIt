# Two total loop summaries beyond the affine core

Status: ordinary mathematical argument with owned finite corroboration; no Lean/Rocq compilation. This is a proof-graph simplification, not a new Turing machine, fewer working states, a runtime speedup, or an endpoint theorem.

## Literal input and positive-step convention

The incoming archive is pinned at commit `aa66d0a33f1f8237a348899eb8095b045a502832`, Git blob `17321c28fc63f3dcdc895fa468eb3cad85d6cabe`, SHA-256 `4b9bf197546985b2c298b15d33bcf256e892a76a749ed1b367fe96aa4c536d46`. Its 367-node affine graph uses nine natural-valued registers R0,...,R8. At a `decnz r` node, the nonzero branch first subtracts one from Rr and then applies the stored affine matrix; the zero branch applies its matrix without a decrement. For the source's unbounded register function, registers at indices at least 9 are an unchanged frame: all checked tests and increments use indices 0 through 8. Their values need not be zero.

Independent reconstruction checks both canonical source graphs from their pinned Lean Tree literals, all 1,059 first-level drain bindings and products, and identity with the phase-five tree literals. The new result does not infer semantics from a graph size or a hash alone. The generic source-to-graph and macro-soundness theorems remain uncompiled.

## A. The 174 triangular loops

Exactly 174 retained affine nodes have register-6 tests, nonzero successor equal to themselves, and the following full register transformation on a positive input:

- R0, R2, R3, R4, R5, R8 are unchanged.
- R1' = 0.
- R6' = R1 + R6 - 1.
- R7' = R7 + R1 + R6.

The subtraction is only performed when old R6 > 0. These formulas include the original node's decrement before its affine body; applying the matrix to the un-decremented vector would be wrong.

Write a = R1, n = R6, z = R7 and T(k) = k(k+1)/2. Stop just before the zero branch.

1. If n = 0, no self-loop body executes. Every register, including R1, R5 and R7, is unchanged at this point.
2. If n > 0, exactly a+n self-loop bodies execute. Their result S is R except S1=S6=0 and S7=z+T(a+n).

Proof: set s=a+n. The first positive body sets R1=0, R6=s-1 and R7=z+s. Every later positive body leaves R1=0, lowers R6 by one, and adds its previous positive value to R7. Induction using T(k+1)=T(k)+(k+1) proves termination and the displayed sum. Equivalently, induct directly on s with the positive-counter premise. While R1 may reset in the first step, R1+R6 decreases by exactly one at every positive body. After the first body R1=0, so the loop cannot stop early with nonzero remaining sum. No global program invariant or clean-scratch precondition is needed.

Let the literal zero-edge affine matrix be Z_v and its target be w_v. The entire node summary is `(w_v, Z_v(S))`. It consumes one additional affine graph step for the zero branch. Hence the complete macro takes 1 outer affine step when n=0, and a+n+1 when n>0. These are NOT primitive register-machine transition counts or Turing-machine transition counts; each affine edge already summarizes a variable-length primitive run.

The zero case is genuinely different. At node 36, initial R1=2 and all other registers 0, the correct exit to 62 has R6=2 and R7=0. Applying the positive-case triangular formula even though R6=0 would incorrectly exit with R6=R7=3.

## B. The four conditional-clear loops

Nodes 4567, 4585, 4668 and 4733 test R6 and have a nonzero self-loop whose full action is:

- R6' = R6 - 1, under R6 > 0.
- R5' = 0.
- All other registers are unchanged.

If initial R6=0, no body executes: preserve R5 and all other registers before the zero-edge map. If initial R6=n>0, exactly n bodies execute, leaving R6=R5=0 and every other register unchanged. Apply that node's literal zero-edge affine map once. The complete macro takes n+1 outer affine graph steps. Clearing R5 unconditionally would strengthen the transformation incorrectly at n=0, even if a particular later exit happens to erase it.

## C. Composition and the 189-node guarded macro core

All 178 zero-edge targets either are retained or lead through another one of these 178 total loops. The checked exit relation is acyclic, with derived maximum rank 7. Entry 0 remains retained. The sole halt remains retained and has no outgoing edges.

Delete the 178 total loops from the 367-node graph. For each outgoing edge of a retained test:

1. Make its original zero/nonzero choice.
2. If nonzero, decrement its tested register once.
3. Apply its original affine edge matrix.
4. Follow the certified finite list of new total-loop summaries, including each one's zero-edge affine map.
5. Arrive at the next retained node.

This yields 189 retained vertices: 188 tests and one halt, with 376 labelled edges. There are 182 summary references across those edges; the longest list has seven. `GUARDED_CORE.json` records these expression circuits and bindings. `GUARDED_CORE_COMPACT.json` is an exactly round-tripped serialization sharing the original 33-matrix dictionary; its smaller file size is only a serialization fact. Neither representation deliberately expands compositions into high-degree polynomials. Each triangular map is piecewise quadratic, and a chain can have much higher expanded degree, so “189-node affine core” would be false. Use “guarded arithmetic macro core.”

Every new edge expands to a nonempty finite original affine run because it includes the retained test step. Each removed loop terminates for all natural inputs, regardless of which preceding path reached it. No removed node is halt, and no local self-loop can halt internally. Therefore deterministic finite-run prefix cancellation proves halting equivalence from every retained node and every register file, and preserves final registers. An arbitrary removed starting node can first use its checked finite entry-normalization path. Source entry 0 requires no such extra normalization.

The claimed contraction is therefore not justified merely by finite testing. Its required generic proof consists of the two small loop inductions above, finite path composition, and the existing deterministic positive-macro transport argument. The present finite checker verifies the concrete hypotheses, not those universal proof-assistant theorems.

## D. Smaller soundness interface: finite paths replace rank witnesses

For retained-node starts and this entry, it is unnecessary to require both a finite certified macro path AND separate ranks for its nodes. Checking every consecutive zero-edge target and that the path ends at a retained node already gives a finite concatenation of total local runs. Strictly positive progress comes from the retained test transition. The ranks are useful generation diagnostics, but can be omitted from the soundness certificate.

For a theorem starting at every removed vertex, either check one finite entry path per such vertex or establish that every removed vertex occurs in an already checked edge path. In the latter case, its required entry-normalization path is just that path's suffix. The concrete 182 references cover all 178 removed vertices, so no separately serialized entry paths are needed here. The incoming first-level affine contraction likewise records complete coverage of all 1,059 removed vertices. Alternatively use a fuel-bounded normalizer, reject on exhaustion and prove acceptance soundness for arbitrary fuel. Do not claim a global all-start theorem from unchecked or uncovered entry paths.

## E. Reuse existing library arithmetic before adding a new algebra interface

At the exact review commit, `L2Lib222.lean` blob `e37f9ec83666edb39579240b2a28ad150aaadbf8` already contains:

- `P_step` (lines 198–203), based on the existing `Cantor.tri` recursion.
- `pair162` (lines 205–248), an all-natural structured `dag222` contract adding `P(s1,tw)` to s2 while clearing s1 and tw, proved by induction on their sum.
- Transfer/copy/clear loop contracts on arbitrary nine-field register records.

These are not directly the narrower checkpoint contract above: `pair162` includes an initial transfer into both scratch registers before the register-6 test, and hence different zero-input behavior. Its `Rn` statement also uses `enc st`, which sets register indices at least 9 to zero. To reuse it for arbitrary unbounded register files, supply the untouched-register frame argument rather than silently imposing that zero-extension restriction. Rebinding an existing complete pair macro to canonical graph occurrences may be cleaner than formalizing a new matrix-power library, but requires a precise boundary/path adapter and a check that it preserves the arbitrary-register contract. The direct checkpoint induction is also small.

`RMDag.while_loop` requires its body to preserve the counter. The triangular body's first step can add old R1 into R6, so it cannot be instantiated directly without the one-shot initialization or a changed measure. `ArithmeticCantor.triangle_succ` is about arbitrary IOpen models and is more machinery than this ordinary Nat loop needs. Reuse `Cantor.tri` or `P_step`, not that unrelated model interface.

## F. Reproducible evidence

Run `python -I -B review_owned.py`. No received scripts are imported or executed. `OWN_AUDIT.json` records:

- 104 manifest payload hashes and four inherited Git blobs checked.
- Both 4,751-leaf source trees independently rebuilt into the identical 1,426-node, 2,850-edge graph.
- 1,059 incoming drain contractions and 367 affine-node edge products checked.
- 26,166 occurrence-level tests: each of 178 new loops at R6,R1=0..6 and R7=0..2, with nonzero values in other registers, compared across the original graph, affine graph and closed-form summary.
- 3,138,765 original checkpoint-graph transitions replayed, all nine outputs compared, and all outer affine step counts verified.

These are bounded regressions, not exhaustive quantification over natural register values, not kernel checks, and not a build-time comparison.
