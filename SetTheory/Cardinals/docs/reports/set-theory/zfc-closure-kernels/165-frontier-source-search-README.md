# Source and encoding experiments beyond K215

## Status and scope

This packet contains reproducible source-level research. It does **not** contain an accepted machine with 214 or fewer working states. A source DAG node is not a Turing-machine state. None of the new encodings in this packet has passed the full all-natural-register binary runtime, blank-tape initialization, dense canonicalization, and mathematical calibration chain required to accept a new Busy Beaver candidate.

The accepted parent is ProveIt commit `2762b8a183830b1f5a30cf059ffb4d92e77cddde`, directory `Computability/BusyBeaver/Research/ZFC/candidate-k215`. Its source has 202 distinct DAG nodes, 4,751 primitive leaves, maximum depth 47, and maximum zero run 6. The exact source SHA-256 is `17af207195179b2508bf91154cd00739374f8862207ca21b9a3cb9098aa6f5ba`; the native machine SHA-256 is `9683d6ed9628e6ce407c315b08f5da3d063da94e92706f275ca0f33e8272e4b2`.

The source utilities are copied from that pinned repository. New experiment scripts use Python 3's standard library. The allocation experiments, summarized here but not used as acceptance evidence, used SciPy's mixed integer solver.

## Most promising new source geometry

Keep the pairing function and membership tag unchanged, but use

```text
I(a,b) = 4 P(a,b) + 3
R(a,b) = 4 P(a,b) + 1
Q(a,b) = 4 P(a,b)
E(a,b) = 4 P(a,b) + 2.
```

The source `tags_3102_0_202.json` has 202 DAG nodes, 4,824 primitive leaves, maximum depth 46, and maximum zero run 10. It therefore gives a different geometry at the same source-node cost. All 81 constructor calls were changed, including early generalization, dominated rho8, the theory bundle, and modus ponens. This is not a change of names in an annotation: the primitive arithmetic source changes.

The 81 calls have original tag census I:41, R:12, Q:22, E:6. Every occurrence of the common 27-leaf arithmetic base is an exact source subtree. `constructor_calls.json` records their original ordinal intervals. The generator verifies the primitive word for each call before changing increments.

Closed source reassociation immediately reduced the new encoding's maximum zero run from 10 to 8 without changing its 202-node cost or primitive guarded control-flow graph. The saved source is `closed_tags_3102_0_202_best1_202_z8.json`. A 420-second bounded closed-reassociation search completed 16,099 iterations with no better than 202 nodes and zero-run 8. Its frozen final source and log are included. A separate 300-second Q/E-swap search completed 12,830 iterations with no improvement on 203 nodes.

The new quantifier encoding has Q(0,0)=0. A mathematical calibration must treat code 0 consistently as a true base code and re-establish the actual code-semantic proof, the seed padding argument, and the dominated-rho8 bound. The usual raw syntactic code-translation argument alone is insufficient because native variable indices and formula codes share a number space. No binary machine has been accepted for this source.

A concrete additional obstruction was found: the inherited 3,728-node classical/dominated-rho8 certificate fails at node 8 if the old literal identity I(T,T)=T is removed. The new I3 encoding therefore does not yet have a lower consistency calibration. This is an open proof obligation, not a passed check.

The old protected-row allocator could not fit this geometry within its restricted allocation model. That negative result is not a lower bound: the model freezes old helper/engine rows and retains context-compatible exact old subtrees.

## Fresh equality binders

The existing equality row has the shape

```text
E(c,a) -> (E(c,b) -> Q_{f(a,b)} E(a,b)).
```

The accompanying formalism research proves that the binder can be replaced by a primitive-recursive function fresh off the diagonal: if a differs from b, then f(a,b) differs from both a and b. The diagonal case is handled by directly derivable equality reflexivity. This includes 4P, 4P+1, 4P+2, 4P+3, 2P, and a+b+1; unshifted P is not generally fresh. See the parent report's mathematical proof for the exact calculus hypotheses.

Direct source pricing against the accepted original encoding:

| Binder arithmetic | Source file | Distinct DAG nodes | Primitive leaves |
|---|---|---:|---:|
| 4P+1, accepted | sites215.json | 202 | 4751 |
| 4P | G_I.json | 203 | 4750 |
| 4P+2 | G_Q.json | 202 | 4752 |
| 4P+3 | G_E.json | 204 | 4753 |
| a+b+1 | G_sumAB1a.json | 204 | 4705 |

These counts illustrate why shortening the primitive word alone does not establish a smaller machine. The sum binder saves 46 primitive leaves but adds two distinct DAG nodes.

In the I3/R1/Q0/E2 encoding above, the 4P binder is also a 202-node source: `tags3102_binder0_0_202.json`, 4,823 leaves. This source still has maximum zero run 10.

We also computed the equality pair once, duplicated it, and added the needed tag difference to the top copy. A clean 24-leaf DUP macro preserves all parameter registers. If top is t and encoded stack is s, it returns top t and stack P(t,s), with scratch registers zero. Its loop invariant is elementary: first copy s into the two scratch accumulators; move t into the vacated stack register while adding t to the triangular-loop input; accumulate the triangular number; restore t; move the paired value to the stack. The existing 10-leaf pairing subroutine supplies the triangular loop. In the original R-binder row, compute R(a,b), duplicate it, add 2 to the top copy to get E(a,b), and quantify. This preserves the exact original formula. It shortens the source to 4,695 leaves but needs at least 210 DAG nodes among the enumerated local parenthesizations. Thus this particular common-subexpression optimization loses on the relevant source measure. `G_dup_1_0_5_210.json` is a representative; `g_dup.py` reproduces the finite experiment.

## Exhaustive finite searches and their limits

### Independent parameter permutations

Each of the seven unguarded logical row emitters may consistently permute its three parameter registers, independently of the others. Because all natural triples are enumerated, this preserves each axiom family. The gated theory bundle and early generalization/dominated-rho8 stages were held fixed.

The exact fixed-tree search covers all 6^7 = 279,936 choices. Its minimum is 202 DAG nodes, attained by four vectors:

1. Original parameters.
2. Exchange registers 3 and 5 in rho6.
3. Exchange registers 3 and 5 in both rho4 and rho2.
4. Make both changes above.

The exact count is obtained by separating constant subtrees, row-dependent forests, and 39 cross-row contexts. After replacing the parameter labels by a common placeholder, the cross contexts are pairwise distinct and disjoint from all possible local subtree shapes. Therefore their contribution is constant, and the remaining exact cost is a bitset union of the seven selected row-forest node sets. All four minima are also checked by reconstructing the complete literal source tree. See `rowperm_exact.py`, `row_permutation_exact_summary.json`, and the four `rowexact_*_202.json` files.

This proves a minimum only for those fixed source-tree parameter permutations.

### Whole-row orders

The original logical row spans are:

| Row | Primitive interval, half-open |
|---|---|
| G / rho7 | [479,888) |
| rho6 | [888,1171) |
| rho5 | [1171,1467) |
| rho4 | [1467,1766) |
| rho3 | [1766,2062) |
| rho2 | [2062,2412) |
| rho1 | [2412,2643) |

The exact original scaffold can be decomposed into 453 minimal closed components across these seven rows. We kept that scaffold and substituted the component sequence induced by every whole-row order. Repeating all 7! = 5,040 orders for each of the four neutral parameter variants gives 20,160 cases. The minimum remains 202, attained only by the original order in each variant. See `roworder_scaffold.py` and `row_order_scaffold_summary.json`.

A second, less favorable construction replaced each interval by a right-serial forest of its maximal old closed subtrees. All 5,040 orders then had minimum 207. The identity already costs 207 because it destroys cross-boundary source sharing. This is recorded to make clear why arbitrary whole-block splicing is not a faithful test of the best source grammar for a new word.

Neither search optimizes over all parenthesizations.

### Residue tags

All six permutations of I/Q/E tags 0/2/3 were explored, with R fixed at tag 1 so that the existing falsity code 1 remains R(0,0). Local choices for adding and deleting tag increments were also enumerated. The original arrangement costs 202; the new I3/Q0/E2 arrangement also costs 202; the other best directly constructed arrangements cost 203 or 206. `tag_permutations.py` reproduces this bounded search.

### Allocation and command orders

All six NIP/DROP/MP command-body permutations retain a 202-node source. Under the inherited protected-row allocation model, three allocate at 215 native states and three have no allocation. Relaxing two potentially overprotected leaf-entry rows, (27,1) and (103,1), did not produce 214 states. Of the neutral parameter variants, the rho6 exchange allocates with complete decoder-prefix binding at 215; the other two nontrivial variants are infeasible in that restricted model. No new 214-state survivor existed to send to a full runtime checker.

The portable allocators `allocate215.py` and `allocate215_relax.py`, baseline table, and inherited row filter are included. For example, run `python3 allocate215_relax.py --source perm021.json --output allocation-replay --limit 20`. The output directory must be new. SciPy and NumPy are required for this optional replay.

The allocation summaries are synthesis evidence only. A complete decoder-prefix audit is weaker than a full source-primitive runtime proof and blank-tape initialization.

## Reproduction

Run from this directory, or invoke the scripts by absolute path:

```sh
python3 verify_source_packet.py
python3 tag_permutations.py
python3 rowperm_exact.py
python3 roworder_scaffold.py
python3 g_dup.py
```

The first three commands are quick. The 20,160-case row-order search takes roughly one to two minutes in the development environment. The closed reassociation searches are bounded heuristic searches; the frozen resulting source files and their exact word/CFG comparisons are stronger reproducibility artifacts than a wall-clock-bounded search trajectory.

`MANIFEST.json` records the frozen packet's file hashes. Summary paths have been made relative for portability. Counts and negative solver outcomes should not be promoted to mathematical nonexistence claims or candidate acceptance claims.


## Explicit rejected binary experiment

The subdirectory `rejected-enumerator-13-108` contains a 214-state table with a concrete source-simulation counterexample and full 656-step trace. This artifact documents why a tempting state fold fails; it is excluded from every acceptance claim.

## Final targeted marker extension

The `targeted-marker-extension` subdirectory freezes exact predecessor-history invariants for the normalized CB1 scheduler and the 91/73 selector target, the obstruction to the proposed state123 selector, and the separate experiment that rewrites state13 incoming marker bits. Its README distinguishes exact history facts from bounded synthesis filters.
