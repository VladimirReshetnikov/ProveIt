# Review of the complete Schreier recoding of S193

**PASS, with no requested changes.** The frozen [author source](matrix193_schreier_recode.py), [receipt](matrix193_schreier_recode.json) and [proof](matrix193_schreier_recode.md) give a faithful recoding of all 20 active upper letters and all 193 directed matrix generators. Their finite-input target language is unchanged. The universal block's even-power Pell parameter becomes **1057**, while the generic conditional target assembly still costs **12=8M+4A** and the index and unbounded membership obligations remain unpaid. No complete Diophantine arithmetic improvement is inferred.

Disclosure: this reviewer proposed the finite covering used by the author. The present independent audit concerns the author's implementation, exact full matrices, accepting product and proof scope; it is not an independent discovery of that covering design. The review helper reads pinned JSON data and never imports or executes the author or predecessor Python.

## Frozen inputs

| Author file | SHA-256 |
| --- | --- |
| matrix193_schreier_recode.py | `2b88eaa45feb7f7255b5d4b8fb5b994ec07c1610b69f2461894f1d74ba623847` |
| matrix193_schreier_recode.json | `e2a01632a9689aaf9ef5966b9f92772b59d71cd4d392d46346ebc890aa8dc9ea` |
| matrix193_schreier_recode.md | `17d67b09b8c05a453be7f23b66a3582fd90c776d57d6e32979b78425bd904f55` |

The checker separately authenticates the four parent source-data/proof files: the S193 JSON and note, and the U15 repeated-block JSON and note. Their complete pins are recorded in the review receipt. The primary covering-space theorem is the one cited by the author, [Stallings, *Topology of Finite Graphs*](https://doi.org/10.1007/BF02095993). The finite labeled cover and its tree basis are reconstructed directly below.

## Covering and complete word theorem

A fresh breadth-first traversal reconstructs the tree paths in the 19-vertex cover. The P action fixes zero and cycles vertices 1 through 18; Q swaps zero and one and fixes the others. Both actions are permutations, the graph is connected, and it has 38 positive edges. Removing the 18 tree edges leaves precisely 20 chord loops. Each independently reconstructed loop agrees with the saved basis. The replacements `a=PQ^2`, `b=Q^-2` have the literal inverse `P=ab`, `Q^2=b^-1`; they therefore preserve a free basis, rather than merely a generating set.

A covering map induces an injection on fundamental groups. Collapsing its maximal tree identifies the 20 chord loops with a free basis. The parent's faithful P,Q representation then embeds that entire basis in integral matrices. The assignment accounts for the bits, all fifteen states, both brackets and separator. The inactive legacy X is correctly excluded. No assumption that an arbitrary pair of bit matrices automatically extends to the state alphabet is used.

All lower blocks and all tile words remain unchanged. The old and new upper maps are faithful embeddings of the same abstract free alphabet group. Combining the resulting upper-group isomorphism with the identity on the lower group preserves every generator-word equality to its corresponding target. Consequently it restricts to an isomorphism of the generated directed semigroups and gives the same membership answer for every finite configuration word. This verifies the whole finite-input theorem, independently of the saved accepting fixture. Its universal U15 dependency and the effective fixed-context initialization remain inherited; no arbitrary-program compiler is newly executed or certified here.

## Literal arrays, accepting product and costs

The review independently emits both old and new arrays using the parent tile strings. It uses a separate flat 2-by-2 matrix interpreter and the closed formula for every retained lower code. All **3,088 old entries and 3,088 new entries** match exactly. The audit checks the 193 lower blocks, 386 block determinants, matrix distinctness, all retained rules/tiles/metadata and the entire coefficient ledger.

The independent totals are 193 generators, 3,088 entry slots, 1,541 nonzero slots, maximum absolute entry **5,094,184,660**, maximum magnitude **33 bits**, and total entry magnitude **20,785 bits**. Thus the smaller Pell parameter accompanies larger maximum and total coefficient-bit metrics than the frozen S193 parent. No generator-count or arithmetic-operation reduction is claimed.

The preserved accepted word is `[110A0]`. Its 83-tile sequence still satisfies the complete literal word equation. Multiplying all 167 corresponding new generators independently produces

```
[[4243286625889, -2087432578696, 0, 0],
 [8612923416042, -4237021564079, 0, 0],
 [0, 0, 1, 2],
 [0, 0, 0, 1]].
```

All sixteen entries agree with the separately reconstructed new target. This is a materialized finite accepting product, not a substitute for the universal input theorem.

## Indexed-power boundary and reproducibility

Independent multiplication gives `Psi(W)=[[-47,6],[-8,1]]` and trace minus 46. Its square has trace 2,114, so `a0=1057`. With `D=Psi(W)^2-1057 I`, the exact matrix identity is `D^2=1117248 I`. This proves the quadratic-algebra formula for all powers; the checker additionally verifies 13 pairs of positive and negative powers by sequential multiplication, separately from the author's powering routine.

The assembly coefficients are fixed program-dependent constants once the contexts are selected. Supplying correctly indexed `chi_1057(x),psi_1057(x)` gives the stated 8M+4A assembly. Their Pell norm alone does not impose x, and the full unbounded matrix-membership relation is still absent. The packet neither claims a minimal trace nor contradicts the separate faithful-parabolic obstruction: trace minus 46 is still hyperbolic.

The full author source and note were read. The CLI's data authentication, duplicate/nonfinite JSON rejection, explicit checks and exact receipt comparison agree with its documented bounded scope. No public compiler API or hardening guarantee is inferred.

For the independently written review helper:

```sh
python3 review_matrix193_schreier_recode.py --root ABS_WIP --expect ABS_REVIEW_JSON
python3 -O review_matrix193_schreier_recode.py --root ABS_WIP --expect ABS_REVIEW_JSON
```

When the author trio is still in a separate scratch directory, add `--author-root ABS_AUTHOR_DIR`. Fresh normal and optimized exact review replays from `/` passed. All predecessor files remain untouched.
