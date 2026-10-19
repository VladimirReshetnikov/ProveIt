# Source and logical-basis integration experiments

This directory is a portable research supplement for the **237-state checkpoint at ProveIt commit `ecb4df12d256704d9115d4860f6ccb7b3443ef4a`**. It contains reproducible source-cost measurements, a compositional macro proof, and a counterexample to a tempting decoder edit. It does not introduce a verified smaller binary Turing machine. Later upstream candidates require a separate comparison.

## Results and exact scope

The pinned source has 6,455 instruction occurrences and 224 distinct live DAG nodes, counting both binary sequence nodes and primitive instruction nodes. Its longest run of zero edges is six; its maximum path depth is 48. These are **source measurements**, not counts of binary decoder states or estimates of a finished machine's size.

| Replacement for the four-parameter Łukasiewicz row | Variants | Best live source nodes | Maximum zero run | Depth | AX macro calls |
| --- | ---: | ---: | ---: | ---: | ---: |
| Original row, exact reparse | 1 | 224 | 6 | 48 | 186 |
| K, S, Peirce | 288 | 226 | 6 | 36 | 196 |
| K, S, Q4 | 288 | 227 | 6 | 45 | 198 |
| K, S, quantified DNE | 288 | 227 | 6 | 43 | 198 |
| K, S, unrestricted DNE | 288 | 227 | 6 | 35 | 194 |

Here `F=1`, `Not(A)=Imp(A,F)`, and the third schemas are:

* Peirce: `Imp(Imp(Imp(a,b),a),a)`.
* Q4: `Imp(All(a,b),All(a,All(a,b)))`.
* Quantified DNE: `Imp(Not(Not(All(a,b))),All(a,b))`.
* Unrestricted DNE: `Imp(Not(Not(a)),a)`.

K and S have their usual implication forms. The logical adequacy of the new Q4/QDN/DNE interfaces belongs to the accompanying foundations proof. This directory checks their exact emitted formulas and source composition; it does not replace that proof. K/S/Peirce itself is prior art in Sources 91 and 95, including a previously measured 250-state routed control. We make no novelty claim for that basis.

Each 288-case sweep covers six **shared** permutations of the register roles `a,b,c`, six orders of the new three schemas, and eight insertion positions among the seven retained logical rows. This is not the larger family in which each schema chooses its register roles independently. For example, independent K/S/DNE orientations would give 5,184 variants under the same order/insertion convention. No exhaustive grammar lower bound follows from the reported minima.

We also reprice all 64 members of Source 91's six-double-negation bundle family. Only the unchanged bundle reaches 224 nodes. The best changed member is mask 4 at 225 nodes, zero run six, depth 42. This is a new integration of an existing family into the pinned source dictionary, not a new Boolean identity.

Finally, we combine the saved best representative from each basis sweep with the six-leaf NIP specialization. All four scores remain unchanged. This is a controlled four-case composition, not an exhaustive joint optimization.

## What the source-cost algorithm proves

`pricing.py` reads the exact pinned source DAG and original macro word. It decomposes a source block only when both children are syntactically closed: neither can break or continue into the other's control context. This produces a fine vocabulary of exact closed register programs. Expanding the 186 original macro calls reproduces the current AX block's **entire 1,270-atom word exactly**.

The dictionary comprises every live closed subtree of the pinned source. Dynamic programming finds covers of each new word by existing dictionary phrases for three fixed penalties. A second dynamic program selects binary associations, retaining five shape candidates per interval after grouping by leading-zero length and depth. It rejects final trees with a zero run above six. The final escaping `CB1` is included as the rightmost leaf during parsing; its local path consists only of ones, so reassociation inserts no additional zero ancestor and preserves the break target.

This search is deliberately bounded. In particular, it does not synthesize an arbitrary new globally optimal grammar, search all independent schema orientations, or co-synthesize a new binary runtime. A source with more than 224 nodes could still lead to a smaller binary machine through different instruction encoding or helper sharing. The measurements neither establish nor exclude that possibility.

## The all-register macro bridge

Matching the original complete word alone would not justify arbitrary new compositions of its parts. `check_macro_contracts.py` supplies the missing compositional check for all 19 macros used by these emitters.

Eighteen macros match the pinned original Wade/Mira-Cult DAG through an exact finite product of their decrement-control graphs. Between successive decrements, the checker compares all nine accumulated increment counts. It covers both zero and positive outcomes and the distinguished return. Jeff Ketchersid's separately supplied path evaluator replays every graph edge.

The current gate macro 131 contains a prior transfer-loop rotation. Before graph comparison, the adapter applies this explicit lemma for distinct registers X and Y:

`[Y++; (decrement X; continue 2)]`

has the same total register function as

`[(decrement X; (Y++; continue 2)); Y++]`.

If X initially contains n, each side terminates, clears X, and increments Y by n+1. Induction on n proves the statement. The distinct-register premise is checked by the adapter. Applying this lemma once, with X=R6 and Y=R5, reduces gate 131 to the shape accepted by the graph product. The complete replay has **19 macro contracts, 192 graph pairs, and 346 decrement edges**. It preserves all nine return registers and divergence of arbitrary macro compositions. This is ordinary executable mathematical evidence, not a new proof-assistant endpoint.

## The rejected NIP decoder graft

The inherited six-leaf NIP test removes six expanded source instructions but still has 224 live DAG nodes. A direct edit of five binary rows is unsafe because the same decoder states also serve as runtime helpers.

`nip_counterexample.py` constructs the attempted edit from the supplied 237-state table and checks an unchanged instruction: `CI8` at path `01010`, with all nine logical registers zero, one zero spare register, and the standard legal runtime frame. The baseline returns the correct frame after 636 transitions. The altered table returns after 648 transitions with a different register tape. The first relevant change is old row `46/0`: the baseline proceeds to state 17, whereas the attempted NIP edit proceeds to state 62.

The saved broader finite replay contains 290 failing cases among 8,378 zero/one guard cases: 289 increments and one break. A single legal counterexample already rejects this graft. Neither that counterexample nor these finite cases assert what happens on the blank run. The rejected table is constructed only inside the checker and is never labeled a candidate artifact.

## Affine substitutions

`affine_substitutions.py` consumes the parent investigation's exact rational affine invariant, stored compactly as `affine_facts.json.gz`. Facts are homogeneous row-space generators in coordinates `[1,R0,...,R8]`, one basis per original source occurrence. The parent's invariant analysis supplies the initialization, transfer, join and post-fixpoint proof; this script checks substitutions under those facts.

The restricted recognizer proves total affine semantics for increments, unary transfer loops and closed compositions, recognizing 35 live nodes. Every proposed replacement is compared on every basis vector at every occurrence of the original shared node. There is only one distinct-node replacement, node 199 by node 200, and it increases the total DAG count from 224 to 225. There is no recognized identity node and no additional invariant-conditioned commutation beyond the two already globally valid ones. This does not exclude nonlinear identities or a richer recognized program class.

## Reproduction

Use Python 3.10 or later with its standard library; Python 3.12 was used for these runs. Do not use `-O`, since assertions are proof checks. All commands run from this directory and use local data.

Fast checks:

```sh
python -B audit_delivery.py
python -B check_macro_contracts.py
python -B nip_counterexample.py
python -B affine_substitutions.py
```

Full source sweeps, each writing into a separate `replay_*` directory:

```sh
python -B pricing.py --basis ksp
python -B pricing.py --basis ksq4
python -B pricing.py --basis ksqdn
python -B pricing.py --basis ksdne
python -B price_bundle.py
python -B price_joint_nip.py
```

The optional broader NIP replay is:

```sh
python -B nip_counterexample.py --all-cases
```

`receipts/` holds completed measurements; `best_sources/` holds compact DAGs rather than binary tables. `macro_contract_certificates.json` is the replayed macro certificate. `MANIFEST.json` records exact file hashes and provenance, including inherited code and licenses. The smaller files can be incorporated directly into ProveIt without vendoring the full repository or any earlier incoming archive.
