# Tagged radix-three research candidate: 207 states

This is a bounded unsuccessful attempt to beat 194 using a different numerical syntax. It accompanies, and depends on the packet root for the retained compiler/runtime. The accepted 194-state deliverables are in the packet root; this 207-state candidate is research evidence.

The constructors are

- `I(a,b)=3*p(a,b)`;
- `U(x,A)=3*p(A,x)+2`;
- `M(a,b)=3*p(a,2*b)+1`;
- `E(a,b)=3*p(a,2*b+1)+1`.

Here `p` is the usual Cantor pairing. Unlike a naive coefficient-three substitution, parity of the second atom operand separates membership from equality. The accompanying mathematical note supplies a self-indexed primitive-recursive recoding proof; this folder records source implementation and measured state costs only.

## Source implementation

`nodeDouble` first transfers T into scratch X, then transfers X back into T with two increments per unit. Its direct shared implementation uses native controls 400, 401, and 402. Replace the common constructor multiplier 4 by 3. Before a membership constructor, insert DoubleT. For equality, insert DoubleT and one increment before the constructor, retaining only one increment after it. Universal syntax retains its two final increments. The AX word grows from 190 to 200 expanded macro tokens.

`check_algebra.py` checks the entire resulting AX word in a free term algebra, including all eleven outputs, both guard comparisons, every intermediate scratch precondition, all nine final registers, and the residual operand field. `algebra_receipt.json` records PASS. This checks symbolic expressions uniformly; it is not a sample of parameter values.

The naive old tree with inserted macros had an optimistic price 210; its changed source address tree did not pass the source-frame replay. It is **not** an accepted literal machine.

## Bounded optimization and actual accepted cost

A 300-second joint reassociation/independent-head-parameter-permutation search proposed 3,150,735 changes and accepted 203,239. Its best **optimistic** score was 66 effective readers, suggesting 203 total states. The screening engine only performs simultaneous-fold compatibility below score 65, so this 203 nomination required independent checking.

The frozen best grammar has 80 reader controls and 19 individually eligible fold pairs. Its optimistic disjoint matching bound is 14, but exact simultaneous compatibility checking permits only 10, giving **137+80−10=207 working states**. The difference is material: 203 is not a certified result.

`check_best.py` verifies that each of the six head segments differs only by a permutation of its three unrestricted parameters, exhaustively searches simultaneous fold choices, reconstructs the source graph, and replays all 4,831 symbolic source-frame branch contracts. It also verifies the complete blank startup frame after 57,922 physical transitions and graph reachability of all 207 controls. `best/receipt.json` and `best_check.log` record these results. This uses the construction-side arithmetic-block verifier; no new independent literal replay or end-to-end kernel proof is claimed for the 207-state research candidate.

## Reproduction

From this directory, with Python 3 and the standard library:

```sh
python3 check_algebra.py
python3 check_best.py search_run.best.grammar.json
```

The second command regenerates the exploratory `best/` folder. To rerun the bounded search with a C++17 compiler:

```sh
c++ -O3 -std=c++17 search.cpp -o /tmp/tag3-search
/tmp/tag3-search templates.txt leaf_attrs.txt /tmp/tag3-rerun 300 2026111519
```

Wall-clock stopping makes proposal counts machine-dependent. The frozen accepted candidate does not depend on rediscovering an annealing result. The C++ optimizer and compiler are derived from the supplied GH research packet; upstream notices and licenses are preserved under `../../licenses/` and `../../NOTICE.txt`.

Three specialized doubled-copy macros were also considered. A direct source-preserving implementation needs a new root, loop composition, and decrement controller per parameter, plus a shared double-increment body: ten new controls before further folding, while the three ordinary copies remain in use. This is only a direct construction cost, not a lower bound; no saving was established.
