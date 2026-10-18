# Exact negation fusion for the ZFC consistency enumerator

This package records a source transformation and a complete **255-working-state binary table** with a checked blank prefix. It does **not** improve the 252-state record. It does expose a useful arithmetic simplification: logical negation can preserve the entire formula stack without encoding the old top into that stack and immediately decoding it again.

The concrete transformation is

\[
 P(x,y)=\frac{(x+y)(x+y+1)}2+y,\qquad
 \operatorname{wn}(t)=4P(t,1)=4\bigl(P(0,t)+2\bigr).
\]

The existing pairing routine accumulates into its output register. Therefore two increments of that output, followed by the existing pairing-and-multiply tail, implement negation exactly. Formula codes, all other registers, the complete stack value, and the logical presentation remain the same at clean macro boundaries.

This is an ordinary arithmetic argument plus executable evidence. No new Lean or Coq consistency endpoint is supplied. The accompanying report must keep the source-macro proof, conditional binary-runtime check, literal initialization check, and final consistency-calibration obligation distinct.

## Reproduce

Python 3.10 or newer, standard library only:

```sh
python -B verify.py
python -B verify_runtime.py --output runtime_recheck.json
```

Run these commands from this directory, or pass absolute paths to the scripts. Neither command needs a ProveIt checkout, network access, a proof assistant, or an installed TM simulator. Assertions must be enabled; `-O` and `-OO` are rejected.

`verify.py` finishes in about one second on the development host. It independently interprets 149 macro fixtures per variant, regenerates four complete 281-state Wade tables, inverts every emitted decoder edge, and compares the complete initial tapes. `verify_runtime.py` took about 16 seconds on that host. It reconstructs the optimized source transformation, replays six state deletions with all 7,221 affine cases after every deletion, and compares the final table's entire 82,552-step blank prefix with the pinned 252 table. Times are observations, not complexity bounds.

To emit a fresh copy of the four Wade controls into a new or empty directory:

```sh
python -B verify.py --write regenerated_controls
```

`results.json` and `runtime_results.json` contain the measured successful runs. Exact input and table hashes appear there and inside the checkers. The two JSON files in `logs/` retain the original uniform and mixed-fold search results. Those search logs are historical measurements; the portable checker replays the six accepted folds, rather than rerunning the complete search.

## Register and source conventions

The source declaration order is

| Index | Name here | Upstream name |
|---:|:---:|---|
| 0 | N | nextproof |
| 1 | T | topwff |
| 2 | W | wffstack |
| 3 | A | axiomcode |
| 4 | D | param1 |
| 5 | H | param2 |
| 6 | X | scratch1 |
| 7 | Y | scratch2 |
| 8 | L | prooflist |

The clean boundary hypothesis is **X = Y = 0**. The values of N, T, W, A, D, H, and L are arbitrary natural numbers for the macro contract. In particular, W can be arbitrarily large; the replacement never reads or writes W.

The relevant original 219-node DAG rows are:

```text
117 = (Decnz Y, Node118)            # multiply Y by 4 into T
118 = (Node156, Continue2)
120 = (Node162, Node117)            # pair, then multiply
156 = (Node157, Inc T)              # add four to T
157 = (Node159, Inc T)
159 = (Inc T, Inc T)
162 = (Node215, Node163)            # additive Cantor pairing
163 = (Decnz X, Node164)
164 = (Node165, Continue3)
165 = (Inc Y, Node208)
171 = (Node216, Node172)            # push current top onto W
177 = (Node171, Inc T)              # push top; construct code 1
208 = (Decnz X, Node186)            # drain X into T
215 = (Decnz T, Node187)            # drain T into both X and Y
216 = (Decnz T, Node185)            # drain T into X
218 = (Node177, Node119)            # wn: implication to code 1
```

The loop-continuation wrappers and all remaining literal rows are in unchanged `data/Dag254.v`. Node 119 decodes the stack head, invokes the pairing tail, and restores the old stack tail. The old `wn` therefore temporarily replaces W by `P(T,W)` before recovering T and W. The new implementation bypasses that stack round trip.

## Unbounded arithmetic proof

Write `tri(s) = s(s+1)/2`. Then

\[
 P(t,1)=\operatorname{tri}(t+1)+1
       =\operatorname{tri}(t)+t+2
       =P(0,t)+2.
\]

Multiplying by four gives the equivalent polynomial `2t² + 6t + 8`. The identity holds for every natural t; the fixture range is not used to justify it.

### The additive contract of pairing node 162

For arbitrary initial values `(X,T,Y)=(x,t,y)`, node 162 terminates normally with

\[
 (X,T,Y)=(0,0,y+P(x,t)).
\]

Every other register is unchanged. The invariant is

\[
                  Y+P(X,T)=y+P(x,t).
\]

Node 215 transfers one unit at a time from T into both X and Y. An elementary step is `(X,T,Y) → (X+1,T−1,Y+1)`. The sum `X+T` is fixed during this inner loop, so `P(X,T)` decreases by one and the invariant holds. The loop terminates because T decreases. Its result has `T=0` and `X=x+t`.

At that boundary, let `X=s`. If s is zero, pairing returns normally. Otherwise the remaining code decrements X, increments Y once, and drains the remaining X into T. The normalized change is

\[
             (s,0,y')\longmapsto(0,s-1,y'+1).
\]

The drain terminates because X decreases. The identity

\[
               1+P(0,s-1)=P(s,0)\quad(s>0)
\]

preserves the invariant across this part of the loop. The outer rank `X+T` decreases from s to `s−1` before the next complete pairing iteration. Thus the outer loop also terminates, and its zero-rank exit proves the stated additive contract. These arguments apply to arbitrary natural values, including a nonzero initial output Y.

### The multiply-and-clear contract of node 117

For arbitrary `(T,Y)=(t,y)`, each loop iteration decrements Y once and adds four to T. The invariant is `T + 4Y = t + 4y`; the rank is Y. The loop terminates with `(T,Y)=(t+4y,0)`, preserving every other register.

Combining the two contracts shows that node 120 maps arbitrary `(X,T,Y)=(x,t,y)` to

\[
                 (0,4(y+P(x,t)),0).
\]

The position order in this display is X,T,Y.

### The prefilled negation replacement

Begin with `X=Y=0` and `T=t`. Increment Y twice and call node 120. Its result is

\[
       X=Y=0,\qquad T=4(2+P(0,t))=4P(t,1).
\]

The replacement consists entirely of nodes that touch only X,T,Y, so preservation of W and the other five fields follows directly from the code. The old negation contract has the same result and the same clean scratch boundary. This gives an exact local source-macro substitution, rather than a change of formula representation.

## Three explicit source variants

All unlisted nodes are literally unchanged. Node 177 has only node 218 as its incoming parent in the original 219-node DAG, so reusing its slot does not silently change another source macro.

| Variant | New node 177 | New node 218 | Arithmetic |
|---|---|---|---|
| `direct_transfer` | `(Inc T, Node120)` | `(Node216, Node177)` | Transfer t into X, set T to 1, pair and multiply |
| `output_prefill2` | `(Inc Y, Inc Y)` | `(Node177, Node120)` | `4(P(0,t)+2)` |
| `zerohead_add8` | `(Node156, Node156)` | `(Node120, Node177)` | `4P(0,t)+8` |

The transfer routine has invariant `X+T` and donor rank T. Together with the contracts above, this proves all three replacements for the same clean hypothesis. The prefilled variant gives the smallest unfolded instruction tree among these three choices.

| Source variant | Reachable source DAG nodes | Unfolded instruction leaves | Wade working states | Rows |
|---|---:|---:|---:|---:|
| Original | 219 | 6,460 | 281 | 562 |
| Direct transfer | 219 | 5,650 | 281 | 562 |
| Prefill output by 2 | 219 | 5,590 | 281 | 562 |
| Add 8 after pairing | 219 | 5,770 | 281 | 562 |

The 281-state controls include all 219 decision states and all 62 framework states. The compiler has one missing row, `1.inc` reading 1; each control totalizes that row by preserving the symbol, moving right, and halting. Every table is fully specified. All four reach `main().0` after exactly 39,769 literal TM moves with the same state, head position, and complete tape. This is the Wade backend's own initialization, distinct from the optimized 252/255 tables' initialization.

For `T=3`, the independent source interpreter counted the following **primitive register-machine instructions**, not TM moves:

| Initial W | Original negation | Direct transfer | Prefill output by 2 | Add 8 afterward |
|---:|---:|---:|---:|---:|
| 0 | 254 | 146 | 119 | 113 |
| 10 | 1,944 | 146 | 119 | 113 |
| 50 | 26,704 | 146 | 119 | 113 |
| 100 | 98,154 | 146 | 119 | 113 |

The original stack-dependent cost disappears because the replacement has no W operations. Reducing unfolded leaves or running time does not by itself reduce the shared decision graph or the complete TM state count.

## Applying the replacement to the optimized decoder

The gzip file `data/Prog254.v.gz` expands to the exact pinned upstream `Prog254.v`; its decompressed SHA-256 is checked. The portable verifier independently parses its 6,459 literal binary nodes. Its unfolding agrees exactly with `data/optimized_original203.json`, a shared 203-node representation.

The optimized source rebrackets sequences and commutes some increments. The matcher in `macro_signatures.py` treats straight sequences of increments as vectors of increment counts. It retains every tested register, both decrement outcomes, termination, and control divergence, then computes a finite operation-bisimulation signature. This is an executable structural matcher, not a new proof-assistant theorem.

The only optimized closed subtree matching original node 218 is node 92. The only subtree matching node 120 is node 56. Replacing all **30** occurrences of the former by

```text
Node(Node(Inc Y, Inc Y), optimized Node56)
```

reproduces the entire changed tree exactly. The changed shared decoder still has 203 nodes, maximum path depth 34, maximum zero run 7, and 5,590 instruction sites. There are 1,631 decrement sites, so the complete instruction audit has `5590 + 1631 = 7221` guarded cases.

## The complete 255-state table

`prepared_runtime/prefill255.tm` has **255 working states and 510 rows**. Labels are inherited and nonconsecutive. The start is old state 64, the instruction-dispatch state is old 96, and the separate halt label is 254. The physical primary-register order is `W,L,T,D,A,Y,N,H,X`. Calling this table “254 states” because its halt is labelled 254 would be incorrect.

The optimized source was initially emitted through the existing contextual decoder emitter. After unused runtime states were removed, the result had 261 working states. Its full affine verification succeeded. Six folds then gave 255 states:

```text
61 → 301, 302 → 45, 303 → 32,
177 → 203, 213 → 134, 237 → 0.
```

Each fold redirects every incoming transition from the deleted state to the retained state and deletes the former's two rows. It preserves every protected Box row. The standalone checker replays all six folds and reruns all 7,221 cases after each one. The final exact SHA-256 is

```text
463067a5a42476c8efeacb296d83df69b7366b0d1894a4e11f418840e79fb0fb
```

The final table's literal blank run agrees exactly with the reference252 table after **82,552 moves**: state 96, head position 2, and the identical set of all 77 nonzero tape cells. The prepared frame has the same nine zero primary registers and the same spare blocks as the reference. The portable replay compares the full set of occupied tape positions, so this check does not ignore trailing scratch data.

### What the affine verification means

Each successful case starts at dispatch state 96 with its exact program-counter bits, gap `40+n` for arbitrary `n ≥ 0`, and an arbitrary encoded register file with at least nine registers. A decrement case supplies the zero/nonzero hypothesis for the register actually selected by that instruction. The conclusion is the required next counter word, the exact updated register effect, and preserved surrounding tape. The checker requires at least one literal TM transition; every checked case contains at least 13.

The checker uses the four existing register-Box contracts. All **55 protected transition rows** supporting those contracts match the pinned 252 reference literally. The exact upstream checker source is included unchanged. A documented loader adapter supplies an inert value for its unused `cost_search` driver import; only `run`, `canon`, and `oracle` are called. No upstream driver or repository path is executed.

This is stronger than testing finitely many register values, but it is conditional on the stated Box contracts and frame hypotheses. The changed source-to-calculus connection and the new binary consistency theorem have not been checked by a proof-assistant kernel in this package. The exact blank prefix discharges initialization as a finite calculation; it does not discharge those remaining mathematical obligations.

### Search limits

The recorded greedy uniform-fold search reached its eligible fixed point at 255 states. A subsequent eligible mixed-row fold pass found no further deletion. “Eligible” excludes deleting dispatch/start states, changing protected rows, and deleting targets needed by protected rows. In a mixed fold, one row of the retained state is copied from the deleted state and its other row is retained. Candidate failures are checked against the same affine case family; accepted changes receive a full pass. The logs record the precise candidate counts and rejected case indices.

These are finite negative results for those particular local search neighborhoods. They do not establish minimality of this table, of the arithmetic encoding, or of binary consistency machines. A different decoder-sharing assignment, a synthesized multi-state replacement, or a stronger source invariant could behave differently.

## Attribution and integration

See `PROVENANCE.md` for exact source paths, pins, and licensing boundaries. The original machine is due to Mira-Cult, Jeff supplies the referenced verification, and the public compiler is Andrew James Wade's work. The 252 table and contextual/affine research infrastructure are ProveIt prior work. The new contribution here is the explicitly described source fusion, its exact optimized-tree application, the resulting tables and replay, and the measured search results.

The portable package can be incorporated under a research-results directory. The frozen `candidate-permutation252` benchmark should remain the baseline until a smaller complete table and the desired proof endpoint have actually been obtained.
