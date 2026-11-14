# Independent review of the frozen MP196 prototype

**Reviewed table:** dense SHA-256 `c14cc614c8f33a67697b4fbc3b502ee5c8c6b3764ef721cd1e0c09f3810a97f3`; native SHA-256 `7689bf1cf5843f3f2c27ac3e3f7da2a84b28a8bce1d9f6458209579012ef6271`.

The 196-state construction supersedes the positive-target 201/200/199 experiments. This review concerns the exact `inc H` construction in `reduction_work/mp196_prototype`, not its experimental association or decrement variants. No mathematical blocker was found, subject to the stated inherited numerical-calculus calibration and generic arithmetic tape-block lemmas. It remains three states above the requested strict target of at most 193.

## 1. Exact command effect

The inherited MP reader and implication constructor are unchanged. They form `I(t,k)`, with `k=d+x`, and leave `D=k`. The old comparison with the cache remains unchanged too. On inequality it clears `T,H,X,Y` and returns `(0,w,k,0)`.

On equality, the source success splice is `node51 ; inc H ; node7`. The delivered resolved source realizes it as follows:

- Sites 3634–3637 transfer D into both T and X. Entry has `T=H=X=Y=0,D=k`. After j positive iterations, `T=X=j,D=k−j`, and every other register is framed. Termination gives `T=X=k,D=0`.
- Site 3638 sets H to 1.
- Sites 3639–3648 use the inherited destructive equality comparator. They compare `H=1` with `X=k`, while framing T. Equality occurs precisely when k=1 and reaches source halt 3649. If k=0 or k≥2, the mismatch/cleanup path clears H and X, reaches site 3650, and returns to command-loop site 25.

Thus the new MP succeeds with `(k,w,0,0)` when `k!=1` and halts when `k=1`. A failed comparison does not trigger this halt. The zero-target success is permitted and leaves the stack unchanged.

The last point simplifies the proof compiler relative to the positive-target experiment. `Discard=MP_0` on a clean store `(t,w,0,0)` either fails when t>0 or succeeds when t=0; both cases return `(0,w,0,0)`. `Offset_0` has the same safe zero-alias behavior; positive `Offset_i` comparisons fail as required. `Push` still fails its final MP comparison because its cache has residue 2 modulo 4, while implication codes have residue 0. The proof-node compiler now uses `MP_b`, rather than `MP_(b−1)`. Its successful nonhalting case is followed by the same Pop normalization.

## 2. Shift, zero stacks, and soundness

The original literal Shift remains intact: it halts if `t+h=1` and otherwise performs `(h,tl(w),d,hd(w))`. There are therefore **two source halt leaves**, 10 and 3649, sharing the **single physical halting row** `(68,1)`. The universal runtime checks include both source leaves; no contract is omitted in MP196.

At every completed, nonhalting command boundary, no current top, cache, or canonical stack entry has code 1. Initially all are zero; AX generates no code 1; MP returns either zero or its target different from 1; Shift transports existing entries. This is an arithmetic invariant and does not assume Con(PA). It makes the Shift halt unreachable after the initialized frame, so the literal initialized run agrees with the abstract protocol using total Shift.

The invariant must be stated at command boundaries. For target 1, MP196 temporarily writes `T=1` inside the successful command and subsequently halts. It does not return that value to the next command. Saying it never physically stores code 1 would be false.

Soundness starts at the genuine initialized theorem-annotated store; arbitrary incoming stores are used only by the completeness compiler. The Cantor stack identities remain valid at zero, including `p(0,0)=0`; explicit wrapper calculations do not require an injective numerical stack-length representation. The all-store witness word and cofinal scheduler argument from the reviewed command proof therefore continue to apply.

## 3. Exact table and independent startup replay

Relative to the primary PA194 native table, MP196 changes only inherited row `(164,1)` to `1 R 400` and adds these four rows:

| State | Read 0 | Read 1 |
|---|---|---|
| 400 | `0 R 130` | `1 R 401` |
| 401 | `0 R 63` | `1 R 68` |

The dense table has 196 working controls, halt label 196, and 392 binary L/R rows. All 23 inherited arithmetic-oracle controls retain their rows. The builder resolves 3,663 source sites and checks all 4,768 primitive outcomes, with 1,476,043 symbolic operations and maximum 497 operations per outcome. Those figures are certificate checks using the inherited arithmetic-block lemmas, not a new kernel theorem.

The independent script `mp196_review_check.py` imports neither the construction compiler nor its symbolic runtime. It verifies the pinned baseline hash, the exact five-row construction, native/dense correspondence, the sole halting row, and the relevant source CFG. It then compares **every one of 58,154 literal startup transitions** in the two presentations and checks the complete final tape support. The endpoint is native state 84, head −2, source site 25, gap 48, physical primary registers `[0,0,0,0,0,0,2,0,0]`, and 26 one-valued spare registers. This is candidate K=2 and all other logical registers zero. Five independent success-block executions also check k=0,1,2,17,1000 with unrelated framing values.

The receipt is `mp196_independent_receipt.json`. A separate comparison, `mp196_census_comparison.json`, found no action-graph match among the pinned census's 503 spanning-root classes and two disconnected diagnostic classes. This is a finite corpus comparison, not a global novelty theorem.

## 4. Claim boundary

The new controller has an ordinary mathematical proof and complete executable source/tape bindings. A mathematical PA-equivalence claim still uses the explicitly attributed ordinary PA calibration of the unchanged numerical calculus and the inherited generic tape runtime arguments. This review does not independently re-prove those dependencies and does not claim a new Lean, Rocq, or iPRA endpoint. MP196 is a verified research construction under those dependencies; it does not improve the existing 194-state bound.

**Final prose correspondence check.** After the command-boundary wording correction, the final `source_proof.tex` (SHA-256 `b8252ceff5239ef4b512c5631ac92bfe288209b4bd8ebaccd00300083bca8853`) agrees with the inspected CFG, table edits, state counts, runtime scope, and startup. The corresponding README hash is `58061ce024a15a2d583ba1a4bf73f464eaf346fdc468ed2ef362d78e7ad29ebc`. The command proof reviewed alongside it is `logical_work/mp_halting_proof.tex`, SHA-256 `8f173e5ee7e917eca277d7157b7847013ccdef3cca41954f78a294d447ca63a7`. No outstanding source-controller discrepancy remains in those versions.
