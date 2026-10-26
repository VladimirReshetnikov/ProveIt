# Additional arithmetic simplifications

Pinned ProveIt commit: `553a5f7a463cbaab8800ff8148fef0bc5a9e1b22`.

## 1. Prove a Pell threshold at a fixed index

Target: `Computability/DiophantineConsistency/Lean/DiophantineConsistency/NativePellBootstrap.lean`, theorem `large_of_six_le` (lines 217–231).

The existing proof compares variable exponent `p - 1` with 5, transports a Pell lower bound through `Nat.sub_add_cancel`, and compares two exponential bases. None of this is needed for a fixed threshold 6. Use

    A (A²−1)² < A⁵ ≤ χ_A(5) ≤ ψ_A(6) ≤ ψ_A(p).

The first strict inequality is the same elementary bound already present. `Pell.xn_ge_a_pow hA 5` gives the second; the definitional successor equation (the statement of `Pell.yn_succ`) and `Nat.le_add_right` give the third; `(Pell.strictMono_y hA).monotone hp` gives the last. The public theorem statement is unchanged. There are no new helper declarations. The pinned declaration is 15 physical lines, including 13 proof-body lines; the replacement is 11 lines, including 9 proof-body lines. Thus the measured reduction is 4 lines (about 31% of this proof body). See `pell-metrics.json` and `pell-fixed-index.patch`. `PellAnchorSmall.lean` contains the complete same-statement replacement in an isolated namespace, importing only Mathlib's Pell module. Its source imports no theorem under replacement.

This is distinct from the excluded proposal to compare *bases* A and P at a common index for `main_index_gt_first`. It is also distinct from the small-ordinate fundamental-unit criterion, parameterized ratio estimates, and parity reuse. The novelty auditor found the exact old variable-exponent proof copied unchanged in three earlier replacement modules, with no proposal for this finite anchor.

A more elaborate finite-anchor identity is ψ_A(6)=6A⁵+20A³D+6AD² for D=A²−1, but it is unnecessary and should not be introduced into the production patch. The earlier `PellAnchor.lean` is exploratory, not recommended. Do not count its helpers against the direct replacement or present it as a second idea.

Validation: the final isolated proof compiled successfully with Lean 4.32.0 and the exact pinned Mathlib dependency (exit 0). The command was `lean -j1 PellAnchorSmall.lean`, with the dependency-only pinned `LEAN_PATH`; its sole import is `Mathlib.NumberTheory.PellMatiyasevic`. See `PellAnchorSmall.log` and `PellAnchorSmall-validation.json`. The 112.98-second elapsed time is an observed run under contention, not a performance comparison. The original repository theorem and every project module are absent from its import graph, so the check does not reuse the theorem under replacement. The full production module was not rebuilt by this agent. `git apply --check pell-fixed-index.patch` succeeds against the pinned checkout.

## 2. Compute selector masses from small color totals

Target: `CurrentKernel2011.lean` (weighted signal-family sums, 287-419) and `CurrentSelectorTail2011.lean` (right/left low-family sums, 129-136). General finite chunk assembly and packed-field descriptors are explicitly treated as already applied. Do not credit this proposal with removing the old handwritten chunk ladder.

For an arbitrary tile family T define n=|T| and W,N,E,S as sums of west,north,east,south colors. Since the actual selector weight is

    1 + 1024 (1+w+256n+131072e+33554432s),

its sum is

    1025 n + 1024 W + 262144 N + 134217728 E + 34359738368 S.

The exact family moment vectors (n,W,N,E,S), independently recomputed from the current authenticated action cache, are:

| Family | n | W | N | E | S |
|---|---:|---:|---:|---:|---:|
| Start | 1 | 2 | 435 | 3 | 1 |
| Transitions | 430 | 18147 | 93095 | 34432 | 189 |
| Copies | 4 | 0 | 866 | 0 | 866 |
| Right signals | 398 | 41790 | 199 | 0 | 91723 |
| Left signals | 90 | 0 | 45 | 20430 | 10965 |
| Tail | 19 | 27 | 7419 | 22 | 6994 |
| All | 942 | 59966 | 102059 | 54887 | 110738 |

These yield exactly the original selector mass 3812322332357550.

The useful further step is symbolic signal-family summation. Write d=0 or1, let Q be the target list (not a tile list), n=length Q, qsum=sum Q, rsum=sum(rail d) Q. Each target emits the two bit rows b=0,1. Its total moments are

    (2n, 2d rsum, n, 2(1−d) rsum, 4 qsum + 5n).

Consequently its exact selector mass is

    171798956034 n + 137438953472 qsum
      + (if d then 2048 else 268435456) rsum.

`SignalMomentsCore.lean` contains a proposed proof of this symbolic identity using the actual source `Tile`, `rail`, `headColor`, and `selectorWeight`. Its isolated compiler attempt timed out after 300 seconds without diagnostics; it is an unvalidated design artifact. `SignalMoments.lean` adds an actual right-family client, also unvalidated. This is a new verification boundary: large packed weights are reconstructed from small target statistics and never evaluated per tile. It remains different after a generic balanced chunk theorem is assumed, because that theorem would still certify weighted leaves. A field descriptor only changes index plumbing; it does not prove these family sums.

Four actual endpoints can share the symbolic formula:

| Endpoint | n targets | sum targets | sum rails | weight sum |
|---|---:|---:|---:|---:|
| Right full | 199 | 22682 | 20895 | 3151578377695630 |
| Left full | 45 | 2685 | 10215 | 379496611276890 |
| Right south≤45 | 7 | 39 | 63 | 6562712006670 |
| Left south≤45 | 17 | 215 | 3621 | 33441962035234 |

For the low sums, `headColor q b≤45` is equivalent to `q≤21` when b∈{0,1}, so exactly an initial segment of the target list is retained. A further reusable rank identity gives `rsum=c*n+n*(n−1)/2`, c=205−199d. It applies to a whole target list and to these initial segments because the rails count earlier target elements. This identity and the cutoff adapter are design work, not certified here unless separately compiled later.

Cost accounting: replacing one packed checksum by five moment checks alone may increase source. The recommendation is justified by the four symbolic signal-family endpoints and reuse under packing/layout changes. Include the algebraic bridge, target-list sum checks, rank-sum proof and cutoff bridge in any net comparison. No net repository line reduction, compile-time gain, smaller proof term, or full-module replacement is claimed for this second proposal. A pilot on `rightWeights_sum` should decide whether the broader migration pays for itself.

## Files and checks

- `PellAnchorSmall.lean`: recommended direct replacement, successfully checked; exact log/JSON supplied.
- `ColorMoments.lean`: exploratory affine formula and actual right-signal moment pilot; timed out, omit from certified deliverables.
- `SignalMomentsCore.lean`: symbolic signal formula, timed out after 300 seconds, design-only. `SignalMoments.lean` adds an unvalidated actual right-signal client.
- `moments.py`/`moments.json`: independent Python arithmetic evidence. Not a Lean proof. Reads the pinned actionCache and reconstructs rows exactly as the visible constructors do; source SHA-256 recorded.

No remote repository writes were performed.
