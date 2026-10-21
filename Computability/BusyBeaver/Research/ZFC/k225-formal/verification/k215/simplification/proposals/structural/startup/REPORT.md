# Startup: a real but secondary simplification

Status: diagnostic code ran successfully; proposed Lean glue is **UNCOMPILED**. No received script was executed. No repository changes were published. No new formal theorem or speedup is claimed.

## What the implementation already does

Pinned source: ProveIt c9dc79323429112c698100f3226a6e4d56c8b782, `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/`.

- `KBoot.lstep` already avoids normalizing trailing blanks on every step.
- `KBoot.TT.look` already uses a balanced transition tree. Replacing linear lookup with an array is not a new opportunity here.
- `KBoot.lblock` runs powers of two via balanced recursion; `lblock_sound` and `lblock_reach` already provide the generic startup-refinement theorem.
- `KBoot215.boot_run` composes **13** block theorems, ending after 95,714 steps. There are 14 `KBoot215*` build modules when the assembly module is counted. Do not describe all 14 as computational blocks.
- `KDenseBridge.blank_iff` already proves the generic dense/sparse reduction. Its relation quantifies over every tape cell on both sides of the current head. `KDense215.commutes` is one finite check; another generic relabelling development would duplicate completed work.
- `KZip.scanL` and `scanR` already prove arbitrary-length same-state sweeps. `KRuntimeCore.sstep` uses these for symbolic `.run` segments, but it does not coalesce newly written `.bit` segments and returns `none` on an empty right side. A naive blank-start invocation of that symbolic executor is not a drop-in replacement.

## Independently measured opportunity

`python research215_further_simplification/startup/audit_startup.py` generates an untrusted sweep certificate using an explicit list zipper, then verifies it using a different, absolute-coordinate finite-support tape implementation. The verifier obtains every row from the literal dense table, verifies every read interval against the complete set of ones, checks self-loop legality before accepting a multiple-step sweep, and applies the writes and head displacement.

Result: 95,714 primitive transitions reduce to **39,889** macro operations, of which 3,406 have length greater than one. This removes **55,825 transition dispatches (58.3%)**, not necessarily 58.3% of build time. The sweep family is already mathematically certified by existing source lemmas, but this particular certificate has only been checked by Python.

The independent runs match the exact first published 16,384-step checkpoint and final boot endpoint. Dense state 83 relabels to sparse state 84. Starting from state 0/head 0/all-zero tape gives absolute head **-8**; complete final support has **95 ones**. Relative to that head, the left side is `[true]`, the right side is exactly the published 65-cell blank gap, sentinel, nine boot registers (nextproof 4), then forty spare registers of value 1. The right list has length 208. No one survives outside that support. Five altered-certificate tests (state/read/write/direction/count) are rejected.

## Minimal formal implementation worth trying

1. Represent each side by positive-length homogeneous runs, with zero-valued exterior by definition. Define expansion to the existing complete zipper `Conf`, not to a sampled interval.
2. Add `pushRun` that merges adjacent equal bits; prove its expansion equals prefix concatenation. Ordinary moves split at most one leading run and merge the written cell into the other side. Blank-extension behavior must be proved explicitly, including empty sides.
3. Add a macro operation using existing `scanR` or `scanL`. In the right-head convention a left sweep of `n+1` cells requires the current read cell plus `n` cells on the left; the proposed `sweepLeftFromRight` shows the exact endpoint. Do not confuse the head-inclusive right list with the left list.
4. Prove `advance_sound` against the actual table or certified `fastOf tt215`; then compose with the small `check_sound` lemma in `SweepGlue.lean`. Untrusted hints may specify counts but must never bypass row, read-prefix, or endpoint validation.
5. Check the full resulting configuration against `zc 84 [true] bootRight`. The existing endpoint theorem needs `Reach`, so exact elapsed time is not required by that interface. If retaining a 95,714-step theorem, strengthen scan lemmas to `run M n = some ...` and sum counts; the existing `Reach` lemmas alone do not prove this stronger claim.
6. Benchmark a compiled prototype before deleting any block files. A monolithic checker still may hit kernel recursion/resource limits. Chunk the compressed checker if needed, keeping the generic proof and untrusted data separated.

`SweepGlue.lean` has no `sorry` or new axioms, but it is an uncompiled proposal, and its generic theorem explicitly requires the missing concrete RLE refinement proof. Do not import it as a finished certificate.

## Priority / expected payoff

This is a low-risk secondary build simplification, not the main proof-size win. At the prior report's approximately 111 compiler-seconds for startup versus approximately 4,500 seconds overall, even deleting startup cost entirely saves only about 2.5% of aggregate compiler time. More useful likely is reducing generated checkpoint modules and reusing the sweep lemmas already present. The canonical relabel proof should be left alone unless measurements reveal an actual bottleneck.

## Files and provenance

- `audit_startup.py`: owned generator and independent checker; standard library only.
- `sweep_certificate.json`: untrusted generated data, not a proof.
- `RESULT.json`: measured output, explicit verification scope.
- `SweepGlue.lean`: uncompiled minimal lemma proposal, missing implementation obligations documented.
- `upstream/`: pinned KBoot/KBoot215/KFast215/KDenseBridge/KZip source obtained read-only from GitHub; these files were not executed.

Source links: https://github.com/VladimirReshetnikov/ProveIt/blob/c9dc79323429112c698100f3226a6e4d56c8b782/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KBoot.lean and adjacent files named above.
