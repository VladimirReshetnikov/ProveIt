# Continued execution of two 251-state mutations

These experiments leave the checked 252-state solution unchanged. Both mutants
run for 100 million literal binary moves from blank without halting, but no
nonhalting theorem or consistency calibration has been proved. The useful new
observation is that continued mutant execution can retain data in different
fields and spares; the original program's residual equations do not describe
that execution.

The [preceding phase-entry analysis](../README.md) selects three recipes from
the existing complete one-incoming-action ledger. This follow-up examines its
two variants that return from the prepared continuation. Starting with the attributed
[permutation252 table](../../candidate-permutation252/README.md), both delete
old state204 and replace its sole incoming row `(172,1)`:

| Name | Replacement | SHA256 of reconstructed table |
|---|---|---|
| R252 | write1, right, target252 | `d12e4b5247b9e1d2aca883bd9b249402f28db71747de48e34b2ef57b3524e94a` |
| L229 | write1, left, target229 | `09dc2f1c3c14603c1b0206c6a8a045f31099690259da622796872107b9473346` |

Each has 251 working states and 502 rows, with old start64, dispatch96 and
halt254. The pinned baseline SHA256 is
`939f99d602c8f7057517c4369279de99e30827050fc743581df83f26aaf1b713`.
The program, backend, table and preceding analyses retain their attribution to
Mira-Cult, Jeff, Wade, mira-emmy and the contributors named in the linked notes.

## The exact original source imposes a stronger invariant

Case8390 is the final unfolded `CC2` of loop205/206 in the successful MP
`ifeq_par1` restoration. See
[`Dag254.lean`](../../../../Lean/BusyBeaver/ZFC/Dag254.lean),
[`L2Control254.lean`](../../../../Lean/BusyBeaver/ZFC/L2Control254.lean),
[`L2Macros254.lean`](../../../../Lean/BusyBeaver/ZFC/L2Macros254.lean) and
[`L2Lib254.lean`](../../../../Lean/BusyBeaver/ZFC/L2Lib254.lean).
The preceding loop198 copies the original parameter into TW and scratch1,
then loop205 restores parameter1. At this occurrence, writing
`TW=t`, `p1=n`, `s1=k`, the original source satisfies `t=n+k` and `n>0`.
This is source reasoning, not a new Lean theorem or a mutant invariant.
Earlier `t=0,n>0` controls satisfy coarse masks but are unreachable in this
exact original source context.

The restricted original-residual obstruction survives this refinement.
For `t=b`, `1≤n≤b`, `k=b−n`, the original expected residual has
`F=(b,b,0)` while the other original residual has `G=(b+n,b,0)`.
There are unboundedly many distinct G values over one F value, so a fixed
finite label cannot recover them uniformly. An unbounded spare register, or a
different global representation, falls outside that obstruction.

## Actual continued execution preserves more information

`prepared.py` follows R252 from a complete prepared tape, with PC
`1111111111`, gap40, spares `[0,1,0]` and logical registers
`[0,t,0,0,n,0,k,0,0]`. The following controls also satisfy `t=n+k`:

| t,n,k | Moves to next PC000 frame | Final TW,WS,p1 | First spare |
|---|---:|---|---:|
| 1,1,0 | 30,352 | 0,4,2 | 0 |
| 2,1,1 | 30,614 | 0,4,3 | 1 |
| 2,2,0 | 50,314 | 0,8,3 | 0 |
| 5,3,2 | 79,488 | 0,13,6 | 2 |

Every saved clean frame checks the entire finite tape support, including the
left exterior and all spare blocks, by a whole-tape repaint. These samples
fit `TW=0`, `WS=P(1,n)`, `p1=t+1`, `spare0=k`, where P is the actual literal
Cantor pairing. The value13 at n=3 rules out the tempting formula `WS=4n`.
The data can be recovered as `p1−1`, `unP(WS).2`, and spare0. Thus numeric1
could be a storage tag in a changed representation. Other live fields were
fixed to zero, and neither this general transformer nor blank reachability
has been proved.

## Startup is the unresolved part

The changed row first fires at move3,507, before the certified baseline boot
ends at82,552. Both 100-million-move runs use it28 times and finish with5,512
one-cells. R252 ends in old state95 at head660; L229 in state95 at head604.
These are fuel cutoffs.

The relaxed scanner accepts only an actual state96 root PC, the sole left
marker at head−1, and a complete parse of all right-hand one-cells into nine
primary registers and all spares. It allows gaps below40. An independent
Python replay checks every accepted frame through100,000 moves by repainting
the entire tape.

| Table | Move | Head/header/gap | Logical primary registers |
|---|---:|---|---|
| baseline and R252 | 4,610 | 4/18/14 | 0,0,3,0,0,0,0,1,0 |
| L229 | 4,636 | 4/18/14 | 0,0,3,0,0,0,0,1,0 |
| baseline | 71,091 | 3/22/19 | 0,0,18,2,0,0,0,0,1 |
| R252 | 15,963 | 3/22/19 | 0,0,3,2,0,0,2,0,1 |
| L229 | 16,019 | 3/22/19 | 0,0,3,2,0,0,2,0,1 |
| baseline | 82,552 | 2/42/40 | all zero |

The first mutant frame is an ordinary baseline bootstrap intermediate. Neither
mutant's second frame satisfies the prepared alternate format: both have
`p1=0, WS=3` and dirty scratch fields. No third complete root frame appears
through100 million moves. Of34,195 dispatch visits per mutant,34,188 fail the
root-PC/header check, five fail complete register-file parsing, and two pass;
none fails the left-marker check.

The literal source has6,460 leaves and maximum consumed path length34,
attained at30 leaves. The maintained controller theorem uses gap40. This
does not establish that gap34 suffices, or that the observed gaps14/19 are
safe for subsequent commands.

A viable changed-calculus argument must supply a stable whole-tape format
covering actual startup, derive root-command behavior in that format, and
prove its refutation search equivalent to a ZFC-strength theory. The freedom
to choose an artificial theory remains useful, but these obligations remain.

The [controlled startup follow-up](conditional-transport.md) sharpens this
target: the actual second root's logical registers already satisfy the existing
theorem invariant, so a binary transport to the original register program would
suffice. The original and mutated tables have identical next-million-move
prefixes from that frame, with no further changed-row encounter. The required
unbounded short-gap binary comparison is still open.

## Reproduction and provenance

The [full-run record](../../results/phase-entry-continuation-verification.json)
preserves completed scratch evidence, explicitly marked as migrated rather
than a new portable 100-million-move rerun. The
[publication replay](../../results/phase-entry-continuation-quick-verification.json)
freshly checks the exact maintained files in quick mode. Both record all five
source hashes. The driver reconstructs the two tables from the pinned baseline,
compiles the literal C++ simulators, runs prepared controls, scans root frames,
and compares Python and C++ whole tapes at an exact common move count.

```sh
python -B Computability/BusyBeaver/Research/ZFC/phase-entry/continuation/reproduce.py --repo /path/to/Proofs --output /outside/continuation --quick
```

Omit `--quick` to run100 million moves per blank control. Quick mode uses
100,000 moves and does not reproduce the longer cutoff. Python and a C++20
compiler are required; no dependencies are fetched and no Coq is built.
The original `Prog254.v` is parsed as pinned source data.
The literal simulator emits one indentation warning in checkpoint formatting;
its unconditional snapshot call and conditional comma emission were reviewed.

An earlier diagnostic labeled1 million moves actually performed1,000,001.
The full-run record preserves this correction: exact R252 at1 million is
state6/head0; at1,000,001 it is state9/head−1 with the same one-cells. The final
independent Python/C++ comparison uses exactly1 million moves and supersedes
the earlier report. Prepared-control counts were unaffected.
