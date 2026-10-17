# Mixed-row fusions in the faster253 variant

This bounded search found no accepted 252-state table. It tested 1,338
recipes on source27's faster253 variant, preserving the full original
frontend and every conservative register-box row. All recipes failed an
affected strict affine instruction check. Fuel exhaustion and unsupported
symbolic rules remain unresolved; this is no minimality result.

The input is the four-row reassociation delivered in source27, archived by
commit `da6dabcd8976acf94c4f3652ed3eeae5713b3d2a`. Its frozen table is
`SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/27-variant-machines-faster_253.tm`,
SHA256 `d5b7a357dbf4dd9d18c8e1aa04dc0c3c0e1b8f349853b7558d1a096a15684412`.
It descends from mira-emmy's public253 PR20 head
`0d544f2a2e3c18f12278441a74b7879f31cbe856`, Mira-Cult's machine, Jeff's
verification, and Andrew James Wade's framework. The driver reuses source27's
attributed strict affine checker and source04/source09 helpers from fresh
scratch copies. It does not modify those delivered sources.

Relative to public253, only the target fields of these compact rows change:

```text
37/read0 -> 42     37/read1 -> 48
42/read0 -> 41     42/read1 -> 50
```

Their write bits and rightward moves remain unchanged. Compact start0 maps
to old5, compact33 to old96, and halt253 to old254. The candidate map names
the three reassociated states 255, 256 and257, replacing old12,128 and110;
these names do not denote extra working states. Their literal rows are:

```text
255/read0 = 0 R 148     255/read1 = 1 R 17
256/read0 = 0 R 255     256/read1 = 1 R 18
257/read0 = 0 R 33      257/read1 = 1 R 256
 96/read0 = 0 R 257
```

The baseline is reconstructed from source27's rotated203-node decoder DAG
(rotation option0, node7, `associate_left`), and every emitted table row is
compared with the frozen table. Runtime cases use that rotated DAG's paths,
which differ from original `Prog254` paths. All8,391 strict affine cases
pass with at least13 literal rules per case. A separate literal binary run
reaches exactly old96, head−17 and the complete published bootstrap tape
after312,935 steps. All178 one positions, all158 spare blocks including the
two nonzero spares, and the blank exterior are compared. No first-arrival
claim is made. Exact transition bisimulation has253 singleton working
classes; it supplies no direct quotient reduction.

The three new labels are the only deletion sources. Both read rows of every
one are used in the finite blank bootstrap. Their affected baseline runtime
case counts are9,10 and13 respectively, so a branch cannot be discarded as
unused merely from these observations.

For deletion source p in {255,256,257}, the principal family retains a
different label q outside the28 conservative box states and old5/96. It
redirects every target p to q, deletes p's two rows, and chooses exactly one
of q's rows from p while retaining q's other row. Each source has222 such
destinations and two row masks, giving1,332 mixed recipes. All candidates
have252 working labels,504 total rows, the original old5 blank start, and
separate halt254. All55 protected box pairs and both old5 rows remain literal.

Source27 already tested uniform folds on this rotated baseline. A both-row
copy usually coincides with an inverse uniform fold up to renaming. There
are six protection exceptions: retaining q=7 or9 and copying both rows from
p leaves all55 protected pairs literal, whereas the inverse recipe that
deletes7 or9 would change a protected incoming target and was filtered by
the prior search. Those six frontier recipes are included here. Uniform
mask0 recipes and the remaining inverse uniform copies are omitted as
previously searched. This family also differs from the earlier nonuniform
old107 incoming-edge experiment on the original public253 baseline.

The baseline observer records every literal table lookup, including scan
tests. A recipe first checks the baseline cases touching any changed or
deleted row, in deterministic order. The unchanged55 box rows justify
retaining the published box summaries. Any survivor would receive all8,391
cases again, followed by a literal blank run limited to400,000 steps that
requires the same complete bootstrap frame and permits a changed arrival
time. No recipe reached either later stage.

| First rejection | Recipes |
| --- | ---: |
| Affine fuel exhausted at1,000 rules | 552 |
| Unsupported symbolic rule | 779 |
| Unexpected halt in a nonhalting instruction | 7 |
| Accepted by all affine cases | 0 |

The final replay executed3,330 candidate-case checks. Of the mixed recipes,
1,330 alter two retained rows and two alter only one row. The two single-row
cases delete255 into256 with mask1 (unsupported marked-box operation), and
delete256 into257 with mask2 (fuel exhausted), both at the `CC` path010111.
The six frontier recipes alter three rows each and also fail affected
checks. No candidate blank bootstrap was run.

Each of the seven unexpected halts is additionally reproduced using literal
binary transitions on a small prepared dispatch frame: gap budget40, marker
at−1, header at40, the recorded PC, ten zero-valued physical register blocks,
and a blank exterior. The unchanged baseline reaches the exact intended
instruction endpoint on each identical input. The modified table halts
before any exact intended endpoint:

| Deleted p | Retained q | Mask | Case | Candidate halt steps |
| ---: | ---: | ---: | ---: | ---: |
| 255 | 62 | 2 | 7 | 5 |
| 255 | 77 | 1 | 11 | 4 |
| 256 | 62 | 2 | 11 | 4 |
| 257 | 32 | 1 | 11 | 371 |
| 257 | 46 | 1 | 11 | 4 |
| 257 | 62 | 2 | 2 | 3 |
| 257 | 77 | 1 | 11 | 2 |

These are finite instruction-contract counterexamples. They do not show
that any modified blank-start machine halts. The other1,331 rejections are
bounded checker failures and do not prove semantic inequivalence.

Replay from the repository root:

```sh
python3 -B Computability/BusyBeaver/Research/ZFC/variant253_search.py \
  --output /tmp/variant253-search.json
```

`--baseline-only` stops after the baseline checks. The driver rejects
optimized Python because assertions perform its functional checks. The
default run takes about five seconds on the intake host. The permanent
`results/variant253-search.json` records every recipe, first failure,
prepared-frame witness, bounds, full target tape, source pins and scratch
path. No network fetch, checksum manifest, Lean or Coq build is used.

Independent reads of the driver found the recipe family, affected-case
screen, full-survivor recheck, protected rows and complete-frame bootstrap
scope correct. A separate root replay then reproduced every functional
field of the saved JSON, including all seven literal witnesses; only the
scratch path, timestamp and elapsed time were excluded from comparison.
`results/variant253-root-replay.json` records this independent check.
This diagnostic adds no consistency calibration, binary/register
simulation, internal arithmetic endpoint or sub254 machine claim.
