# Exact MP no-filler rewrite of the frozen 252-state table

This folder is a self-contained diagnostic closure for a source change proved
at the abstract enumerator level in the accompanying `EnumNoFiller254.lean`.
It is **not a new blank-tape consistency machine** and contains no state
improvement claim.

The literal source patch is `Prog254.v` node 6423, right edge 6434 → 6453.
The successful modus-ponens branch copies the conclusion into the top register
without first pushing an extra truth entry. Reusing the old labels of the
replaced decision nodes changes exactly one frozen binary row:

```text
204 1 1 R 113    becomes    204 1 1 R 132
```

All 8,366 guarded instruction cases of the modified source pass the strict
affine checker, conditional on the unchanged four register-box contracts.
The source still has 203 distinct decision pairs. The binary table still has
252 working states and 504 transitions. All 55,471 eligible uniform state
folds were tested against the **modified** source; the search performed
127,407 affine checks and found no survivor. A literal one-million-step
blank run did not reach the sufficient safe root recognized by the harness.
It ended at old state 85, head 686, with 426 one-cells; a fuel cutoff does not
establish eventual behavior.

## Reproduction

From this folder, with standard-library Python 3:

```sh
python3 -B nofiller_frozen_search.py --input-dir inputs --output replay --seconds 600
```

The result should report 8,366 baseline cases, 55,471 fold recipes, 127,407
affine checks, and zero survivors. The time limit applies to the fold loop,
not the preliminary checks. To replay only the changed source and the
bounded blank run:

```sh
python3 -B nofiller_frozen_search.py --input-dir inputs --output quick --skip-folds
```

The `results.json` and `folds.jsonl` supplied here record the original completed
experiment. The driver can also operate against a ProveIt checkout using
`--repo /path/to/ProveIt`; omit `--input-dir` in that mode. Assertions must
remain enabled.

## Provenance and limitations

The ProveIt snapshot is
`85633fd2f57b5dca16f87667699134d1b500ebc0`, whose imported upstream snapshot is
`297ab8df7e5de329605c3875b4934643b371a5e3`. The frozen source and table hashes
are checked by the driver. The original program and machine are attributed
to Mira-Cult, Jeff Ketchersid, and Andrew James Wade; the 253-state reduction
is mira-emmy's public PR 20; the subsequent register permutation and frozen
252-state initializer are ProveIt's. The strict checker is the attributed
closure-kernel source 27. Copied input files are unmodified, except that
their names are shortened for a portable layout. The accompanying license
and upstream attribution files retain their original text.

The search excludes changes to the proved register-box support rows and
their required incoming targets. The finite search is an exhaustive census
of that specific 55,471-recipe family under this checker, not a lower bound
on Turing-machine states. Neither the affine checker nor the bounded
bootstrap run substitutes for a kernel-checked modified binary simulation.
