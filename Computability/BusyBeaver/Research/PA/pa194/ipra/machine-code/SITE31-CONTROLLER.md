# Encoded source-controller step at site 31

`PA194SourceSite31Controller.site31Instruction` checks the actual resolved source instruction at site 31 as `.inc 0 (some 32)`. `controllerStep` proves in every PRA model that the primitive-recursive encoded controller takes one step from site 31 to site 32, increases logical register 0 by one, leaves the other eight logical registers unchanged, and preserves the entire independent controller tail. Its replacement suffix argument is arbitrary: positions 9 and 10 of the physical argument vector are not encoded as logical controller registers. The source-state and register-projection definitions in this standalone module are definitionally the same as the existing site-25 bridge definitions.

This is an all-model source-controller theorem. The physical site-31 step has its own replay in `SITE31-ROOT-STEP.md`; the present controller-only theorem does not itself establish their synchronization, a native iPRA sentence, or a consistency implication.

```sh
env -u LEAN_PATH Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-site31-controller.sh "$PWD" \
  Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code /dev/shm/pa194-fetch-coherent-full-v2 \
  /tmp/current14-standard-fresh-build-20261104/lib \
  /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib
```

The checker rebuilds this source in a fresh output directory, pins the source, fetch-closure manifest and three direct controller objects before and after, and audits the four printed theorems for `sorryAx`. It uses the prebuilt source-rebuilt fetch root, its documented `foundation-view`, and the prebuilt general foundations. The manifest and pinned direct objects do not by themselves independently rebuild or authenticate the complete transitive imported-object closure.
