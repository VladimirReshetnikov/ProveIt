# Site-31 physical path to the site-32 header

`PA194Site31RootTo32.rootTo32` is a model-uniform literal-machine run from the site-31 header to physical control 24 at the actual site-32 program path. Its starting numeric frame is the same as `PA194Site31To2.site31To2`, and its output is `modelWord (path 32) (z + z)`, where `z` and the full output-file value are explicitly defined from the model inputs. The clock is the checked first-three-header-pass clock followed by the explicit nested `runAfter` clocks; it is not an existential witness.

The starting register values, gap `k`, and repeated-spare count `count` range over arbitrary elements of any model of PRA. The required physical suffix is `repeatOutput(count, 0)`: a model-valued sequence of one-valued spares followed by blank tape. This is the same suffix discipline used by the established physical orbit. The output file is still represented by its exact `returnCode` expression; the separate arithmetic identification with the source file updated at logical register 0 is not part of this replay.

`PA194Path32Header.path32` kernel-checks the actual program path `[true,false,false,false,true,true,true,false]`; `path32Word` provides its exact packed-word identity. `PA194Site31ReturnHeader.headerTo24` checks the site-specific control-7 header return. `PA194Site31AfterSelectedTo32.afterSelectedTo32` composes the selected increment, return over the six preceding blocks and gap, and final header return. `PA194Site31AfterRun.runAfter` abstracts those exact nested physical steps as a model-level function, and `rootTo32` composes them with the literal machine's first three site-31 header passes. No native-iPRA sentence or consistency implication is claimed here.

The staged replay extends `check-site31-increment-return.sh` with the actual site-32 path, two source-built existing header modules, the site-31 return module, and the two compositions. Use:

```sh
env -u LEAN_PATH Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-site31-root-to32.sh \
  "$PWD" /dev/shm/pa194-site27-coherent/build \
  /tmp/current14-standard-fresh-build-20261104/lib \
  /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code \
  /dev/shm/pa194-site28-work/build-one-spare-file-roundtrip \
  /dev/shm/pa194-site28-work/build-carry-roundtrip
```

The checker pins the listed sources and direct inputs, rejects different overlapping machine objects, verifies input hashes before and after the run, and rejects `sorryAx` in the axiom audits. It rebuilds the stated staged source modules; the machine baseline, two tail stages, and general foundation roots are prebuilt, and the full transitive imported-object closure is not rebuilt or independently certified by this checker.
