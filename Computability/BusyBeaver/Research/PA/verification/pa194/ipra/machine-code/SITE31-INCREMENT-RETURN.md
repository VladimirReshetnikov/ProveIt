# Site 31: selected-register increment and return toward the header

This increment continues the pinned 194-state literal machine's physical run from the site-31 source root, in every model of PRA. It builds on the independently checked two-pass header prefix. The work does not prove a consistency implication or a complete source-instruction simulation.

`PA194Site31To2.site31To2` composes the first two site-31 header passes and a third 15-step dispatch. It reaches physical control 2 with an exact primitive-recursive clock. All register values and the complete numeric file suffix are arbitrary.

`PA194Site31ToSelected.site31ToSelected` continues to control 1 by scanning the model-valued header gap, six preceding physical registers, the marked logical-register-0 block and three subsequent physical registers. The complete suffix is still arbitrary and unchanged at this endpoint. Its two nested clocks are explicit.

`PA194Site31DynamicIncrement.increment` proves the marked-register increment with the following three physical file blocks and a model-valued count `n` of one-valued trailing spare blocks followed by blank tape. Its output explicitly contains `block (e 0 + 1) rest`, where `rest` is the exact return-code expression for the three unchanged following blocks and `repeatOutput n six`; the existing open-induction `modelOutputShift` identifies that last expression as one additional spare. All input values and `n` are arbitrary model elements.

`PA194Site31IncrementSelected.incrementSelected` adds the six-block prefix scan. `PA194Site31ReturnPrefix.returnPrefix` proves the exact return across that prefix and the model-valued header gap. `PA194Site31IncrementReturn.incrementReturn` composes the two: it begins at the third-pass control-2 layout and reaches control 7 at the header with a named right-tape expression, a model-valued spare-count condition, and all component clocks explicit. These theorems do not yet identify the resulting tape with the site-32 source frame; the control-7-to-control-24 return and source-frame/output-file identification are separate obligations.

The selected-checkpoint result and the increment-return result have a common control-2 layout, but `PA194Site31IncrementReturn.incrementReturn` itself starts there; this stage does not state one theorem from the site-31 root through the whole increment.

## Replay

```sh
env -u LEAN_PATH Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code/check-site31-increment-return.sh \
  "$PWD" /dev/shm/pa194-site27-coherent/build \
  /tmp/current14-standard-fresh-build-20261104/lib \
  /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code \
  /dev/shm/pa194-site28-work/build-one-spare-file-roundtrip \
  /dev/shm/pa194-site28-work/build-carry-roundtrip
```

The script builds the 14 site-31 second-root prerequisites and twelve additional modules in a fresh output directory. Two existing source modules, `PA194IncrementFront` and `PA194Site28IncrementWrite`, are read and pinned from the repository. The other added sources are supplied by the SOURCE directory. The checker pins the listed sources, baseline manifest, selected direct machine objects, and the direct tail-stage objects; it rejects byte differences among overlapping machine `.olean` names across the three machine roots. It records a before-and-after input hash check and rejects `sorryAx` in the printed audits.

The machine baseline, the two selected tail roots, and both general foundation roots remain prebuilt. The hashes and overlap check do not rebuild or certify every transitive imported object; this is a staged replay, not a fresh full dependency-closure audit.
