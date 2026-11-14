# PA194 packed-run concatenation in arbitrary PRA models

`PA194StepperCompose.lean` proves that the explicit packed iterator run for
`s+t` steps equals the run for `t` steps from the state reached after `s`
steps. It uses a quantifier-free induction instance of the candidate classical
PRA, and holds for all model times and starting codes, including nonstandard
ones. `PRA_proves_composeSentence` packages the equality as a closed
first-order sentence and proves it in the candidate classical PRA by
completeness over equality models. This supplies the segment-concatenation
algebra needed for later source and physical runtime refinement; it does not
prove that refinement or either consistency implication.

Replay with the same dependency overlays:

```sh
IPRA_LEAN_OVERLAY=/tmp/current14-standard-fresh-build-20261104/lib \
IPRA_FOUNDATION_OVERLAY=/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  bash Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-compose.sh
```

The checker rebuilds the pinned machine and dependency chain privately and
rejects `sorryAx`. It assumes the transitive prebuilt overlay objects match
their recorded sources rather than rebuilding all of them.
