# PA194 clock and source, conditional composition

`PA194ClockSourceConditional.lean` relates halting of each of the two fixed
PA194 clock codes to halting of the extracted source program at site 25. Both
equivalences explicitly assume the 3,673-site compiler coverage certificate
and reachability of the source seed from the blank parent machine. The module
also proves that the two clock codes agree at each standard natural number.

This composes the dense-to-parent quotient, full-tape-to-zipper bridge,
source simulation, and clock interpretation. It is a standard-model Lean
result; it does not prove either implication in PRA/iPRA or establish
consistency equivalence. The source-tree generation boundary is documented in
`../pa194-source-iteration/README.md`.

The source was Lean checked against locally rebuilt dependency overlays; the
printed axiom lists contain `propext`, `Classical.choice`, and `Quot.sound`,
with no `sorryAx`. On the machine used for this check, the command from the
repository root was:

```sh
LEAN_PATH="/dev/shm/pa194-compose-probe:/dev/shm/pa195-tree-probe:/dev/shm/pa194bridge-probe/build:/dev/shm:/tmp/current14-standard-fresh-build-20261104/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib:$(lake env printenv LEAN_PATH)" \
  lean -M6000 -j1 Computability/BusyBeaver/Research/PA/pa194-clock-source/PA194ClockSourceConditional.lean
```

Those temporary paths are not distributed build artifacts. A clean,
self-contained reconstruction of the combined dependency overlays has not
been run for this composition. The neighboring package READMEs describe the
individual dependency checks.
