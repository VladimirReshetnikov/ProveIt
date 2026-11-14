# PA194 clock and source halting

`PA194ClockSourceComplete.lean` proves, without additional hypotheses, that
each of the two fixed PA194 clock codes reaches 1 at a standard natural time
if and only if the pinned formal source program halts from site 25 with
register 0 equal to 2 and all eight other registers equal to 0. The proof
composes the complete 3,673-site coverage certificate with the independently
checked blank-tape startup and the standard-model clock/parent/source bridge.
`PA194ClockCanonical.lean` expresses the verified initial store explicitly.

Both final theorems print the axiom list `[propext, Classical.choice,
Quot.sound]`. This is a standard-natural-number Lean theorem. It does not
establish the internal PA/PRA/iPRA machine reductions or an equivalence to
Con(PA). The construction still relies on the pinned Python translation of
the archive grammar into the formal source tree, described in
`../pa194-source-tree/README.md`.

The full fresh coverage and startup runs are documented in the neighboring
`pa194-coverage/verification.json` and `pa194-startup/verification.json`.
The final composition was checked against independently rebuilt downstream
modules, the preserved startup objects, and the complete coverage objects.
After the full coverage run, its aggregate was independently recompiled from
819 hash-verified preserved files, including all 368 batch objects. On the
machine used for the checks, the final command from the repository root was:

```sh
LEAN_PATH="/dev/shm/pa194-compose-fresh:/dev/shm/pa194-coverage-preserved:/dev/shm/pa194-composition:/dev/shm/pa194-startup-preserved:/dev/shm/pa194-compose-probe:/dev/shm/pa195-tree-probe:/dev/shm/pa194bridge-probe/build:/dev/shm:/tmp/current14-standard-fresh-build-20261104/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib:$(lake env printenv LEAN_PATH)" \
  lean -M6000 -j1 Computability/BusyBeaver/Research/PA/pa194-clock-source-complete/PA194ClockSourceComplete.lean
```

Those temporary overlays are not distributed build artifacts. A single clean
combined rebuild script for every dependency and both long certificates has
not yet been provided. The full checks and their independent aggregate replays
are stated separately rather than claiming such a rebuild.

A combined fresh build is now provided. Supply the matching freshly built
project and Foundation object overlays used by the iPRA checks, then run:

```sh
IPRA_LEAN_OVERLAY=/path/to/project/objects \
IPRA_FOUNDATION_OVERLAY=/path/to/foundation/objects \
  Computability/BusyBeaver/Research/PA/pa194-clock-source-complete/check.sh
```

It retains each component in a private tmpfs directory until assembly,
compares duplicate object files byte for byte, and rejects collisions. It
prints the repository revision, Lean version, source-builder and archive
hashes, and theorem axioms. `--preflight` checks wrapper construction and
Lean version without rebuilding proofs. Expect about 55–70 minutes or more on
the machine used for the receipts, mainly for the full coverage and startup
runs. The component wrappers, collision check, and final assembly have been
tested, but this new complete fresh script has not yet been run end to end.
The previous checks and receipts remain the evidence for the theorem.
