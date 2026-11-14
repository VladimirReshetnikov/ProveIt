# PA194 clock and source with startup discharged

`PA194ClockSourceStartup.lean` uses the kernel-checked 58,154-step startup
certificate to discharge the reachability hypothesis in the two standard-model
clock/source equivalences of `../pa194-clock-source`. Their only remaining
explicit hypothesis is the 3,673-site source/compiler `Coverage` certificate.
The startup certificate's generation, full-run receipt, and exact inputs are
documented in `../pa194-startup/`.

The startup theorem has axiom list `[propext]`; the clock equivalences have
`[propext, Classical.choice, Quot.sound]`. This is a theorem in Lean about
standard natural numbers; it does not establish either direction of the
consistency equivalence in PRA or iPRA. The generated source tree's provenance
and trust boundary remain as documented in `../pa194-source-iteration/`.

This composition was checked against locally rebuilt dependency overlays. On
the machine used for the check, after compiling
`PA194ClockSourceConditional.lean` and the startup aggregate into
`/dev/shm/pa194-composition`, the command from the repository root was:

```sh
LEAN_PATH="/dev/shm/pa194-composition:/dev/shm/pa194-startup-preserved:/dev/shm/pa194-compose-probe:/dev/shm/pa195-tree-probe:/dev/shm/pa194bridge-probe/build:/dev/shm:/tmp/current14-standard-fresh-build-20261104/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib:$(lake env printenv LEAN_PATH)" \
  lean -M6000 -j1 Computability/BusyBeaver/Research/PA/pa194-clock-source-startup/PA194ClockSourceStartup.lean
```

The temporary overlays are not distributed build artifacts. A clean combined
rebuild of this composition has not been run; the individual startup
certificate was fully checked as recorded in its receipt.
