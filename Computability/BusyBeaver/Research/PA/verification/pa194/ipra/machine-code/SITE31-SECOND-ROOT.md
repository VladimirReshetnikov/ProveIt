# Site-31 second physical root pass

`PA194Site31SecondRoot.site31SecondRoot` composes the site-31 first header
pass, the marked path and model-length scan, six physical register-block scans
and rewind, and the site-31-specific unmark and return. It starts and ends at
literal control 24, gives an exact model-valued physical clock, and identifies
the entire output right half. All source-file slots and the full file suffix
are arbitrary model values; no blank-tail premise is imposed. This is the
second root-to-root pass in the site-31 source increment, not the complete
source instruction.

`check-site31-second-root.sh` extends the passed site-31-to-71 source replay
with `PA194Site31SecondTo17`, `PA194Site31SecondReturn`,
`PA194Site31SecondUnmark`, and `PA194Site31SecondRoot`. It rebuilds all of
those modules and the earlier path modules together, checks pinned source and
selected direct object hashes before and after, and rejects `sorryAx` in the
axiom reports. The replay exited 0 (`/tmp/pa194-site31-second-root-replay.log`).
The machine baseline and general foundations remain prebuilt; the selected
pins do not authenticate their complete transitive source closure.

Replay from the repository root:

```sh
Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code/check-site31-second-root.sh "$PWD" \
  /dev/shm/pa194-site27-coherent/build \
  /tmp/current14-standard-fresh-build-20261104/lib \
  /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code
```
