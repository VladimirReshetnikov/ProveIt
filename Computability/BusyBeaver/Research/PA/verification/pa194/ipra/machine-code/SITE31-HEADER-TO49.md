# Physical site-31 header to control 49

`PA194Site31HeaderDispatch.sevenSteps` follows the seven bits of the actual
source-site-31 path through seven literal physical transitions, from control
24 to control 108, for any PRA model, any left half, and any remaining right
tail. `PA194Site31HeaderTo49.to49` starts from the actual path-31 prefix
followed by a zero bit and an arbitrary remaining right tail, and executes ten
literal transitions to control 49 with the exact left and right halves shown
in the theorem. It does not assume the spare suffix is blank. The time is the
sum of the model numerals 7 and 3. This is a physical header prefix, not yet
the complete site-31 increment or its source/physical simulation.

The staged replay rebuilds `PA194Path31Header`, `PA194Site31HeaderDispatch`,
and `PA194Site31HeaderTo49` in one temporary output, verifies selected
prebuilt direct object hashes and source hashes before and after the build,
and rejects `sorryAx` in the axiom audits. It passed with exit 0 in
`/tmp/pa194-site31-header-to49-replay.log`. The site-27 machine baseline and
the general project and package foundations are prebuilt; the selected hash
checks do not authenticate their complete transitive source closure.

From the repository root, replay with:

```sh
Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code/check-site31-header-to49.sh "$PWD" \
  /dev/shm/pa194-site27-coherent/build \
  /tmp/current14-standard-fresh-build-20261104/lib \
  /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code
```
