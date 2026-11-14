# Marker-exit to PA194 controller state 24

`PA194HeaderController.markerTo24` composes the previously checked return
from either marking-exit control (dense 15 or 17) with the next controller
segment. It holds in every candidate PRA model, including nonstandard ones.

The input has state 15 or 17, left tape half `ones(k, 256*u)` and right tape
half `2*t+1`. Here `ones(k,x)` prepends `k` binary one bits to `x`; the factor
`256` supplies eight zero bits before the higher tape tail. The exact output is
dense state 24, left half `512*u+1`, and right half `ones(k,t)`. The source
spells these constants as additions and zero-run codes, and records the exact
clock as the sum of the marker-return and controller-handoff clocks. All of
`k`, `u`, and `t` may be nonstandard model elements. The proof first reaches
state 18, moves left across five zeros to state 23, and scans right across the
zero run through the following one into state 24. The generic state-23 scan
is proved using open induction, not external induction over model lengths.

This is a physical controller segment with the stated tape shape. It does
not establish that every source frame has that shape, reach an increment or
decrement entry, or prove either machine-consistency direction.

Replay from the repository root with the same pinned overlays as the marker
package, for example:

```sh
TMPDIR=/dev/shm IPRA_LEAN_OVERLAY=/path/to/ipra/lib \
  IPRA_FOUNDATION_OVERLAY=/path/to/foundation/lib \
  bash Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-header-controller.sh
```

The script rebuilds the prerequisite table and model proofs in a private
temporary directory, checks the new modules, and rejects `sorryAx` in their
reported dependencies.

An independent suffix replay rebuilt the new controller modules in order in a
fresh temporary overlay, reusing the preserved marker prerequisites. The
printed dependencies had no `sorryAx`. The nested replay command above also rebuilds the
prerequisite chain; both the author run and an independent fresh Linux replay
passed using the audited overlays.
