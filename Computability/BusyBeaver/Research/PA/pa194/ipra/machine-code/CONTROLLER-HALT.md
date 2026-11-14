# PA194 controller terminal branch

`PA194ControllerHalt.threeSteps` checks the literal transition sequence from
dense state 24 through states 25 and 27 to terminal state 194. Its right tape
has low bits `0,0,1`; all higher bits and the left half may be arbitrary
model elements. The theorem gives the exact output halves after three steps.

`PA194ControllerHalt.markerTerminal` composes that branch with the checked
marker-exit-to-state-24 segment. For either marker-exit control 15 or 17, a
configuration with left half `256*u` and right half `16*r+9` reaches control
194 in 20 physical steps, with left half `4096*u+9` and right half `r`. The
source states these numerals through additions and zero-run codes and includes
the exact clock. The theorems hold in every candidate PRA model, including
nonstandard values of `u` and `r`.

These are conditional facts about an intermediate tape shape. They do **not**
show that the machine reaches this configuration from a blank tape, identify
it with a source-program state or a PA refutation, or prove either consistency
direction.

Replay from the repository root using the same pinned overlays as the marker
package:

```sh
TMPDIR=/dev/shm IPRA_LEAN_OVERLAY=/path/to/ipra/lib \
  IPRA_FOUNDATION_OVERLAY=/path/to/foundation/lib \
  bash Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-controller-halt.sh
```

The script freshly rebuilds the header-controller prerequisites and these two
modules in a private temporary directory, rejecting any `sorryAx` dependency
in the reported theorems.

An independent suffix replay rebuilt the new controller modules in order in a
fresh temporary overlay, reusing the preserved marker prerequisites. The
printed dependencies had no `sorryAx`. The nested replay command above also rebuilds the
prerequisite chain; its full run is in progress.
