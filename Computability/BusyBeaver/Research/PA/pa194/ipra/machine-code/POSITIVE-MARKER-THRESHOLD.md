# State-35 one-run branches and marker return

`PA194PositiveThreshold.classifyLength` proves in every candidate PRA model
that the remaining one-run length is 0, 1, 2, 3, 4, or `n+5` for some model
element `n`. The five `shortTraverse` theorems give the exact run through the
corresponding controls 35, 47, 67, 33, and 43. `shortBoundary` gives the next
state on a following zero: respectively 46, 36, 86, 42, and 61. These are
physical steps; the later behavior of those five branches remains to be proved.

`modelRunAtLeastFive` covers the remaining case uniformly: it consumes five
ones, rewrites the fourth and fifth to zeros, and reaches state 15 after six
steps, retaining an arbitrary residual one-run of length `n`. This includes
nonstandard `n`. The theorem gives both tape halves exactly.

`thresholdReturn` composes that branch with the existing marker-return theorem.
When the state-35 left half has the displayed `4*x+1` shape, the machine reaches
state 17 after eleven steps; both halves are explicit. The state-35 left half
in the checked `k=1` non-first marker segment has that form. This is a physical
controller return, not yet a proved source-instruction simulation or a PA
consistency implication.

To replay from the repository root:

```sh
TMPDIR=/dev/shm IPRA_LEAN_OVERLAY=/path/to/ipra/lib \
  IPRA_FOUNDATION_OVERLAY=/path/to/foundation/lib \
  bash Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-positive-threshold.sh
```

The script rebuilds the earlier marking, header and dispatch packages in a
private temporary directory before checking the two threshold modules, and
rejects `sorryAx` in the reported dependencies.

An independent suffix replay rebuilt both threshold modules in a fresh tmpfs
overlay against separately checked controller and dispatch objects; the
reported theorems have no `sorryAx` dependencies. The full author nested replay
also passed with the audited overlays.
