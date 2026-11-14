# First marking-entry terminal path

`PA194MarkHalt.firstMarkTerminal` composes the checked first-register marking
run, header controller, and `0,0,1` terminal branch. In every candidate PRA
model, beginning at dense state 113 with left tape half `512*u+1` and right
half `8*r+6` reaches terminal state 194 after 23 physical steps, with halves
`4096*u+9` and `r`. The Lean statement records the exact clock and tape
values using additions and zero-run codes. The model elements `u` and `r` may
be nonstandard.

This theorem assumes the displayed intermediate configuration. It does **not**
prove that blank-tape execution reaches that configuration, that a source
program or a PA refutation produces it, or either consistency direction.

To replay from the repository root:

```sh
TMPDIR=/dev/shm IPRA_LEAN_OVERLAY=/path/to/ipra/lib \
  IPRA_FOUNDATION_OVERLAY=/path/to/foundation/lib \
  bash Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-mark-halt.sh
```

The script rebuilds the marker, header, and terminal-branch prerequisites in
a private temporary directory and rejects `sorryAx` in reported dependencies.

The author completed a fresh full replay with the audited overlays. An
independent suffix replay also recompiled `PA194MarkHalt.lean` in a fresh
overlay against independently rebuilt controller objects, with no `sorryAx`.
