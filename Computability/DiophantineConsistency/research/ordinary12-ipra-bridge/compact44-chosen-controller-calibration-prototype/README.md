# Controller calibration at the chosen compact dimensions

On the same author-side symbolic controller provider,
`CompactChosenControllerCalibration.chosen_bounds` proves the two numerical
controller hypotheses for every model element `T`, taking

```
w = 581197^(T+1)
H = 581197^(T+3)
N = w*H = 581197^((2*T+3)+1).
```

`chosen_calibration` then specializes the preceding symbolic-K controller
theorem with `m=2*T+3` and `e=T+1`. For every model `T,R0`, without any
additional size premise, it gives a model-definable Boolean selector whose
selected positions and translates by `1` and `w` are in range, and whose
controller sum has the stated calibration congruence. The choice of powers
matches the earlier halt-to-compact-word dimensions, but this file neither
imports nor constructs that word and does not assume that a run halts.

The bounded incremental Lean compile actually exited 0 in 3.007 seconds,
without warnings or `sorryAx`. Both theorem axiom reports list `propext`,
`Classical.choice`, and `Quot.sound`. The source is byte-for-byte the checked
input; the words “bounded attempt” in its opening comment are historical.
Command, dependency listing, direct preceding object hashes, source and log
hashes, and terminal observation are retained in `observations/`. The source
reuses the `CompactHaltDimensions.controller_bounds` proof at these same
constants, plus the earlier width-times-height power identity, rebuilt against
the current symbolic controller provider.

This is a single-author incremental build, not a paired replay or a freshly
authenticated project/package closure; inherited controller-data and
controller-choice linter warnings, transitive dependencies, dynamic ancestry,
and between-check limitations remain. Range bounds for the abstract selector
do **not** prove physical dummy safety, rank variation, a joined packed word,
retained-byte or display binding, a positive graph zero, or an iPRA proof.
