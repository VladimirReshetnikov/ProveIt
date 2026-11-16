# Literal PA194 and the exact source controller

`PA194CompressedControllerStep.advance` turns a checked finite root-to-root
execution into a positive literal segment over model-valued data. It
reads the instruction from the same resolved tree as
`PA194SourceControllerCode.step`. Every branch uses the concrete register
oracle. An increment appends one unit spare. A positive decrement increases
the gap by one, and the other branches preserve the gap.

`PA194CompressedSourceFrame.sourceRootCodeCorrect` gives a finite code for
the exact packed root. `PA194CompressedSourceOrbit.synchronize` carries
the clock, gap and spare count as existential witnesses in the Σ₁
induction. The literal state-24 root excludes halting at every earlier
time by persistence. Site 10 executes the three-step literal halt
segment. `PA194CompressedStartup.initialAligned` starts at the literal
blank configuration and reaches site 25 at physical time 58154. The
initial root has width 48, registers `[2,0,0,0,0,0,0,0,0]`, and 26 unit
spares, of which the first is a permanent ordinary slot.

The finite checker uses a balanced tree of transitions. The kernel
verifies equality of its lookup with the decoder of the pinned dense
PA194 literals. `PA194FoldedChecks` checks a fixed source path and actual
resolved instruction at each ordinal. The batching script uses
`decide +kernel` with fuel 512. The aggregate generator combines the
bounded ordinal facts into a theorem that applies at every working site.

`check-compressed-controller.py` replays the source proof modules into a
new output directory. Its receipt records the source and selected direct
imports in the ordered stages file. The helper needs existing staged
imports for the lower machine and arithmetic layers. The full coverage
replay is separate and can reuse `PA194FoldedChecks` once this replay
produces it.

The controller-to-literal theorem uses PRA models whose arithmetic
reduct satisfies IΣ₁. The PC-3674 endpoint is the exact finite source
controller starting from site 25. The correspondence to the modeled
scheduler is a separate mathematical step.

`PA194FoldedAllCoverage.all` supplies the finite coverage for every one of
the 3,673 source ordinals. `PA194NativeControllerCorrectness.endpoint`
identifies truth of the exact `PA194ExplicitEndpoint.haltClassical` with
a model-length run of the source controller reaching PC 3674, starting
from the decoded initial configuration at site 25. Its assumptions are
a PRA model with classical IΣ₁ arithmetic reduct. The theorem has no
finite coverage hypothesis.

Run both checks from the repository root after preparing the ordered
lower stages in `compressed-controller-stages.txt`. The first stage is
a `DiophantineConsistency` namespace view over the retained objects. It
combines the term graph stage with the endpoint arithmetic imports from
the opening substitution stage.

```sh
dir=Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code
core=/dev/shm/pa194-compressed-controller-new
coverage=/dev/shm/pa194-folded-controller-new
ulimit -s 65536
python3 "$dir/check-compressed-controller.py" "$PWD" "$dir" "$core" "$dir/compressed-controller-stages.txt"
{
  printf '%s\n' "$core"
  cat "$dir/compressed-controller-stages.txt"
} > /tmp/pa194-folded-stages.txt
python3 "$dir/check-folded-coverage.py" "$PWD" "$dir" "$coverage" /tmp/pa194-folded-stages.txt 2
```

All batches passed the original Lean kernel checks. The final repository
replay regenerated the aggregate and rebuilt both endpoint wrappers
against those batches, checking their reported axioms. The full source
replay can additionally rebuild all batches in a fresh output.
