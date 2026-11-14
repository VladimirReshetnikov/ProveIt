# First physical value five: marker return to dense 84

`PA194FirstFiveTo84.markerFirstFiveTo84` follows the genuine non-first marker
entry with first physical value five through the k=1 controller and the
zero-residual state-42 branch to dense 84. It preserves the exact packed tape
halves and model clock, for all eight non-first marker positions and every
selected value, in every candidate PRA model. The stated marker delimiter and
controller shape are hypotheses; no blank suffix is required. Model-valued
data and clocks may be nonstandard.

`PA194FirstFiveSuccCore.returnedOddHalf` proves that for the seven marker
positions at least two, the returned file has the physical form
`2*(2*q+1)` for some model value `q`. This supplies the two-zero prefix and
following one needed by the existing dense-84 scanner. The first non-first
position has a different, data-dependent returned-file prefix and is not
covered by that lemma. The file-prefix lemma does not itself compose the
scanner.

These are conditional executions from a specified intermediate marker
configuration. They do not establish blank-tape reachability, identify dense
84 with a source frame, simulate a source instruction, or prove either iPRA
consistency implication. First physical values below five remain separate.

The two modules passed an author suffix rebuild against previously checked
prerequisite overlays, with `propext`, `Classical.choice`, and `Quot.sound`
as their reported axioms and no `sorryAx`. The full nested checker
`check-first-five-to84.sh` is supplied but has not been run.

An independent ordered suffix replay rebuilt the first-five marker and
scanner modules against separately checked controller objects and retained
deeper prerequisites. It passed without `sorryAx`; this was not a full nested
replay.
