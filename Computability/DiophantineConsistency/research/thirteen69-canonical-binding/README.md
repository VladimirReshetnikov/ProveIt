# Canonical expression for the thirteen-coordinate carrier

[`Thirteen69Canonical.lean`](Thirteen69Canonical.lean) defines an integer
expression whose four ports and thirteen variables are symbolic. It proves in
Lean, for every commutative ring `R`, that evaluating this expression equals
`ThirteenCarrier.value69` at the same four ports and thirteen coordinates.
For an ordered natural-like semiring and its difference ring it also proves
that `InternalZero` of this expression is equivalent to that carrier value
being zero. A further theorem applies `positiveShift`, and `current_zero`
instantiates exactly `CurrentWindowCarry2011.ports`, including its existing
source-mask shift.

**This is not yet a binding to the separately recorded 69-operation JSON
DAG.** The expression is arranged to match the carrier definition and uses
powers and repeated subexpressions; this packet does not count its gates or
prove inside Lean that it evaluates to the exact graph at
[`polynomial69.json`](../thirteen-variable-independent/polynomial69.json).
The JSON graph is bound to a different phase-split2471 four-port tuple. The
2011-port expression is a different candidate; no equality of those fixed
numerals or independent calibration of the phase-split tuple is asserted.
A direct 69-row cut-point comparison and the all-model converse are separate
open work. The theorem does not prove the 69-operation equation equivalent to
consistency, nor does it construct a derivation in iPRA.

## Paired bounded replay

[`replay.py`](replay.py) rebuilds `ShortEquation`, `ThirteenCarrier` and this
expression theorem independently on each side of the separately audited
[70-source coherent provider](../../reviews/ordinary12-coexistence-pair-independent-audit/README.md).
These two additional project modules are rebuilt from pinned workspace source;
no historical project object is substituted. The script checks the parent
pair before and after, each source and direct import, compiler exits, matching
objects and all four axiom reports. The observed wrapper session `81960`
actually exited `0`; its [terminal observation](terminal-observation.json)
records the output and the [receipt](replay-receipt.json) records six compiler
and six dependency-check exits. The reports are `[propext]` for arbitrary
ring evaluation and `[propext, Classical.choice, Quot.sound]` for each model
and shifted statement, with no `sorryAx` or warning. These are Lean metatheory
axioms, not added object-theory iPRA axioms.

Run a fresh replay where the pinned parent and provider still exist:

```
python3 -I -S replay.py --output /tmp/ipra-thirteen69-canonical-pair-NEW
```

The current evidence has not yet received an independent suffix audit. The
70-source parent inherits the original Foundation wrapper's unobserved outer
exit and package-transitive and dynamic-loading qualifications. Source and
provider checks are point-in-time checks, not protection from mutation
between observations. The [failed exact-row expansion attempts](observations/failed-attempts.md)
are preserved separately; neither is promoted to a completed proof.
