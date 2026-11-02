# Thirteen-variable 69-row model binding

[`Thirteen69Nodes.lean`](Thirteen69Nodes.lean) defines the 69 arithmetic
nodes as individual polymorphic expressions. Each node has a Lean theorem
showing that evaluating its `Expr` form agrees with its scalar form.
[`Thirteen69Cuts.lean`](Thirteen69Cuts.lean) then proves, using small
cut-point ring identities, that the output equals
`ThirteenCarrier.value69` over **every commutative ring**. It composes this
with `internalZero_iff` and `positiveShift`, and its `current_zero` theorem
instantiates the full `CurrentWindowCarry2011.ports` tuple. In an ordered
natural-like semiring and its difference ring, the shifted syntax has an
internal zero exactly when the carrier value at the corresponding positive
coordinates is zero. The binding is model-level, not an object-theory proof.

[`check_rows.py`](check_rows.py) independently reads the pinned
[`polynomial69.json`](../thirteen-variable-independent/polynomial69.json)
and compares every one of its 69 ordered binary rows to the node definitions,
including all thirteen variable indices, all four port slots and the output.
It verifies the `39` multiplication, `16` addition and `14` subtraction
histogram, rejects four mutations, and checks the exact 2011-port shifted
literal declaration. Its comparison is an **external source check**, not a
Lean parser or theorem about JSON. It does not bind a PDF or count any decimal
constant digits. The separately audited original graph has exact degree 174
for its phase-split2471 ports; this packet does not independently certify the
exact degree after substituting the distinct 2011 tuple.

The 2011 fixed tuple and the JSON's original phase-split2471 tuple are
**different**. The symbolic node theorem holds for any integer tuple, but its
2011 specialization is a distinct candidate. This packet does not prove that
the two coefficient tuples agree, calibrate the phase-split tuple, establish
the all-model carrier converse, or establish either direction of an iPRA
consistency equivalence. Positive shifting adds a separate substitution in the
syntax: the 69 count describes the positive-coordinate DAG, not a claim that
the unshared expanded nonnegative-coordinate syntax has 69 operations.

## Paired bounded replay

[`replay.py`](replay.py) checks the exact source-row binding and then rebuilds
`ShortEquation`, `ThirteenCarrier`, `Thirteen69Nodes`, and `Thirteen69Cuts`
separately on each side of the independently audited
[70-source coherent provider](../../reviews/ordinary12-coexistence-pair-independent-audit/README.md).
The four modules are rebuilt from pinned source; no historical project object
is mixed into either sibling. It checks each direct import, compiler exits,
object hashes and axiom reports, and the parent comparator before and after.
The actual wrapper session `17498` exited `0`; its
[terminal observation](terminal-observation.json) records the output and
[receipt](replay-receipt.json) records all eight compiler and eight dependency-check
exits and matching object hashes. The final model theorems report only
`[propext, Classical.choice, Quot.sound]` with no warnings or `sorryAx`.
These are Lean metatheory axioms, not extra object-theory iPRA axioms.

Run a fresh replay where the pinned parent/provider paths remain available:

```
python3 -I -S replay.py --output /tmp/ipra-thirteen69-dag-pair-NEW
```

The paired suffix has not yet received an independent artifact audit. The
provider inherits the original Foundation wrapper's unobserved outer exit and
package-transitive and dynamic-loading qualifications. Checks are at observed
points, not protection from mutation between observations. Earlier global
normalization attempts exceeded resource bounds and were retained with the
[canonical-binding packet](../thirteen69-canonical-binding/observations/failed-attempts.md);
the successful cut-point proof avoids that expansion.
