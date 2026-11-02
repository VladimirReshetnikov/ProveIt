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
for its phase-split2471 ports. A further external [2011-port degree check](check_degree2011.py),
described below, checks that the same degree survives the distinct tuple.

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

The paired suffix passed an [independent artifact audit](../../reviews/thirteen69-dag-binding-independent-audit/README.md).
The provider inherits the original Foundation wrapper's unobserved outer exit and
package-transitive and dynamic-loading qualifications. Checks are at observed
points, not protection from mutation between observations. Earlier global
normalization attempts exceeded resource bounds and were retained with the
[canonical-binding packet](../thirteen69-canonical-binding/observations/failed-attempts.md);
the successful cut-point proof avoids that expansion.

## Exact degree at the 2011 ports

[`check_degree2011.py`](check_degree2011.py) reruns the pinned prior
[`audit.py`](../thirteen-variable-independent/audit.py) leading-form
calculation on the exact 69-row schedule. That calculation treats all four
ports as symbolic coefficients and checks the entire degree-174 homogeneous
form, including the full main-norm cancellation; specialization of any
integer ports can only lower that degree. For the variable monomial

```
J^101 gamma i^4 eta^15 w^14 s^27 f^8 T^4
```

the script checks that the entire generic coefficient consists of the single
term `-128*beta^101`, with no K, MC or MF terms that could cancel it. The
checked 2011 tuple is exactly `CurrentMasks2011.ports (K : ℤ)`:
`(beta, K, lowPort, highPort+beta)`, with `beta=(2^47)^2011-1`. Modulo
`1,000,000,007`, this beta is `878756698` and the selected coefficient is
`937554773`, so the coefficient is nonzero. Thus the distinct 2011-port DAG
has exact degree 174. The substitution of each variable by `x+1` preserves
the leading homogeneous form and therefore its degree.

The normal check actually exited `0` and wrote [its receipt](degree2011-receipt.json)
(SHA-256 `1c78a79547036a9b88ac7ef2bd5d7d3b4a3ccabe3eb265208985397f1789b0fb`);
an optimized `python3 -I -S -O` invocation actually exited `1` before the
check. This is an external finite sparse-polynomial check, reusing the
earlier audit rather than an independently authored proof or a Lean theorem
about polynomial degree. It does not establish PDF semantics, the converse,
or the final iPRA equivalence. An independent review is pending.
