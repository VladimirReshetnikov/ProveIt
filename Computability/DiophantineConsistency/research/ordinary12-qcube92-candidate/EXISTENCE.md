# Positive zero-existence comparison for the 92-operation graph

`QCube92Existence.positive_zero_iff` proves that, in every model of `IΣ₁`,
the 92-graph has a positive-coordinate zero exactly when the 95-operation
free-J graph has a positive-coordinate zero. This holds for arbitrary
natural-number ports, assuming that the first port β is positive in the
model. The quantification is over all elements of the model, including
nonstandard witnesses. The two directions do not assume consistency or
halting.

The forward map replaces `s` with `q³s` and preserves positivity. For the
reverse map, the rebuilt `FreeJRootBinding.first_factor_forces_Y_divisible`
obtains `Y=q³s` from the old zero and positive `J,β`; positivity of `Y`
then forces `s>0`. An explicit coordinate update is shown to invert the
forward map. `QCube92Model.zero_iff_transformed` supplies the transformed
zero comparison, and the existing 94-to-95 bridge completes the composition.

The unchanged [divisibility source](FreeJRootBinding.lean) was copied from
`research/ordinary12-ipra-bridge/free-j-first-divisibility-prototype/` and
rebuilt against the same selected 94-graph provider. The bounded
`binding-attempt01` exited 0 in 8.2 seconds, with no warning or `sorryAx`;
its two direct project objects had hashes `14016535…` and `b838afab…`,
matching both the earlier replay receipt and the selected provider. The source
and runner hashes are
`5d826d8f1cf5ce4a11c45f4a6762ba0729a5e282a1356bce0aeb02f49c58083b` and
`b66de5fd78d7e05fe4fb0aed3185a12399ffd5ebd6eaf0e2b3d7d343c0d003a2`.
Four memory samples saw up to two Lean processes and at least 18,146,888 KiB
MemAvailable.

The bounded `existence-attempt03` exited 0 in 4.2 seconds, without warnings
or `sorryAx`. Both named theorems report only the Lean metatheory axioms
`[propext, Classical.choice, Quot.sound]`. Its source and runner hashes are
`62b030d3c8d0ccfac46b4b0c41be58c67dbe96e7794d01c284c317499c456e9d` and
`6ddc322eb4cad3f0df3a59dacc7d8b546144801a46ac1365ee22e643810d07bb`.
Two samples saw one Lean process and at least 18,518,996 KiB MemAvailable.
Sampling does not exclude shorter overlaps or memory dips. The first existence
attempt failed on a name resolution; the second compiled but was rejected for
a linter warning. Their exact source snapshots, logs and receipts are kept
alongside the successful run.

The author runners record 74 and 77 selected provider-file hashes respectively
and report them unchanged. Their traversal does **not** cover every object
behind symlinked directories; full source-to-object, package-transitive and
dynamic ancestry remain inherited. This is not an independent replay or an
internal iPRA derivation. The fixed-port positive-β proof and composition with
the 95-graph halt theorem are separate Lean work. The graph, coefficient
files, TeX and PDF remain connected to these expressions by external checks,
not a Lean file or PDF semantics theorem.

With the recorded providers available, use fresh attempt names to replay:

```sh
ATTEMPT=attempt02 python3 run-binding.py
ATTEMPT=attempt04 python3 run-existence.py
```

The existence runner names the originally recorded binding and model output
roots explicitly; replaying the binding in a new directory does not
implicitly replace that pinned import.
