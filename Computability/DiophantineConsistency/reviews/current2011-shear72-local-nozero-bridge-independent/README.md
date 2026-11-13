# Independent review of the local no-zero bridge selection

The local no-zero interface and bridge have the same mathematical directions
as the previous generic bridge. The selected source changes and direct
frontier cut agree with the pinned predecessor, and no concrete source-level
mismatch was found. The local proof, name resolution, transitive imports and
all endpoint declarations remain unelaborated.

The local `SameNoZero` definition is textually identical to the generic
`HAExpressionNoZeroEquiv.SameNoZero` definition: in each IΣ₁ model it says
child no-zero iff parent no-zero. The `ParentToChild` and `ChildToParent`
propositions and their `same_no_zero` proof are unchanged. Each map is used
in the correct contrapositive direction, and may return a different valuation.

The new `bridge72` follows the generic bridge proof: `classicalNoZero_iff`
identifies each formal no-zero sentence's model evaluation with absence of
split-natural zeros; the local equivalence transfers from child to parent;
the existing 71 parent `PolynomialBridge` completes the transitive
biconditional. The pinned source places `classicalNoZero_iff` and
`PolynomialBridge` in `HAExpressionAssembly` and `classicalNoZero` in
`FoundationHANoZero`, both opened by the alternative. The semantic
interfaces are source observations; their availability in the selected Lean
provider environment and the `rw`/`simpa` steps are not checked here.

The native, standard and mapped translated endpoint tail is unchanged
byte-for-byte. The joint alternative removes only the old namespace opening
and opens the local conditional namespace, so its `SameNoZero` refers to the
local definition at source level. The selection changes only those two draft
entries and removes `HAExpressionNoZeroEquiv` from the direct frontier. The
independent checker verifies every selected header and nonexternal frontier
source, reachability and acyclicity: 15 draft names and 12 direct frontier
names. Direct removal does not establish transitive absence, resolve object
providers, discharge either map hypothesis or prove an iPRA endpoint.

The preceding narrowed order-import selection was independently reviewed in
[the separate order-carrier audit](../current2011-shear72-order-carrier-selection-independent/README.md).
Both source selections retain their respective provider and theorem limits.

From `Computability/DiophantineConsistency`:

    set -o pipefail
    timeout 30s python3 -I -S -B research/current2011-shear72-local-nozero-bridge-selection/check.py | cmp - research/current2011-shear72-local-nozero-bridge-selection/receipt.json
    timeout 30s python3 -I -S -B reviews/current2011-shear72-local-nozero-bridge-independent/check.py | cmp - reviews/current2011-shear72-local-nozero-bridge-independent/receipt.json

Both receipts reproduce. No Lean, build, staging or reviewed-source mutation
was performed.
