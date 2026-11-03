# Independent audit of corrected 80-to-90 main-factor receipts

The captured read-only check passes for the three corrected guarded author
builds: fresh main offset, fixed-placeholder 90 main factor, and flexible
90 main factor. It verifies their source, self-pinning v2 runners, Lean tool,
all selected object hashes, logs, axiom reports and six resolved direct
imports; all six are individually pinned. It inventories 12 retained
terminal histories and 17 sampled resource observations.

The corrected fresh-offset runner includes the previously missing direct
`ArithmeticPellCongruences.olean` pin. The actual resolved object is
`/tmp/direct90-ipra-join-b66u_qqo/lib/DiophantineConsistency/ArithmeticPellCongruences.olean`,
SHA-256 `ff395c82ca9ea770a64ec69e4b4b7f8e1e2d655d67db4831af39a2d8a78ae664`.
Both dependent v2 builds select the new offset object at
`/tmp/tenpositive-80freshmainoffset-zbew9euo/Direct80FreshMainOffset.olean`;
the audit checks its output hash and the selected paths. Each of the three
new objects is bit-identical to its previously accepted counterpart and the
Lean source hashes match. This corrects the specific direct-pin omission
identified in the [earlier audit](../ten-positive-80-to-90-main-independent/README.md).

The flexible theorem retains `∃ η ζ γ h` outside `∀ t T n s` for positive
free coordinates and proves positivity and the selected 90 Lean graph's main
factor zero at the same fresh witnesses. The β, low and shifted-high symbolic
port equalities and the actual positive 80 graph zero remain premises; p₁ is
arbitrary. This is still only a main-factor result, not a whole-graph zero,
positive-zero equivalence, external payload binding, or iPRA endpoint.

The audit does not independently replay Lean or authenticate full transitive
serialized, package, dynamic-library or historical source-to-object ancestry.
The reported Lean axioms concern metatheory dependencies, not object-theory
iPRA axioms.
