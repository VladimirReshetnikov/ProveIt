# Adaptive Pell indices: author result

Both internal Pell indices now follow from the actual adaptive equation's
zero. The theorem retains the first root's scaled magnitude and the positively
oriented main signed root, and gives positive, bounded indices with their
precise recurrence coordinates. The shifted-current natural client assumes
only the literal natural zero. The [scope note](../research/adaptive-pell-indices2011.md)
spells out the parameters and the claims that remain open.

The accepted main-orientation and earlier Pell-classification provider overlays
had 344 overlapping artifacts, all byte-identical. The prior Pell plan showed
three changed current sources (Recurrence, Classification, Congruences); the
current FirstNorm source also changed and now imports KnownUnit. The author
refreshed UnaryRecursion, Recurrence, Classification, Congruences, KnownUnit,
and FirstNorm in dependency order, followed by both new client modules. The
first preflight build failed because the new UnaryRecursion prerequisite was
missing from the old overlay; the corrected build explicitly includes it.

Two fresh corrected author builds both passed with identical source hashes,
object hashes and complete logs for all eight modules. Compilation produced
no warnings. The checks print the Lean axioms `propext`, `Classical.choice`,
and `Quot.sound`; these are Lean metatheory dependencies, not a literal HA proof.
The builds rehashed inherited provider files and all 344 intersections. The
package and toolchain interiors remain inherited boundaries. The prior main
orientation and old Pell providers were independently replayed; this six-module
refresh and new pair still require independent review. The first successful
provider is `/tmp/adaptive13-indices-n06y4jf8/lib`.

The [66-file evidence manifest](adaptive-pell-indices2011-build-evidence/FILES.json)
SHA256 is `e2b9f65e69cda5101ecd6cbe8af0ca6d6e9c8857ecbdfb7b4c66d0284db06a51`.
It preserves the failed preflight and both successful attempts, including
snapshots, logs, timings, drivers, state and provider inventories.

| Source | Source SHA256 | Object SHA256 |
| --- | --- | --- |
| ArithmeticAdaptivePellIndices2011 | `3ba88e58accc2451ebd39abdfe3e441e4bad424b85b350da636077d86b8775d4` | `b5056dcdb1f7612fbad02fc892541f033fa3093eaa63761f9f81d8db8bc095ec` |
| ArithmeticAdaptivePellIndices2011Checks | `1f94685621a35a6aa5c5ce3841bc69ebb98166edd3777ac207772a77b254e42b` | `f2d7540b3a78857d66d266f76c22c2a448ade6470e54aace4bb4f8866ef543a7` |
