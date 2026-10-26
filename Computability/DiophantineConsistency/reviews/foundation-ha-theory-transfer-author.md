# Source-theory proof transfer into HA — root author receipt

26 October2026. Root authored and read the complete main/check pair and
private build/freeze drivers before execution. This is author validation;
an independent review is still required.

`HA.Relative.discharge` removes an actual finite list of assumptions using
genuine theorem proofs of its entries. Induction on that list uses existing
implication introduction and MP, retaining the underlying finite arithmetic
axiom lists. Repeated assumptions and sparse free variables remain legal.
`intuitionistic_theory` applies the existing finite proof-tree map, obtains
each source assumption from the actual context-subset certificate and
discharges precisely those assumptions. `classical_theory` composes this
with the existing Foundation GG theorem. Its premise that each source
axiom image has an HA proof is explicit; this does not identify an arbitrary
theory with HA.

The concrete `semiring_provable` corollary has no image-provability premise:
its source theory is exactly the eight already discharged semiring axioms.
Checks apply it to a source axiom and a genuine source conjunction proof.
A separate duplicated open context at variables0/7 tests finite discharge
using actual HA add-zero and multiply-zero instances.

Main SHA256: `e25cb43e446840f1cfebe1020ce7ec74a38a12b98bc76371d94e54fc6fc2fa50`.
Checks SHA256: `53158b2880e1645902d8e115b80e177ab5fd8efd9395f6ac863ecf82f4b338fb`.
The main passed on its first invocation with an empty diagnostic log. One
check draft failed because its local formula abbreviations were not
unfolded in context-membership simplification. Adding those definitions
fixed the check without changing a theorem statement or premise. The
unchanged main was not rebuilt unnecessarily. The final seven axiom
reports use only `propext`, `Quot.sound` and, in the existing GG composition,
`Classical.choice`. Discharge, the intuitionistic map and its direct open
context check use only the first two. No new axiom or HA classical rule
is introduced.

Both final leaves used `-M6000 -j1 -DElab.async=false` in private
`/tmp/foundation-ha-theory-transfer-root-bqzregv0/lib`. The93 cached
prerequisites include76 Foundation modules. The existing59-module GG
inventory agrees on its exact source/object subset with the accepted
76-module syntax/equality inventory. Five hundred inherited/additional
pin observations, compiler and package identities were checked before and
after each run and at freeze. Only the two final leaves are fresh proof
checks; no prerequisite closure was rebuilt.

[Replay metadata](foundation-ha-theory-transfer-dependency-replay.json)
pins both final objects and logs. The durable
`foundation-ha-theory-transfer-author-replay/` bundle preserves all three
executed invocations, source snapshots, inputs and both build-driver
versions. Its first preparation version failed a metadata representation
comparison before running Lean; the corrected version compares exact
object paths and hashes instead of dictionaries with different optional
fields. Full arithmetic transfer, target-sentence comparison and the final
HA consistency equivalence remain open.
