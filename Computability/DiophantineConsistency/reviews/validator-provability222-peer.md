# Actual C222 theorem predicate: independent read-only review

26 October 2026. **PASS within the stated scope; no correction requested.**
I independently read all 125 main lines and 48 check lines, the complete
author receipt/replay metadata and all three drivers. I checked the actual
new proof constructors and all-code Nat binding, and reread the generic
Lukasiewicz and Kalmar interfaces and the rho6/rho8 numeric contracts.
I did not compile, execute the author's drivers or edit frozen sources.

| Input | SHA-256 |
|---|---|
| Main | `a3b50d8088d288ee951f2a9612e624e54ea78814151aaa3a2acc083242ac78b2` |
| Checks | `c9422b37c6c3847a0e3516c2fb709301c924ca36a8f228bcc58c5614e5f90a68` |
| Author receipt | `abb513de5ebb20f48643c9dae9fe275499f8b7df5366955363d2a5d6387f5370` |
| Replay metadata | `30d8f8e282925072f4fd51543ce4727e95e54fa9a96c580b809dbd23446bfa63` |
| Input inventory | `2fd0d8df9f097cb269a685d63dc148e48e30445985f2bb0230987886870e11d5` |

`cProvDef` is fixed Σ₁ syntax declared before the ambient model variables.
Its interpretation is exactly `∃code, value code=conclusion+1` in every
ORingStructure model of IΣ₁, using the new history's actual acceptance
formula. No free semantic oracle or model-specific formula is supplied.

Every closure constructs an actual numeric proof node. MP accepts its
major premise first, but its payload is correctly ordered as conclusion,
minor proof code, major proof code. GEN uses the full child code. The
equality leaf is the actual growG rule; rho7 is not assumed. The bundle
closure retains precisely the two gates `c≠a,b`, including the legal
`a=b` and `c=0` cases. The fixed false formula code is 1.

The generic propositional certificate requires only actual MP and rho8,
with no implication injectivity, freshness, standardness or seed-validity
assumption. Its parameter ordering agrees with the literal rho8 circuit.
The ex-falso proof is the explicit finite rho6/K/S derivation: with
`x=∀0(∀0 a→1)` and `e=x→1`, rho6 supplies `e→a`, K supplies `1→e`
and `1→(e→a)`, and S/MP yield `1→a`. Thus `Kalmar.Classical` describes
the represented C222 proof calculus; it is not an added classical rule
for HA or a semantic consistency assertion.

`cProv_nat_iff` composes the actual all-code Nat acceptance theorem with
the fixed formula interpretation. Its right side is exactly
`KCode222.C222`, not the old calculus and not an assumed checker agreement.
The old History254 transitive dependency contributes only the already
reviewed generic Nat arithmetic normalization in that adapter.

All **586 provenance hash comparisons matched**: 122 selected custom
sources (95 Foundation), 407 object companions, 38 external roots, two
parent receipts, compiler/manifest, input inventory, three drivers, final
source snapshots, run records/logs/timings and output objects. Every
recorded source import list was independently reparsed and matched. The
external cache/package boundary is explicit; this is not a fresh closure
validation. Private overlay: `/tmp/provability222-controller-v9au4606`.

The recorded first fresh main/check pair passed with the 4.32.0 compiler,
`-M6000 -j1 -DElab.async=false`, no main diagnostics and ten axiom reports
using only `propext`, `Classical.choice`, `Quot.sound`. These are verified
author records; no independent compilation is claimed here. Root separately
reports a fresh pair. My prior reviews of the template, row, history and
Nat adapter are disclosed; I did not author this packet or its new rules.

Seed validity, rho7 recovery, an internal calculus translation, actual
machine runtime and the desired internal HA consistency equivalence
remain separate work. Nothing in this packet is used to replace those
missing steps with standard-model agreement alone.
