# Conditional model equivalence for the fixed symbolic compact tuple

`CompactSymbolicModelIff.model_iff` joins the previously checked reverse
and constructive directions in any `ORingStructure` model of `IΣ₁`. It uses
exactly the fixed natural tuple

```
ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat
= ![betaNat, paramKernel rho, lowNat, betaNat+highNat]
```

cast pointwise to the integer port tuple `p` of
`Ordinary12FreeJ.literal`. In particular the fourth port already includes
one beta shift. The theorem proves

```
(∃ v : Fin 12 → V, (∀ j, 0 < v j) ∧ InternalZero (literal p) v)
  ↔ ∃ T : V, ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0
```

under four **explicit** model difference-ring port assumptions. The first
requires, for every model time `T`, the beta-port product with
`rep 590069 (haltLength T)` to equal
`Exp.exp (590069*haltLength T)-1`. The other three require the interpreted
integer kernel, low and shifted-high ports to equal respectively the model
casts of `paramKernel rho`, `low`, and
`high+(Exp.exp 590069-1)`. These are assumptions of this theorem; they are
not silently identified with the retained/displayed equation.

For positive symbolic graph zero, the proof invokes
`FixedGraphMarkedHaltDraft.graph_halts` to produce an internal halt; this
implication itself needs no port-cast assumptions. For an internal halt at
`T`, it invokes `FreeJHaltModelZero.halt_positive_zero_of_ports` with the
beta assumption at that same `T` and the other three stated casts. The
`Draft` suffix in the reverse theorem's namespace is historical: the exact
graph-halt client belongs to the 22-child author suffix with an independent
artifact audit. Its inherited package/transitive/dynamic qualifications
remain; it is not a paired proof.

This is a conditional **model-level** equivalence for the 95-operation
12-variable symbolic free-J graph. It is not yet a Lean proof that an iPRA
derivation exists, a binding of the symbolic constants to retained bytes or
`equation.pdf`, or a claim about the 14-variable equation in that PDF.

The bounded single-author `observations/attempt01` exited 0 without warnings
or `sorryAx`. The named Lean metatheory axiom report is exactly
`[propext, Classical.choice, Quot.sound]`, not an object-theory axiom list.
Source SHA-256:
`481b94d4cb0eeb5d3aec2f4a48ce1ec2844dabdf22eac19089353efec4f28042`;
object SHA-256:
`b7d9867f6437385a7f7f51478337d08317b2beed660d5f63050b545c3272805a`.
The runner verifies the previously checked 14-module namespaced graph-client
chain, uses a fresh root of selected object links plus the successful halt
client, and rejects conflicting same-named provider files. The independently
artifact-audited reverse provider and selected gamma project had 514 matching
project files at preflight, with no mismatch. Direct import/companion guards,
selected provider inventories and that reverse overlap were unchanged at the
final checks. Exact source, compiler output, guard/inventory records and
terminal receipt are retained under the attempt.

This single mixed-provider author build is not a matched paired replay or a
complete authentication of inherited transitive, package and dynamic
ancestry. Inventory/guard checks are point-in-time and do not establish
continuous filesystem or whole-process-tree resource monitoring.
