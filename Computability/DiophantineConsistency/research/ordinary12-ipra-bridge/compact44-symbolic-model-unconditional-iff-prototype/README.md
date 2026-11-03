# Symbolic compact model equivalence without port hypotheses

`CompactSymbolicModelUnconditionalIff.model_iff` proves, in Lean and for
**every model of `IΣ₁`**, that

```
(∃ v : Fin 12 → V, (∀ j, 0 < v j) ∧ InternalZero (literal p) v)
  ↔ ∃ T : V, ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0.
```

Here `p` is the exact integer-cast symbolic tuple defined by
`CompactSymbolicModelIff.p`:

```
ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat
= ![betaNat, paramKernel rho, lowNat, betaNat+highNat].
```

The last port includes one beta shift. The proof applies the previously
checked conditional model equivalence and supplies all four of its explicit
model port hypotheses using `CompactSymbolicPortProjections.beta`,
`.kernel`, `.low` and `.high`, instantiated at the **same** symbolic
kernel and, for beta, at each chosen model length. Thus no port-cast
hypotheses remain in this theorem. Its only ambient assumptions are the
model's `ORingStructure` and `IΣ₁` satisfaction instances. Positive graph
zero and halt on the right are **internal to the model**; the time and
coordinates can be nonstandard.

This is an all-model statement for the 95-operation, 12-variable **symbolic
free-J graph**. It is not yet a Lean proof that an iPRA derivation exists,
not a proof that these symbolic coefficients equal the retained payload or
`equation.pdf` bytes, and not a theorem about the 14-variable PDF equation.
Joining it to an iPRA adapter requires a coherent dependency provider;
point-in-time comparison of a separate adapter provider found significant
object mismatches, so direct overlay is not justified.

The bounded mixed-provider single-author `observations/attempt01` actually
exited 0 without warnings or `sorryAx`. The named Lean metatheory axiom
report is exactly `[propext, Classical.choice, Quot.sound]`, not an
object-theory axiom list. Source SHA-256:
`ed8a55893fbf6be3d6272fbc713edfa2d32107caff6756152865e49fc8fd037e`;
object SHA-256:
`bf9452403b3d83d0cddc0155bb54a35681f7847e5b35146b535279b6083a6e0a`.
The exact source, direct import/companion guards, terminal receipt and
selected provider inventories are retained in the attempt. The 514 shared
reverse/gamma project entries matched at preflight and were unchanged after
the build; no same-named selected-provider file conflicts were found, and
all recorded direct guards and provider inventories remained unchanged.
The runner uses a fresh selected object root for the coherent 14-module
graph-client predecessor and the checked halt client.

This result is one exploratory author build, not a matched paired replay or
complete authentication of transitive, package or dynamic ancestry.
Filesystem and provider checks are point-in-time, not continuous monitoring.
