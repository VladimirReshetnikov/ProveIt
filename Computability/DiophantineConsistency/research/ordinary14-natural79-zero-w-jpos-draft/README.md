# Natural-79 J positivity at w=0: source proposal

`Natural79ZeroWJPos.lean` proposes one step in the model proof of the
[79-operation forced-w reduction](../ordinary14-natural-forced-w79/README.md).
It depends on the proposed [literal factor residues and zero-w units](../ordinary14-natural79-factor-residues-draft/README.md).
The source and all its dependencies are **unelaborated**; no Lean theorem,
axiom report, iPRA derivation or physical coefficient/PDF binding is established.

The intended statement works in a model `V` with `ORingStructure` satisfying
`𝗜𝚺₁`. Given an arbitrary integer port tuple `p`, an element `K : V` with
`(p 1 : DiffRing V)=ι K`, a literal 79 zero and `v 6=0`, it proposes
`0<v 0`. In this model K is a natural-model element, so its embedding is
nonnegative; no separate strict-K0 hypothesis is required. There is no beta,
gamma or w-positivity premise, and the MC and MF ports are unrestricted.

The proposed zero-specific unit client supplies that the signed guard factor
represents +1. The new helper proposes converting that signed-pair equation
to a difference-ring evaluation of one. If also `J=v 0=0`, the literal graph
has `X=q*w=0`, and the guard specializes to

```
−(ι(v 1)+ι(v 2)+1)*ι K − ι(v 1) <= 0.
```

All four embedded natural-model values are nonnegative, so this contradicts
the guard's evaluation being one. When `K=0` and `v 1=0`, the specialized
guard is exactly zero: a strict-negative bound would be unjustified, but the
nonpositive bound suffices. Decidable natural-model order then supplies
`J>0`. This does not prove the target `w>0`; after J positivity, the main
norm and divisibility contradiction of the [forced-w model route](../ordinary14-natural79-w-model-route/README.md)
still need explicit graph and model bindings.

The checker pins the source, literal Lean graph/JSON, unit client and model
interface; compares all graph rows and aliases; derives the guard cut as an
exact sparse-polynomial identity with J=w=0 and arbitrary integer symbolic
ports; checks the cited source signature and unit-conjunction position; and
runs 300 finite nonnegative controls including the zero-K0 edge. This is
external source/algebra evidence. It does not verify Lean casts, tactics,
name resolution, zero-w unit theorem, model instances, providers or axioms.
Both `#print axioms` commands remain unexecuted. No actual symbolic port is
bound to the represented model K by this packet.

An [independent source and mathematical review](../../reviews/ordinary14-natural79-zero-w-jpos-independent/README.md)
checks the guard cut and the nonnegative-K0 boundary without elaborating Lean.

Run from the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/ordinary14-natural79-zero-w-jpos-draft/check_source.py | cmp - Computability/DiophantineConsistency/research/ordinary14-natural79-zero-w-jpos-draft/result.json
```
