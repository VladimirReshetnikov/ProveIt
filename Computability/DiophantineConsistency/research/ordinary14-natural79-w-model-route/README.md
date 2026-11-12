# Model-proof route for forced w in the natural-79 graph

This is a **source-level research route**, not a Lean-checked theorem. The
external [79-operation construction](../ordinary14-natural-forced-w79/README.md)
removes one input shift from the natural-80 graph; its local standard-integer
proof uses divisibility. `ForcedWDivisibility.lean` proposes two abstract
commutative-ring divisibility lemmas needed in a corresponding model proof.
It is unelaborated source: neither the module nor its two `#print axioms`
commands have run. The graph-to-model, iPRA endpoint, and physical-file/PDF
bindings are not established here.

An [independent source and mathematical review](../../reviews/ordinary14-natural79-w-model-route-independent/README.md)
checks the ring identities, cited model-divisibility interfaces and the
zero-specific unit gap, without elaborating Lean.

## Existing model-level source interfaces

The source `ArithmeticSquareDivisibility.dvd_of_square_dvd` states that in an
`ORingStructure` model of `𝗜𝚺₁`, `m>0` and `m*m ∣ z*z` imply `m ∣ z`.
Its proof is written using an internal gcd/Bézout certificate; its statement
does not assume that the model is the standard natural numbers or invoke a
standard-natural prime-factorization principle. The source
`ArithmeticAdaptiveQuotients2011.scaled_quotient` builds on that interface:
if `m>0` and `z²=m²*n`, it supplies `z=m*t` and `t²=n` in the model.
Whether the retained objects and transitive providers elaborate coherently
with a new draft is **not** established by inspecting these sources.

`ReducedNormSigned.natural_magnitude_square` proposes, for a signed element
of `DiffRing V`, a natural-model magnitude whose embedded square agrees with
its square. `Direct80NaturalProjection.natural_dvd_of_signed` states that
signed divisibility between two embedded natural-model values reflects back
to natural-model divisibility. `ModelDifferenceRing` provides the evaluation
and embedding interfaces. These declarations suggest how to work with a
possibly negative main root without assuming a positive root or standard
integer semantics. Their actual use, casts, instances, dependencies and axiom
closure must still be checked in Lean.

## Why existing 74 own-zero extraction cannot be applied at w=0

The unelaborated `OwnZeroProduct74Draft.factor_units_of_zero` requires
`0 < v 6`, the 74 graph's w coordinate, as well as positive beta, J and s.
Its `FirstFactor74Draft.m_at_least_two` client uses that assumption to show
`m=X*Y²>=2` for a negative-Pell exclusion. At the critical 79 valuation
`w=0`, the corresponding 74 valuation has `w=0` and `m=0`, so invoking that
extractor would be circular and its hypotheses are false. No currently cited
source client establishes the required five unit equations for this case.

A new **zero-specific** unit argument is needed. In the literal 79 graph,
`w=0` makes `X=ell=0` and the first factor `F0=r²`; hence it cannot be the
negative unit. The 74 residue draft states that the other three restricted
factors avoid negative one modulo four at arbitrary valuations. The source
`ArithmeticSignedPairs.product5_magnitudes` extracts magnitudes from a
five-factor product equal to one, and `product5_positive` can force the
remaining guard factor positive after four explicit negative-unit exclusions.
To use these interfaces, one must first transcribe the 79 graph in Lean,
prove its related-valuation identity with the 74 graph while **keeping w
zero**, connect its own `InternalZero` to the signed five-factor product,
prove the first square factor's negative-unit exclusion in that model, and
bind the three remaining residue premises to the literal factors. The
unelaborated 80-to-74 partial bridge assumes a different w shift and is not
by itself this 79-to-74 identity. None of these new 79 obligations is supplied
by the abstract ring lemmas in this packet.

## Intended signed model argument after the missing bindings

Assume those unit equations and the represented port conditions have been
proved in the model. At `J=0` and `w=0`, the guard factor is nonpositive
when `K0>=0`, contradicting its forced value one. Thus `J>0`; with positive
beta, `q=1+J*beta>=2`. The retained positive s shift then gives `Y>=q³`,
`U=Y*q²>0`, `a=Y` and `H=4Y+3`.

The main unit must be bound to the exact model equation
`Dstar²=U²*(1+(a²+H)*c²)` with `Dstar=U*a*c+H*shift`. Use a natural
magnitude for `Dstar` and the positive-scale quotient source above to obtain a
signed `d` in the difference ring with `Dstar=ι(U)*d` and
`d²=1+(a²+H)*c²`. This outline requires explicit treatment of both signs,
the signed-pair/root binding, and the embedding of every natural quantity.
It should not assume `Dstar` is nonnegative. The graph equation then yields
`H ∣ U*(d-a*c)` in the difference ring. The proposed
`ForcedWDivisibilityDraft.divisor_of_main_norm` derives `H ∣ U` from this
and the square norm, using an explicit polynomial witness, for any
commutative ring. The proposed `divisor_of_three_square` derives
`H ∣ 3*q²` from `H=4Y+3` and `U=Y*q²`, again with an explicit polynomial
witness. These are conditional source declarations, not model conclusions.

After reflecting the signed divisibility to natural-model values, prove
`0<3*q²<H`: from `q>=2` and `Y>=q³`, `H=4Y+3>3q²`. A natural-model
positive-divisor bound contradicts this divisibility. The resulting `w>0`
would give a predecessor and a related-valuation zero map to natural-80;
only then could an audited model bridge and the existing semantic-to-iPRA
conversion be composed. Port hypotheses, predecessor witness orientation,
provider provenance, Lean elaboration and all axiom reports remain separate
obligations. The local standard-integer map uses `beta>0`, `K0>=0`, arbitrary
MC/MF; the stronger compact-port/rank assumptions inherited from the parent
endpoint are not removed by this local argument.

The deterministic checker pins the 79 candidate, the proposed ring source and
selected source interfaces; checks 28 literal graph-shape rows including the
main factor; checks two ring rearrangements by exact sparse-polynomial
arithmetic; and evaluates 99 finite algebra controls. These tests do not
elaborate Lean, authenticate providers, establish the graph/model bindings or
prove an iPRA derivation. A source theorem declaration and its written proof
are not a new kernel-checked replay.

Run from the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/ordinary14-natural79-w-model-route/check_sources.py | cmp - Computability/DiophantineConsistency/research/ordinary14-natural79-w-model-route/result.json
```
