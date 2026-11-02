# From the graph to the compact decoder: source-only plan

This is a proposal, not a compiled theorem or paired build. The setting below
is an arbitrary model `V` of `IΣ₁`, used in Lean's metatheory. The desired
end result still requires an internal iPRA proof, which does not follow just
from these model-level statements. In particular, no global graph-to-decoder
transport or machine simulation is established here.

## Existing graph outputs and the first useful new lemma

Use `p = CompactSymbolicPorts.ports betaNat K lowNat highNat`, positive
coordinates `v : Fin 12 → V`, and `InternalZero (literal p) v`, with the
casts and literal exactly as in `CompactGraphDerivedRadix.fixed_graph_digits`.
Put

```
q = 1 + v 0 * p 0;  C = q - v 1 - v 2;  F = v 1;
d = 67 * 8807;      n = 8807 * N;         M = q - 1.
```

`CompactGraphDerivedRadix.fixed_graph_digits` supplies `N > 0`,
`q = Exp.exp (d*N)`, `v 0 = rep d N`, `dig 67 C 0 = 1`, and digits of
`C` bounded by three at positions below `n`. Its `K` is an arbitrary natural
parameter. `FreeJRadixAlignment.graph_alignment`, called in that proof,
also supplies a `w` with `v 5 = q*w` and
`w = Exp.exp (R-d*N)` for the theorem's exact graph index `R`.

The first graph-to-carry congruence has now compiled in the single-side
[exploratory client](../free-j-first-congruence-prototype/README.md). Its
`graph_congruence` assumes the graph, positive coordinates, positive beta,
and the explicit alignment `v 5 = q*w`; it proves:

```
0 < M ∧ F < M ∧ ((K : V) + w) * C % M = F.
```

The nearest source interfaces are `FreeJRootBinding.root_rep`,
`first_root_quotient`, and `first_factor_forces_Y_divisible`, together with
`FreeJFirstTransport.freej_first_factor_transport` and graph alignment. A
concrete proof route is: set `Q = q³`, `b = q−1`, `A = v 5 + K*q`,
`W = 1 + (v 8+v 9)*b`, and
`Bn = (v 1+v 2)*A + v 1*q`, `Bp = q*A`. The first root is represented by

```
Q*b*(ell+k+v 7) + v 6*b + Bn*(W*Q),   Bp*(W*Q),
k = v 8+v 9,  ell = (v 5*v 6)*(v 6*k).
```

The root quotient makes the pair congruent modulo `Q*b`; the existing
`Q ∣ v 6` allows cancellation of `Q`. Since `W ≡ 1 (mod b)`, this should
give `Bn ≡ Bp (mod b)`. The existing strict orientation gives
`C*A > F*q`, so rewriting `Bp−Bn` is legitimate in the natural model.
Using `v 5=q*w` and `q ≡ 1 (mod b)` then yields the displayed candidate.
The same strict gap `v 1+v 2 < q`, together with `v 2>0`, is expected to
give `F < b`. This is the proof strategy implemented in that exploratory client. The paired
replay and independent artifact review have not yet been performed.

`FreeJMainOrientation.main_congruence` is another existing additive graph
congruence, but it is a different `q^5` relation used for the rank argument;
it is not already the above modulus-`q−1` weighted-word equality.

## Stronger no-carry output and actual slot caps

`FreeJSaturationClient.graph_saturation` proves, under its explicit graph,
radix, port-split, mask-population and positivity hypotheses,

```
NoCarry (C - 1) (MC * v 0 + 1)
NoCarry F (HP * v 0 - 1).
```

Here `MC = p 2`, `p 3 = HP + p 0`. The `CompactSymbolicGraphDigits`
client establishes the symbolic-mask population/residue assumptions for
its stated symbolic ports; its existing result retains only the final
`C`-digit bounds. A useful companion lemma should expose these no-carry
conclusions under the fixed symbolic graph hypotheses alongside `N`, `w`
and the repunit equations. It should not assume that the general
`digit ≤ 3` statement alone implies either no-carry assertion.

`CompactMixedIncrement.decode_mixed_increment` already proves the
following intermediate fact inside its proof, but does not export it:

```
∀ k < 8807*N, 0 < k →
  NoCarry (dig 67 C k) (dig 67 MC (k % 8807)).
```

A second concrete lemma should export this fact, preserve its `k > 0`
condition, and separately retain `dig 67 C 0 = 1`. It can reuse
`ArithmeticWindowDigits.dig_mul_rep`, the increment calculations in that
source, and `CompactDummyBound`'s forbidden/ordinary/dummy digit bounds.
The symbolic low mask is the finite-support recipe in
`CompactConcreteMask`: outside its support its digit is `2^67−1`, at an
ordinary support position `2^67−2`, and at special position 1063 it is
`2^67−4`. Thus the intended bounds are respectively 0, 1 and 3. The support
is the displayed finite union **with position 1 removed**; deriving the
exact class at each model index requires a slot-specific model lemma, not
just the existing three-way `model_class`. The origin has its own increment
argument. The retained low-mask byte equality is an external finite check;
its equality to the actual graph port inside the desired arithmetic proof
remains a separate binding obligation.

## From the congruence to a bounded cyclic carry

The retained finite coefficient recipe defines `K = DC + B*DR`, with
`B=2^d` and `DR=2^(67*42)`. If its exact interpretation is established in
`V`, then the exploratory graph congruence would become a congruence for the
static stencil and two shifted contributions to `C`. Prove that equality
and the direction of each cyclic rotation inside the model, for arbitrary
model `N`; do not replace it with a finite check of one standard block.
The recipe/table-to-port equality must also be bound to the particular
retained `K`, rather than inferred from the arbitrary-`K` theorem.

`CompactHeterogeneousCarry.CarryInput` is the nearest existing carry
interface. For a standard finite family of model words `X i`, weights `a i`
and digit caps `D i`, it asks for the word bounds, `F<M`,

```
(∑ i, a i * X i) % M = F % M
(∑ i, a i * D i) + 1 ≤ (b+1) * (2^67 - 1),
```

and the corresponding digit bounds. The actual `X`, `a`, and `D` must be
constructed from the proven coefficient/rotation identity; the exploratory
congruence alone does not instantiate this structure. If the resulting
weighted cap sum is proved at most `3*stencilMass + (2^67−1)`, the finite
`CompactCoefficientMass.heterogeneous_mass_slack` inequality supplies the
numerical `b=1` bound. Its `stencilMass = 29973251816886116` is proved for
the finite Lean table, while its identification with the full retained
stencil is a separate external source interpretation. The heterogeneous
bound is conditional on a correct decomposition; it does not show that a
fractional bit rotation has digits ≤3.

`CompactCarryReset.digit_after_bounded_predecessor` then gives a target
digit equal to its raw weighted column if the explicit `CarryInput`,
predecessor bound, incoming-carry slack and target-column bound all hold.
That reset client currently has only a single-side exploratory compile;
its coherent pair and independent artifact review are still needed.

The external fractional-rotation calculation checks all 590069 shifts for
one standard 8807-slot word with the stated caps, including position 1
zero. It finds a clean target among 4393 and 5495 with predecessor at most
`2^66`; the bound is sharp. It is **not** an all-model rotation theorem and
not evidence that the word came from a graph zero. A model proof must cover
arbitrary `N`, cyclic wrap and fractional shifts, and relate the model slot
caps to those hypotheses. In particular, the attractive stronger bound of
one is false under the caps alone, as the retained finite counterexample
shows. Even a clean column must subsequently be connected to all rows needed
for the computation; selecting one target does not by itself provide that.

## Local decoder and remaining transport

`Compact943Decoder.decode_iff` is the nearest existing local decoder. It
requires a standard family `f : Fin 943 → V` with every `f i ≤ 1`, a model
word `W < 2^41`, and the exact local premise

```
NoCarry ((∑ i, f i) + 2^10 *
  ((∑ i, (2^41 - tileValue i) * f i) + W)) (2^51 - 2).
```

It concludes the stated empty-or-one-selected alternative. The construction
must identify those selector digits and the 41-bit copy value at the correct
cyclic locations, prove their bounds, and identify this exact expression
with the clean graph column. The second saturation no-carry statement and
the high-mask local digits are the natural source of the local premise;
its extraction and the exact offsets must be proved. The 943-row data are
externally bound to the retained JSON; this is not by itself an internal
source-table equality. Finally, local row decoding must be transported across
the model-length word, linked to adjacency and the required initial and
terminal conditions, and translated into the selected consistency statement.
Those are outstanding obligations, not consequences of the finite check or
of this plan.
