# Natural-82: required model-level zero transfer

This is a **source-based plan**, not an elaborated Lean proof. It identifies a concrete route from the proposed natural-82 graph to the existing positive-74 and natural-86 endpoint drafts. Its [bounded receipt](result.json) hashes 16 selected source files and checks named source tokens; it does not check Lean types, proofs, provider coherence, or absence of relevant lemmas elsewhere. The inspected 74 and 86 bridge files themselves are unelaborated proposals. The iPRA endpoint still requires a coherent completed build, axiom review and physical byte/PDF binding.

Subsequent [predecessor source drafts](../ordinary14-natural-forced82-predecessor-draft/README.md)
now propose the partial-shift transport, graph-factor equations and successor
witnesses described below. They remain unelaborated. An
[independent review](../../reviews/ordinary14-natural82-model-transfer-audit-independent/README.md)
checks the cited interfaces and the external partial-shift identity, not the
Lean theorem or the iPRA endpoint.

## Interfaces and the exact remaining premise

For `V` with `ORingStructure V` and `V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁`, let `Z82(v)` abbreviate `InternalZero (P82NaturalForced.graph p).output v`; similarly define `Z86`. In the proposed [natural82 model draft](../ordinary14-natural-forced82-ring-bridge-draft/Natural82Model.lean), `HasThreePredecessors v` means there are `f r y : V` with `v 3=f+1`, `v 8=r+1`, and `v 11=y+1`. The draft explicitly **assumes** the following essential lemma:

```
∀ v : Fin 14 → V, Z82(v) → HasThreePredecessors(v).
```

As written that universally quantified form is too broad to assert without specifying the ports: the intended positive compact beta must be assumed or proved. A suitable generalized premise is `p : Fin 4 → ℤ`, `beta : V`, `(p 0 : DiffRing V)=ι beta`, and `0<beta`; the selected compact tuple then needs its beta-cast and positivity facts. No local use of `K0>=0` or a sign condition on `MC` or `MF` is needed for this predecessor argument. The full inherited positive-74-to-machine bridge may have additional conditions already discharged at its selected symbolic ports.

The draft's arbitrary-commutative-ring identity evaluates 82 at a ring valuation `z` and 86 at `down(z)`, where one is subtracted at slots 3, 8, 11. It imposes **no** positivity, no beta assumption and no model; it is a polynomial comparison at changed valuations, not a same-valuation statement. The model draft then proposes `Z82(v) ↔ Z86(w)` when `v` has precisely those three coordinates equal to the corresponding `w` coordinate plus one and the other coordinates agree. The two existence maps are: increment the three slots of any 86 zero to get an 82 zero; and use the predecessor lemma to map an 82 zero back to an 86 zero. Ring subtraction by itself does not supply natural predecessors. All these declarations are source proposals, not checked theorems.

## A route using the existing 74 own-zero drafts

Define the partially shifted natural valuation `s(v)` by leaving slots 3, 8, 11 unchanged and adding one to the other 11. Over an arbitrary commutative ring, with arbitrary signed ports, prove the all-factor and output identity

```
eval(P82(p), z) = eval(P74(p), s(z)).
```

This is another exact algebraic identity; the three cancellation cuts for the shifted `F`, `h`, and `zeta`/`r0` coordinates need checking in Lean. It can instead be obtained by composing the proposed 82-to-86 identity, the existing source-only 86-to-shifted-74 identity, and compatible valuation arithmetic. With `ModelDifferenceRing.internalZero_iff` and the embedding's preservation of `+1`, it would turn an 82 zero at `v` into a 74 zero at `s(v)`.

The source signatures suggest useful reuse. `FactorResidues74Draft.restricted_residues` supplies the three modulo-four exclusions at any 74 valuation. `OwnZeroProduct74Draft.factor_units_of_zero` then needs beta positive, its cast equation, and positivity only at slots 0, 6 and 7, all of which `s(v)` provides; it does **not** demand that slots 3, 8, or 11 already be positive. It yields, among other results, the natural first-factor equation and positive-unit pair equations for the auxiliary and strong factors. `OwnZeroUnits74Draft.unit_iff_one` proposes conversion of those pair equations to difference-ring evaluation equalities. All these declarations are unelaborated and the proposed use must be type-checked.

The remaining graph-specific model lemmas can then be stated and proved as follows:

1. Evaluate the 74 factors and relate their named fields to the partially shifted valuation. The first-unit equation has the form `r²=ell*(ell+k)+1`, so `r>0` in `V`.
2. Establish `Delta=a²+4a+3>1` in the ordered difference ring, with `a` nonnegative, and interpret the strong-unit equation as `I²=Delta*(f²−1)`. If `f=0`, its right side is negative while the square is nonnegative; hence `f>0`.
3. Interpret the auxiliary unit as `y²−Delta*(f²−1)*(y²−Vroot²)=1`. If `y=0`, it makes `Delta` a unit via `Delta*((f²−1)*Vroot²)=1`, contradicting `Delta>1`. The proposed `DiscreteOrderedRingFacts.eq_one_or_neg_one_of_mul_eq_one` and `ModelDifferenceRing.one_le_of_pos` are potential ingredients, with the latter's natural-model discreteness hypothesis still to discharge.
4. Convert the three strict positivities to explicit successors in `V` using the model's natural predecessor/order facts, proving `HasThreePredecessors`. Check actual required order and subtraction lemmas rather than assuming standard-natural semantics for an arbitrary model.

This reuse avoids reproving the negative-Pell and residue claims from scratch only **if** the cited source drafts elaborate and their assumptions are met. Those arithmetic results already occur in their dependency chain; they are not supplied merely by the graph identity. The positive-to-predecessor maps are constructive arithmetic operations, but this audit does not supply a derivation of them in iPRA.

## Endpoints and direction of transport

For the selected symbolic ports, the zero maps yield, in every relevant model,

```
(∃ v, Z82(v)) ↔ (∃ w, Z86(w)).
```

Each map directly converts a universal no-zero assumption in the opposite direction, giving `HAExpressionNoZeroEquiv.SameNoZero` without requiring a general equivalence `¬∃ ↔ ∀¬` in an intuitionistic object theory. The source declares `bridge` to transport a `PolynomialBridge` across `SameNoZero`; the natural-86 endpoint proposes that bridge using the positive-74 bridge. The source then declares `IPRAExpressionNative.equivalence_of_bridge`, with adapters for the standard and equality-only presentations. These are Lean metatheoretic interfaces; the target object-theory proof-existence claim must be checked from the completed endpoint and axiom closure, not inferred just from this document or from a classical external zero-set argument.

Run from the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/ordinary14-natural82-model-transfer-audit/check.py | cmp - Computability/DiophantineConsistency/research/ordinary14-natural82-model-transfer-audit/result.json
```
