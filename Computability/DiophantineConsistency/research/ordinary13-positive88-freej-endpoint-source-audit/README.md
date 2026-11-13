# 88/30 → 88/46 → retained 87/51: bounded source audit

This audit compares the exact three JSON row lists and the corresponding Lean
source declarations. It does not run Lean, authenticate compiled providers,
prove file semantics, or establish an iPRA endpoint. The deterministic
receipt checks that all literal input, port and operation lines occur in the
three cited source graph definitions and verifies their exact row deltas. This
lexical correspondence is evidence about pinned text, not a kernel-checked
translation or `Expr` equality.

All three graphs use the same 13 witness names and positions, including free
J and the old positive auxiliary coordinate u at position 11. Their four
integer-port positions agree. They share first/main residuals `A0,A1` and the
signed auxiliary and strong factors `Fa,Fs` up to the explicit ring identity
below. There is no witness update in either proposed edge.

## From four residual squares to a paired residual

At one valuation, the 88/30 graph evaluates as

```
A0² + A1² + (Fa−1)² + (Fs−1)²,
```

where its live `g72` equals `Fs−1`. The 88/46 graph evaluates as

```
A0² + A1² + (Fa*Fs−1)².
```

These outputs are not asserted equal as polynomials. In the ordered difference
ring, an 88/30 zero makes all four residuals zero, hence the 88/46 output is
zero. In the reverse direction, an 88/46 zero gives `A0=A1=0` and
`Fa*Fs=1`; the proposed source first sends that zero to the 87/51 graph, then
uses its `FreeJ13.factor_units` and `unit_iff_one` to obtain `Fa=Fs=1` at the
same valuation. `P88FourSquareModel.zero_iff` states this equivalence for
arbitrary integer ports and every IΣ₁ model valuation, with no positivity
hypothesis. Its proof is an unelaborated source proposal.

The abstract assignment `A0=A1=0, Fa=Fs=-1` makes the paired output zero but
the four-square output 8. It is an **abstract factor-value control**, not an
actual graph zero: it demonstrates why an argument needs the specific
negative-unit exclusions, which `FreeJ13.factor_units` claims for actual
parent zeros.

## From paired residual to the retained product

The 87/51 source output is

```
Fs * Fa * (1+A0) * (1+A1) − 1.
```

The literal auxiliary expression is written using `y²−V²`, while both 88
sources use `u*(y+V)` with `y=V+u`. The receipt proves
`(V+u)²−V² = u*((V+u)+V)` in the free integer polynomial ring, so this
local change is valid in every commutative ring.

For an 88/46 zero, nonnegative squares yield `A0=A1=0` and `Fa*Fs=1`; the
87/51 product is then zero. For an 87/51 zero, the existing source
`FreeJ13.factor_units p v` states that all four factors
`1+A0, 1+A1, Fa, Fs` evaluate to one, using the encoded unit exclusions;
that implies the paired output is zero. The proposed
`P88PairModel.zero_iff` states these directions for the same `p` and `v`,
arbitrary integer ports and every intended IΣ₁ model. `FreeJ13.factor_units`
itself is a repository source declaration; the new edge proof is not a
replayed Lean result.

## Exact endpoint and open provider boundary

The retained source `FreeJ13Halt.positive_model_iff` specializes to
`CompactSymbolicModelIff.p` and states that existence of a **positive** zero
of `FreeJ13.graph p` is equivalent, in each intended model, to existence of a
machine-215 halting time. The two draft model files compose their
same-valuation equivalences with that endpoint, yielding proposed
`PositiveModelBridge` statements for their exact 88 graphs at the same
symbolic tuple. The positive-domain restriction enters this endpoint step;
it is not an extra premise of the proposed local `zero_iff` declarations.

The proposed native 88 endpoints conclude precisely

```
nativeTheory ⊢ nativeNoZero (positiveShift expression)
               ↔ ∼mappedNativeRefutation embedding.
```

The sources also state standard-theory and order-erased reference-theory
versions via `IPRAOrdinary12Chain`. The retained `IPRAOrdinary13` source has
the analogous native statement for the **87/51 Lean expression**. Its
historical endpoint record reports author-side successful builds and axiom
reports, explicitly without a paired replay. The new 88 graph/model/endpoint
files are unelaborated drafts; their `#print axioms` commands are not reports
of executed checks. The exact translation from the displayed mapped
refutation to any chosen external ZFC-consistency sentence and the physical
JSON/PDF/byte relationship require their separate source and file bindings.

The bounded provider survey records a historical P72/base route and five
frontier source/object candidates for the 88/46 draft. It is not an actual
future dependency trace, coherent package/dynamic ancestry, collision-proof
88/30 overlay, current disk reservation, or a new paired endpoint replay.
A correct all-model source statement is not a substitute for checking that
its direct and transitive providers and compiler inputs match when built. The
subsequent new 87/36 auxiliary map and the earlier 84/83/81 links also remain
separate unelaborated work.

Reproduce from `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary13-positive88-freej-endpoint-source-audit/check.py
```
