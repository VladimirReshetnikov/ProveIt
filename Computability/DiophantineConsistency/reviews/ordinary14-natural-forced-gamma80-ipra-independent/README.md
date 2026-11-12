# Independent source review: natural-80 iPRA endpoint proposal

The [natural-80 endpoint draft](../../research/ordinary14-natural-forced-gamma80-ipra-draft/README.md) proposes the expected selected-port instantiation and correctly directed no-zero transport from its gamma-shift client to the existing natural-81 endpoint draft. The original and independent receipts reproduce. These are bounded source-interface observations, **not** Lean elaboration, an axiom audit, or a proof that an iPRA derivation exists.

The pinned symbolic source defines `p` as the integer cast of the natural tuple `[betaNat, paramKernel rho, lowNat, betaNat+highNat]`. The existing source-only natural82 and strict-K0 drafts propose the required representations of slots 0 and 1; the new endpoint proposes the analogous low and already-shifted high representations for slots 2 and 3. The source-only compact bound draft, instantiated with the beta identity and the fixed masks, proposes `0<beta`, `MC<beta` and `MF<2*beta`; the strict-K0 draft proposes the required `0<K0`. No extra beta shift is applied to the fourth port. These cast and bound proof scripts and all their imported dependencies still require Lean elaboration.

The gamma-shift source proposes `exists zero80 ↔ exists zero81` at related valuations, assuming those four representations and inequalities. An 80 no-zero hypothesis rules out an 81 zero using the reverse witness map `he.mpr`; an 81 no-zero hypothesis rules out an 80 zero using `he.mp`. Those directions match `HAExpressionNoZeroEquiv.SameNoZero`, and its source `bridge` has the orientation used to transfer the proposed natural81 `PolynomialBridge` to the natural80 expression. The witnesses generally differ at gamma; no equality at the same valuation is asserted.

The checker pins 18 sources, checks the selected direct import lines, port declarations and casts, both no-zero directions, and compares all three native, standard and equality-only endpoint target texts with the corresponding natural81 clients. The cited native and standard adapter signatures match the proposed route. The reference adapter produces `erase` of the **whole** native sentence, while the displayed target is written using componentwise erasure; actual Lean must check the intended definitional reduction of the erased logical connectives. No definite source-level direction or selected-import mismatch was found within this bounded inspection.

The source depends transitively on the earlier unelaborated 81/82 and gamma-positivity chains; the predecessor-order hazards documented in those earlier drafts are not repaired merely by this endpoint. Lean must still check the `change`/cast simplifications, implicit model instances, no-zero rewrites, reference erasure reduction, and every provider and imported proof. The seven `#print axioms` commands are present but unexecuted. The symbolic tuple is not identified with mutable external coefficient bytes, graph JSON, or the different Carrier65 PDF by this source.

Run from the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/ordinary14-natural-forced-gamma80-ipra-independent/check.py | cmp - Computability/DiophantineConsistency/reviews/ordinary14-natural-forced-gamma80-ipra-independent/result.json
```
