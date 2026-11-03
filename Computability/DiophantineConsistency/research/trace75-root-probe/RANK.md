# Trace75 bounded-port natural rank window

`Trace75Rank.graph_rank_window` is Lean checked in every `IΣ₁` model. For
arbitrary natural ports satisfying the following inequalities **in the
model**,

```
31 ≤ beta,    MC < beta,    MF < 2*beta,
```

and for ten positive witnesses at which the Lean trace75 value is zero, it
identifies the signed rank register in the difference ring with the natural
model expression `rankNat`, and proves

```
F+alpha < q,
3*q < rankNat,
rankNat + q³ + q + 1 ≤ q⁴,
2*rankNat < c.
```

K0 (`p 1`) is arbitrary; no equality with either fixed payload is assumed.
The mask/port inequalities are explicit hypotheses, not a fixed-port
specialization. This is a necessary rank window, not main-index equality,
machine halting, trace74 reverse-guard proof, an iPRA theorem, or a formal
JSON/payload binding.

Accepted source `Trace75Rank.lean` SHA-256
`aee450119067ca76ac0f42bc2bcf2505b0cb0615b5aa47a5df086054c8159b75`;
`run-rank-v2.py` accepted `observations/rank-attempt02/`, object
`/tmp/trace75-rank-4hiva0nq/Trace75Rank.olean` SHA-256
`1cc63c96d4f6f59de021d41d8a2b2ac0db544235d6b43cef63be05c47259898b`.
`#print axioms` reports `[propext, Classical.choice, Quot.sound]`.
The initial failed association check is retained. Direct and several nearby
providers are pinned; project/package transitive, historical source/object,
between-stage and dynamic ancestry remain inherited, without a full closure
scan or independent replay.
