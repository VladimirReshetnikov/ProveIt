# Independent source review: compact 84-to-88 endpoint chain

This is a bounded source/tuple review of
`research/ordinary13-unscale84-compact-chain-draft/`. No Lean, builds, staging,
full provider resolution or axiom command was run. The receipt pins the
source statements and reproduces the author's checker output.

The natural compact tuple used by the draft is, at arbitrary natural K,

```
[CompactFixedBeta.betaNat, K, lowNat, betaNat+highNat].
```

At `fixedK = paramKernel rho`, the cited `CompactSymbolicModelIff.p` source
is the integer cast of that same tuple. Both `portsInt` wrappers inspected in
the bounds and unscaling sources are transparent pointwise natural-to-integer
casts; the proposed `fixed_ports` claims this equality by `rfl`. The source
definitions support the proposed alignment, but this review does not check
Lean's definitional equality or identify the symbolic constants with external
payload/PDF bytes.

The proposed `compact_beta` applies `CompactFixedBeta.bounds` at the positive
model natural J=1 to supply the strict beta premise of the 87/88 bounds
client. For arbitrary K, `positiveBridge87` takes as an **explicit premise**
the 88/30 `PositiveModelBridge` at that very K, and composes the proposed
87↔88 positive-zero equivalence with it. At fixedK, `fixed88Bridge` attempts
to use the existing **uncompiled draft** `P88FourSquareModel.positiveBridge`
at `CompactSymbolicModelIff.p`. The conditional endpoint source then
composes the separate proposed 84↔87 positive-zero equivalence and applies
`IPRAOrdinary12Chain.native_of_positive`.

The final `native84` source statement has no explicit theorem premise and
its exact conclusion is the native-theory derivability of

```
nativeNoZero (positiveShift (Unscale84EndpointDraft.expression84 fixedK))
  ↔ ∼mappedNativeRefutation embedding.
```

That is a *proposed source declaration*, not evidence of an accepted proof.
It inherits all unelaborated graph, root, signed reflection, large-k,
auxiliary-bound and 88/46/free-J endpoint proofs, as well as their model and
compiler providers. It does not by itself identify the mapped refutation with
a separately selected external ZFC encoding, fixed coefficient bytes or the
existing equation PDF. Actual Lean compilation and axiom reports remain open.

There are two separately generated 84 graph namespaces in the surrounding
work: `PositiveUnscale84GraphDraft` in this endpoint and
`PositiveUnscaled84GraphDraft` in the 83→84 proposal. The receipt verifies
that both have the same 84 named JSON rows, inputs, ports and output field;
their structures differ in additional exposed fields. This lexical check
does **not** prove their projected output expressions definitionally equal
or provide a checked bridge between them. That exact interface must be
verified when composing the larger chain.

The previous 88/30 bridge and retained free-J endpoint retain their
independent source-review, author-side history and provider-ancestry limits;
a historical build is not a fresh paired replay of this full chain.

Reproduce from `Computability/DiophantineConsistency`:

```
python3 -I -S -B reviews/ordinary13-unscale84-compact-chain-tuple-independent/check.py
```
