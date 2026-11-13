# Focused 67/106 all-model and iPRA endpoint check

This client imports only the independently replayed historical stage-079
`ModelCarrierCurrent` provider and asks Lean to check the types and report
the axioms of three existing declarations:

- `sameZero106`: in every model of `IΣ₁`, the positively shifted 67/106
  expression and the maintained current14 expression have the same zeros
  at the same model valuation;
- `bridge106`: the resulting all-model polynomial bridge; and
- `standard_equivalence106`: standard iPRA derives the equivalence between
  the 67/106 positive-domain no-zero sentence and intuitionistic negation
  of the mapped native ZFC-refutation predicate.

The client has no additional premises. It does not itself prove that the
stored 67-row JSON or a displayed document matches the Lean expression.
The separate `../normalized106-graph-syntax-binding/` packet checks the
JSON/Lean-source expression correspondence externally; the earlier
`../fourteen-normalized-product106/` packet supplies a finite degree and
coefficient audit. None of those checks is a new Lean total-degree proof or
a PDF parsing proof.

The guarded check passed: Lean and runner exit 0, no warnings or `sorryAx`;
each declaration reports only `[propext, Classical.choice, Quot.sound]`.
The run used `-M2800`, 120 seconds, sampled 3.5 GiB process-group RSS and
10 GiB available-memory limits, nice 19 and idle I/O. It took 26.330 seconds;
peak sampled RSS was 2,806,726,656 bytes and minimum available memory was
18,811,355,136 bytes. Outer session 4715 was separately observed to exit 0.

The imported stage-079 object has SHA-256
`79bf09c3051ad06f55abdd511c7310ccd795856f1275b6b23836f8b535e74122`.
The pinned author and independently replayed stage-079 source hash
`f0a4898f545a932b135783799ae0d44179fbcbcb08e5d97eaced4515740e990f`
matches the live source. Its producer receipt and all 360 captured direct,
companion and shadow slots were rechecked before and after this client.
The associated equal-length replay and producer ancestry are retained at
`reviews/nine-variable-ipra-equal-length-stages-77-81-overlap/`.
Transitive, package and dynamic ancestry and sampled monitoring remain
inherited. This uses the coherent historical overlay, **not** the fresh
current14 base; two overlapping base object hashes differ and must not be
mixed without a coherent rebuild or an explicit audited connection.

The new output object is
`/tmp/normalized106-historical-endpoint-priority-check01/Normalized106EndpointCheck.olean`,
SHA-256 `0b0ebabc40c3b716b31656b1c7e4a22928e5017f58296db5e7dcad59f22d93c8`.

| Artifact | SHA-256 |
| --- | --- |
| `Normalized106EndpointCheck.lean` | `f2d1d17416a159be82405a96b0abefb17e2a02a57608fa86f2a2b0f02009a5a6` |
| `check01.py` | `3e20b2e3c13a7bf49840639dd767baaa6ad7f7856f0349b33fc9c18a8392db03` |
| `observations/attempt01/compile.log` | `029eeebcb3b2eff02816593067fb1ee4c5db3d0a98c6c1e63c468d66852a28d3` |
| `observations/attempt01/result.json` | `0f7db0f46fc34fd52ebdac20253f9f22761c0c38ff04fce2241e3d59aa537112` |
| `observations/attempt01/outer-terminal.json` | `3905c27ef88a36e011c1cc402b0420e4c5c7b0e74ad29f347478b49f1b3fe725` |
