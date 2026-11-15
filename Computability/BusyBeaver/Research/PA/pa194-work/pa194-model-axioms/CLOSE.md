# Proof equivalence under model-valued closure

Under the same assumptions as the separately replayed `PA194ReopenProof`—a nonempty candidate-PRA model, IΣ₁ in its induced ordered ring, and an internal Δ₁ source theory—`close_iterated_provable_iff` proves

```
Provable T.theory (modelClose n p) ↔ Provable T.theory p
```

for every model-valued length n and every internally valid arity-zero formula p. Thus n and p may be nonstandard. The new `closeProof` constructs one internal proof of `closeOne p` from an internal proof of p using universal introduction and the inverse-binding equality. `close_iterated_provable` obtains the model-valued-length existential proof by Σ₁ model induction; the converse uses the earlier reopening result.

The result establishes existence of internal proof codes in each model, not a parameter-free graph for an explicit iterated code transformer and not a native iPRA derivation. It does not prove ordinal induction or translate arbitrary PA proofs.

`Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-axioms/check-close.sh "$REPO" FRESH_OUTPUT` compiles this source against the source-replayed `/dev/shm/pa194-reopen-proof-repo` and its prebuilt transitive dependencies. It checks the source and immediate dependency hashes, and four axiom reports. The passing output is `/dev/shm/pa194-close-proof-replay`; log `/tmp/pa194-close-proof-replay.log`.
