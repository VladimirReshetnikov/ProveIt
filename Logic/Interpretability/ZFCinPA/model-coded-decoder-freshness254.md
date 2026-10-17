# Positive formula codes supply their own fresh labels

For every internal source code n, positive internal label c with n ≤ c, and
internal depth d, `ModelCodedDecoderFreshness254` proves that binding label c at
depth d leaves `decode n` unchanged. In particular, every positive code is fresh
for its own decoded formula. This is a theorem in every IΣ1 model, with no
assumption that the code or label is an ordinary natural number.

The proof first establishes that binding two different free labels commutes
when each operation retains its own bound depth. This raw syntax identity is
separate from swapping two quantified slots. Internal Π1 order induction on the
actual source code then uses the strict Cantor-child bounds. At the universal
constructor, commutation moves the fresh binding through the original named
binder and the induction hypothesis applies at the incremented depth. Arbitrary
free parameters are retained throughout.

The literal code-zero decoder is `membership(0,0) → membership(0,0)`, so it
contains free label zero. The theorem includes source zero only when the chosen
label is positive. It does not assert that zero is syntactically closed. The
focus audit includes source0/label1, source1/label1, and arbitrary source n with
label n+1. A direct client proves the decoded implication from a positive coded
formula to its universal closure under its own code, without a target axiom or
GEN premise, using the checked finite vacuity constructor.

The final source and audit passed Lean 4.32.0 with eight ordered axiom reports,
twelve callers, standard axioms only and no warnings. The exact closure reuses
42 source/object-matched project modules and six recorded direct dependency
boundaries. All 109 inputs, actual first providers, Init/Omega and the new object
were checked after compilation. The inherited Cantor pair is exactly the
previously recorded pair; the unused variant remains hashed. No dependencies
were rebuilt or downloaded. The complete Foundation namespace cache is supplied;
its full transitive dependency graph is not independently rebuilt or attested.

One failed source attempt is retained. Its repairs open the existing paired
vector lemma's namespace and reduce tag conditionals explicitly before using
the selected row. The mathematics and theorem statements are unchanged.
A separate preparation failure, before output creation or any proof compilation,
came from a mechanical ancestor-list substitution and is also retained. The
successful verification JSON is byte-for-byte original, separate from history
and publication metadata.

The maintained replay is:

```sh
python3 Logic/Interpretability/ZFCinPA/check_model_coded_decoder_freshness254.py \
  --output /outside/new-empty-directory
```

Explicit repo, dependency root, parent evidence/source/audit, project cache,
Foundation namespace cache, compiler and library paths are supported. A
`--prepare-only` invocation checks and snapshots inputs without compiling proofs;
compiler version discovery may run. No extra negative controls or relocated
replay are claimed for this packet.

This discharges the positive-code freshness condition needed by the numerical
Collection row, which uses its matrix code as its container's variable label.
The internal Collection proof and its special zero-matrix case remain open, as
do the full bundle, both proof translations, and the internal PA endpoint.
