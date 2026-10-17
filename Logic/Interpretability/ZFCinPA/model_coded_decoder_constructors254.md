# Exact internal decoder constructor equations

[`ModelCodedDecoderConstructors254`](Lean/ZFCinPA/ModelCodedDecoderConstructors254.lean)
connects the checked internal decoder to the literal source constructor
expressions `4*P(a,b)+tag`, where P is the actual Cantor pairing. Every input
may be a nonstandard element of an IΣ1 model.

Membership, universal quantification and equality decode exactly to the native
target atom or checked named binder. Implication does so unless both children
are zero. In that case the source constructor is zero and decodes to literal
T0. The unconditional implication theorem states that case split explicitly;
it does not identify T0 with the different syntax tree `T0 → T0`.

The proof uses the exact Cantor zero characterization, quotient/remainder
identities and the previously checked positive decoder recurrence. Source code
1 decodes to membership(0,0). Turning a proof of that formula into target Bottom
still requires a separate ZF irreflexivity proof.

The arithmetic expressions are definitionally the existing represented
constructors, without introducing another encoding. Four audit clients also
use the actual ordinary-Nat names `Code254.wim`, `wel`, `wal` and `weq`.
They do not assert a general numeral-transport theorem for the decoder or
identify the entire decoder with the external syntax implementation.

The [verification](results/model-coded-decoder-constructors254-verification.json)
passes nine ordered axiom reports and twelve callers with the standard three
Lean axioms only and zero warnings. Source and audit took 2.451 and 2.181 seconds
on pinned Lean 4.32.0, with one thread and a 4 GiB limit. The exact 22-project
decoder closure, six external boundaries, actual first Lean/Omega providers,
all 67 inputs and the fresh object are checked. No dependency was built or
downloaded.

Run 1 failed on two ambiguous `zero_div` names; qualifying the arithmetic
lemma fixes them. Run 2 checked the source, but four ordinary-Nat audit clients
needed the existing Foundation numeral bridges for 4, 2 and 3. Run 3 passes
with all theorem statements retained. Failed records and snapshots remain in
the separate [publication record](results/model-coded-decoder-constructors254-publication.json).

The portable checker freezes the final source and audit. Its maintained and
relocated-cache preflights are explicitly unbuilt. Four controls reject Python
`-O`, nonempty output, a wrong first Omega provider and a corrupted isolated
copy of the predecessor object. The original successful verification record
is copied byte for byte.

```sh
python -B Logic/Interpretability/ZFCinPA/check_model_coded_decoder_constructors254.py \
  --dependency-root /path/to/dependency-checkout \
  --decoder-evidence /path/to/decoder/verification.json \
  --output /fresh/external/decoder-constructors
```

Source, audit and predecessor evidence default to the maintained files.
`--decoder-cache` relocates the 22 exact project objects; `--namespace-cache`
supplies the complete Foundation namespace mirror. Existing recorded paths
are used otherwise. `--prepare-only` runs no proof compilation.

These are syntax equations. Translation of the twelve proof rules, including
GEN and the two set-theoretic bundles, and the PA consistency comparison
remain separate.
