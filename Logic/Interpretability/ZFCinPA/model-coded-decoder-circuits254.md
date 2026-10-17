# Decoding finite constructor circuits at internal inputs

[ModelCodedDecoderCircuits254](Lean/ZFCinPA/ModelCodedDecoderCircuits254.lean)
proves that every fixed finite `ArithmeticTemplates254.Circuit`, evaluated at
arbitrary elements of an IΣ1 model, decodes to its logical interpretation up to
provable equivalence in actual internal ZF and ZFC. This gives a common decoding
lemma for the container clause C, collection clause G, and complete bundle.
The results for those three circuits are equivalences, not proofs of the
set-theoretic clauses.

The interpretation treats an input as its decoded formula, implication as
logical implication, and the literal relative-falsity constant as Bottom.
Membership and equality use the original numeric values of their two children
as variable labels. A universal uses the original numeric value of its left
child as the selected label and interprets its right child as the body. Thus a
literal `one` in label position still denotes label1; interpreting a formula
does not alter any label.

The proof inducts on the external finite circuit. Each input, label and decoded
matrix remains an arbitrary internal object. Implication uses the total
decoder equivalence, including its zero alias. The falsity case uses the
proved negation of decoded1. The universal case transports the body's
equivalence through the actual named binder using target generalization.
Consequently a label0 binder may capture the free variable in decoded1 without
requiring that formula to be syntactically closed. The generic theorem states
the falsity and generalization resources explicitly; actual ZF/ZFC discharge
both. No internal formula is quoted as an ordinary finite formula.

The 102-line source and focused audit passed Lean4.32.0 with seven ordered
axiom reports, ten callers, zero warnings, and only `propext`,
`Classical.choice`, and `Quot.sound`. Source/audit durations were
2.121651s/2.060537s. The audit includes the literal1 in label position, a label0
universal over relative negation, and the all-zero bundle equivalence. That
last equivalence asserts no acceptance of the all-zero triple by the program's
gates.

The first source attempt lacked a local classical decision procedure needed
for the internal theory's ex-falso instance. Adding `classical` inside the
Bottom-equivalence helper resolved elaboration; no statement or compiler
resource limit changed. The original preparation, failed attempt, successful
record and exact source/audit/guard snapshots are retained in the
[history](results/model-coded-decoder-circuits254-history.json). The
[successful verification](results/model-coded-decoder-circuits254-verification.json)
is preserved byte for byte.

The maintained checker is:

```bash
python Logic/Interpretability/ZFCinPA/check_model_coded_decoder_circuits254.py --output /tmp/decoder-circuits-replay
```

It reuses the exact checked rho6 and equality objects, their 40-project and
six-external-boundary closure, and the explicitly recorded Cantor object pair.
The guard verifies compiler/dependency identities, all106 input paths, actual
first providers including Omega, ordered audit results and unchanged fresh
object. It builds no dependencies and downloads nothing. The maintained
`--prepare-only` check performed no Lean proof build; publication did not
repeat the successful proof check.

This removes repeated decoding obligations from fixed templates. Logical
normalization and proofs of C and G, accepted-proof translation, global runtime
and the PA equivalence remain separate obligations.
