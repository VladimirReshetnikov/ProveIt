# Proposed two-quotient model bridge (source only)

The positive 22-variable, 110-operation, degree-ten graph replaces the two
root variables of the 22/114/10 parent by positive quotients. This packet is
an **unelaborated Lean draft**, not an iPRA proof: neither the generated
sources, the model extraction, nor the conditional endpoint has been run
through Lean. No output here authenticates any imported compiled provider.

`AQ22Quotient110Literal.lean.src` and `AQ22Quotient110Residuals.lean.src`
transcribe the pinned 110-row JSON graph and its 13 ordered residuals. The
source-only `sum_eq_literal` and `all_residuals` declarations express the
sum-of-squares relationship; the Python checker verifies the former only as
finite syntax/DAG equality. `AQ22Quotient110Witness.lean.src` proposes
extracting both parent norm equations and applies the pre-existing
`ArithmeticAdaptiveQuotients2011.scaled_quotient` to each. Parent scale and
root positivity then give positive quotients. The precise parent equations
and quotient witnesses appear in that source. This argument uses no
assumptions about the signs or representation of the four ports.

`AQ22Quotient110ConditionalTransfer.lean.src` proposes projection (replace
slots 18 and 19 by the quotients) and extension (multiply them by scales in
slots 13 and 14). The intended conditional endpoint depends on
`GraphZeroObligations`: **both** zero-preserving directions remain explicit
unproved hypotheses. Under those hypotheses and the proposed quotient lemma,
the draft obtains the positive-shifted no-zero equivalence in all relevant
models, then composes with `IPRAAQ22Native.bridge22`, and finally sketches the
native and standard-theory clients. The 132-operation natural graph has not
been identified by Lean with `positiveShift child`; its separate JSON does not
by itself establish that identification.

The graph author’s checker independently verifies all 13 exact residual
identities as integer polynomials: parent residuals 0 and 1 after extension
are respectively scale-squared times the child residual; residuals 2–12 are
unchanged. Together with both sum-of-squares characterizations, these are the
concrete remaining graph-map proofs. Reverse projection additionally uses the
factorization and two quotient norm equalities. A complete development needs
Lean proofs of those maps, elaboration of all this packet's declarations,
`#print axioms` audits, a coherent replay and imported-provider audit. The
historical parent endpoint has a paired replay; it is not a fresh
replay of the child, and concerns the mapped Foundation sentence; it does not by itself
establish equivalence to an untranslated classical consistency sentence.
See [the historical parent paired result](../../reviews/ipra-aq22-historical-pair-terminal/README.md) and the
[graph analysis](../adaptive-aq22-two-quotients110/README.md).

Reproduce the non-Lean, read-only checks from the DiophantineConsistency
folder:

```
python3 -I -S -B research/adaptive-aq22-quotient110-model-draft/generate.py | cmp - research/adaptive-aq22-quotient110-model-draft/generated.json
python3 -I -S -B research/adaptive-aq22-two-quotients110/check.py | cmp - research/adaptive-aq22-two-quotients110/receipt.json
python3 -I -S -B research/adaptive-aq22-quotient110-model-draft/check.py | cmp - research/adaptive-aq22-quotient110-model-draft/receipt.json
```

The checker pins exact input and draft-source hashes, verifies the witness
replacement and output DAG, searches the bounded draft for proof escapes, and
checks that both conditional obligations and the historical endpoint are
present. It does not prove Lean syntax, tactics, theorem correctness, provider
provenance, or the claimed internal endpoint.
