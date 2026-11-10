DIRECT NATIVE SR CERTIFICATE PRODUCER
====================================

Files
-----
sr_producer.py                 Untrusted named proof-tree constructors and emitter.
../code/checker_sr_bytes.py    Complete measured SR checker used for this replay.
sr_certificates.json           26 complete canonical array/integer proof packets.
../evidence/sr_certificate_receipt.json  Normal and Python -O results.

Run from the archive directory:

    python3 tests/sr_producer.py

The producer imports no checker and no arithmetic evaluator. A finite
normalization request expands to explicit SR computation equations,
congruence, symmetry, and transitivity. Every emitted certificate is then
checked in a fresh process. The standard JSON and Python runtime are the
only dependencies; no network or source repository is needed.

The emitter and named-syntax helpers are adapted from the frozen
generated-assumptions archive tests/producer.py. This SR version changes
the zero computation to successor(seed), derives reflexivity from the
positive constant-update computation R(1,0;const t)=t, and represents a
truthy zero witness by the supported annotated-zero array [0,0] when the
existential coordinate is unused. R and T are the public named constructors;
the internal inherited tree tag 'i' is merely a serialization label.

The retained closed packets include:
  SR0_nonzero_seed                         1 command
  SRS_state_used                          1 command
  SRS_constant_update                     1 command
  SR_actual_atomic_induction              4 commands, with essential IH use
  SR_Q_compound_target                    6 commands
  SR_compound_case_nested_induction       6 commands
  SR_nonvacuous_D_Q_roundtrip              5 commands
  SR_transport_under_Q                    6 commands
  SR_Boolean_decoder_native_CASE         45 commands
  SR_Boolean_decoder_specialization      97 commands
  SR_restricted_Boolean_implication     149 commands

The decoder conclusion is exactly

    Q_x [p2(S(Z(x))) = Z(x)],
    Z(x) = R(x,0;u.0),
    N(x) = Z(R(x,0;u.Z(u))),
    p2(x) = N(S(x)).

The restricted-implication example has a genuinely variable Boolean N(n).
Its native D introduction assumes the shifted antecedent S b=1, applies
the checked Boolean decoder to obtain b=0, and then proves its successor
matrix. No general predecessor or successor-injectivity oracle is used.

Fourteen negative packets reject. They cover the old I0 equation, canonical
falsity, malformed predecessor counters, invalid seeds, future parameters,
failed majors, forbidden compound induction, changing atomic induction to
case mode, removing the implication's required zero antecedent, and a false
successor-shifted decoder target.

All 26 packets were replayed both normally and with Python -O: 52 outcomes
matched their expected verdicts. These are actual native proof certificates
and negative controls. They do not constitute a proof-assistant verification
of the universal Python checker metatheory or the complete P construction.
