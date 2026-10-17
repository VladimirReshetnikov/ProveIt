# Finite logical certificates

These artifacts use Python 3 and its standard library. Run the following
commands from this directory:

```sh
python verify_basis.py --mutations
python verify_kbp.py
python verify_ks_countermodel.py
```

The first checker replays 107 attributed schema rows from the public CD254
proof, including every instantiation and modus-ponens edge, and rejects six
deliberate corruptions. The second replays an independently constructed
325-row K, B, Peirce derivation of S and rejects two deliberate corruptions.
The third checks the exact six-element counterinterpretation, including
420 finite conditions and a Peirce instance with undesignated value.

Validation uses explicit exceptions, so it remains active under Python's
`-O` option. The JSON files contain certificates or reference results.
`verify_kbp.py` imports `verify_basis.py` from this directory; neither
checker imports a theorem prover.

Read `THEORY_FINDINGS.md` for formulas, proofs, source pins and limitations.
In particular, the six-element interpretation is for the genuine-bottom
logical calculus. It is not asserted to model the additional set-theoretic
schemata or the numerical falsity alias used by the machine.

`LukasiewiczCertificate.lean` and `TarskiClosedBasis.lean` are proposed
integration adapters. They have **not been compiled**, and their presence
does not certify a successful Lean build. The independent finite replays
described above are the verification performed here.
