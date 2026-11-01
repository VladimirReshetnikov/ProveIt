# Independent audit of the 47-variable quartic display

`run_audit.py` ran five independent checks on the recorded input hashes.
`audit.py` uses a separate tokenizer and sparse-polynomial implementation to
compare all 53 displayed definitions, including all 33 residuals, with the
pinned 179-gate candidate in 51 independent symbols. It checks all 47 variable
names and positions, four port positions, complete raw sum wiring, all 179
printed evaluator rows and all 179 Lean-literal rows. It also rejects two
corrupted raw sums. `evaluate_samples.py` independently checks the definitions
on 25 deterministic assignments, using seeds 80231 through 80255.

`check_generator.py` reproduces the TeX byte-for-byte in a temporary copy.
`check_verifier.py` confirms that the shipped verifier rejects both a bare
residual-alias spoof and an extra term outside the split environment.
`check_pdf.py` independently rebuilds the PDF byte-for-byte; the local TeX run
reported seven font-substitution warning lines and no overfull boxes. Both PDF
pages were visually inspected, including the explicit evaluator column breaks.

This packet checks the displayed equation and local reproduction. It does not
independently authenticate historical Lean object ancestry or prove the
separate identification of the mapped refutation predicate with Con(ZFC).
