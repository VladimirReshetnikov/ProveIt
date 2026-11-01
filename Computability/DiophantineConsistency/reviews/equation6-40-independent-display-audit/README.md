# Independent audit of the 40-variable degree-six display

`run_audit.py` ran five checks on recorded input hashes. `audit.py` uses a
separate tokenizer and sparse-polynomial implementation to compare all 44
displayed definitions, including all 27 residuals, with the pinned 160-gate
candidate in 44 independent symbols. It checks all 40 variable names and
positions, four port positions, complete raw sum wiring, all 160 printed
evaluator rows and all 160 Lean-literal rows. It rejects two corrupted raw
sums. `evaluate_samples.py` checks the definitions on 25 deterministic
assignments with seeds 80231 through 80255.

`check_generator.py` reproduces the TeX byte-for-byte in a temporary copy.
`check_verifier.py` confirms that the shipped verifier rejects both a bare
residual-alias spoof and an extra term outside the split environment.
`check_pdf.py` rebuilds the PDF byte-for-byte; the local TeX run has no
overfull boxes and seven font-substitution warning lines. Both final PDF pages
were visually inspected. A separate comparison with `equation6.tex` found the
same font substitutions in the 42-variable predecessor: three Computer Modern
shapes requested at 4.3pt and 3.84999pt are substituted with 5pt, plus a
summary warning of maximum difference 1.15001pt.

This checks the displayed equation and local reproduction. It does not
independently authenticate historical Lean object ancestry or prove the
separate identification of the mapped refutation predicate with Con(ZFC).
