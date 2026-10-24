# Direct radical majorant: a nine-positive degree record

- One explicitly specified polynomial, nine strictly positive integer unknowns.
- Exact total degree1,158,228;1753 live binary +,-,* operations.
- Replaces source71's final majorant only; retains its complete original31
  native coefficient tuple and source/ratio calibration.
- Degree falls from1,379,730; circuit size rises from478. No minimum claim.

Read PROOF.md and majorant_section.tex. equation9.json is the complete division-free
DAG. data/radical.json lists every coefficient of the new local majorant and
its exact defect. certificates/ contains full shifted positive-coefficient
identities; ordinary expansion verifies them. coefficients/ includes the fixed
integer payloads, finite recipe, and original notices. upstream/ retains the
required comparison/source statements as well as the exact former circuit.

Rebuild the circuit with `python3 build.py`. Recompute the local coefficients
and certificates with `python3 regenerate_majorant.py` (SymPy1.14 or newer).
Run `python3 verify.py` for the integrated finite checks. The mathematical
consistency equivalence relies on the explicitly retained native/refutation
calibration; this is not a new end-to-end Lean or object-languageZFC proof.
