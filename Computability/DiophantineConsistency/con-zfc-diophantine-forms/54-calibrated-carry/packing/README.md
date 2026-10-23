# Independently verified selective-source packing

Main deliverables:
- `CERTIFICATE_170_selective12_packed.json`: W170,c169,D4085,K4425. Its odd-threshold composition gives the smallest retained final degree.
- `CERTIFICATE_174_selective12_packed.json`: W174,c81,D4072,K4420,Hmax4276, retained comparison.
- `CERTIFICATE_170_selective12_packed_shifted.json`: W170,c169,D4086,K4426,Hmax4292,minH340. Ready for shared homogeneous evaluation.
- `CERTIFICATE_163_selective12_regular.json`: W163,c0,D7194,K7520. A small-width operation-oriented comparison.

All nine certificate variants are frozen. `SUMMARY.json` records the complete
family, hashes, leading coefficients, row signs, sparse-padding headroom,
and the calibrated source exponent E=Kcode+W+2. Actual circuit operation
counts are to be evaluated by the downstream arithmetic builders, not inferred
from the packing degree alone.

The new source has only109 records and62 active monomials after12 justified
coordinate shifts. A new row-orientation freedom avoids reserving row5 last:
any highest source term with a nonzero integer coefficient may be made positive
by reversing its residual row. Neither main packed certificate needs a sign
change; comparison certificates exercise and verify the generality.

`PROOF.md` contains extraction, coefficient, positivity, completeness, and
packing arguments. `section.tex` is a concise report-ready section.
`data/source_system60.json` is the original pinned inert gate data;
`data/selective12_source.json` records the selectively shifted rows.
The positivity-recovery equivalence itself is proved separately in the
source component's `SELECTIVE_POSITIVITY_PROOF.md`.

Reproduce all finite checks with standard-library Python only:

    python3 verify_certificates.py

The independent verifier reconstructs all source polynomials from the original
60-gate input and checks 57552 exact record/expansion pairs per certificate.
The output is `VERIFICATION.json`. It does not import or execute any optimizer,
serializer, symbolic library, or upstream script.

`build_certificates.py` is an optional SymPy serializer. C++ optimizers and
text outputs are optional provenance only. The original search label `packed165.txt` normalizes to W163; the release
provides canonical `packed163.txt`, `packed170.txt`, and `packed174.txt` inputs. Search has stopped after a verified
improvement; neither numerical optimality nor new end-to-end formalization of
the inherited Con(ZFC) dependency chain is asserted.
