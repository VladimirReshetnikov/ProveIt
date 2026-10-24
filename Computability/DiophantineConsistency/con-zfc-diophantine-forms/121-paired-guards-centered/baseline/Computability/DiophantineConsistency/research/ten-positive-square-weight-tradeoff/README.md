# Existing-square transport:97 operations/degree368 and102/344

Reuse the existing I2=I*I register in L=I²+b and delete the private kI
multiplication. The complete ten-positive graphs are [zero97.json](zero97.json)
and [direct102.json](direct102.json). This saves one multiplication relative
to the sealed98/360 and103/332 equations, at a higher exact degree.

[PROOF.md](PROOF.md) proves complete ordinary soundness, positive completeness
through nnew=nparent+I(I-k)B, and exact nonzero leading coefficients.
[check.py](check.py) independently checks every literal source row, whole
coherent coefficient payload, actual center/shear and norm polynomial,
liveness/count and leading form. [LEAD.md](LEAD.md) preserves the earlier
unmaterialized research note for provenance.

```sh
python Computability/DiophantineConsistency/research/ten-positive-square-weight-tradeoff/build.py --check
python -O Computability/DiophantineConsistency/research/ten-positive-square-weight-tradeoff/build.py --check
python Computability/DiophantineConsistency/research/ten-positive-square-weight-tradeoff/check.py --output /tmp/square-weight-normal.json
python -O Computability/DiophantineConsistency/research/ten-positive-square-weight-tradeoff/check.py --output /tmp/square-weight-optimized.json
python Computability/DiophantineConsistency/research/ten-positive-square-weight-tradeoff/artifact_checks.py --output /tmp/square-weight-artifacts.json
python -O Computability/DiophantineConsistency/research/ten-positive-square-weight-tradeoff/artifact_checks.py --output /tmp/square-weight-artifacts-optimized.json
```

This separate operation/degree tradeoff changes no canonical page, common
report, frozen endpoint or Lean file. It asserts no positive inverse map
or optimality claim.
