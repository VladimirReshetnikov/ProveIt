# Fourteen positive unknowns by one free scale

This packet supplies an explicit polynomial in **14 strictly positive integer unknowns**, of **exact total degree 30**, evaluated by **87 binary arithmetic operations** (47 multiplications, 24 additions, 16 subtractions). Its five residual equations have degrees 12, 14, 10, 15, 2 and a shared 78-operation evaluator.

This improves the degree of the existing fourteen-positive degree-52/79 point, but increases operation count. It is a Pareto tradeoff, not a claim of global simplicity or minimality. The idea combines one new monic integral-root carrier with the adaptive index absorber. Keeping X=wq is essential: freeing both scales using a single root would not justify their separate divisibilities.

## Files and reproducibility

- `PROOF.md`: complete new mathematical composition, including imported interfaces and proof boundaries.
- `section.tex`: report section suitable for inclusion in the parent report.
- `fourteen_positive_degree30.json`: authoritative polynomial circuit, whose output is a sum of five squares.
- `fourteen_positive_degree30_certificate.json`: algebraically equal circuit displaying the degree cancellations. Its cost is not the primary cost.
- `fourteen_positive_system.json`: five-output system sharing the primary evaluator's 78 live gates.
- `build.py`: deterministic standard-library generator.
- `check.py`: source/payload authentication, exact identities, liveness/counts, literal-expression checks, exact-degree witnesses with actual fixed coefficients.
- `negative_controls.py`: isolated corruption tests.
- `coefficients/`: the whole unchanged Integral Root compact coefficient packet, including four actual little-endian integer payloads in gzip containers. The nested directory preserves upstream relative paths.
- `upstream/`: inherited ordinary compiler, Pell lemmas, root gap and absorber/squared-modulus proofs.
- `SOURCE_PINS.json`: source provenance at arrival 7331974b696693a8eed2aa5f0f64f1c19d9569f0 and placement beb0192cb8dc36f78c369c080f2adfbc1887a486.

From this directory run:

    python3 build.py
    python3 check.py
    python3 -O check.py
    python3 negative_controls.py

No external Python packages are required. The finite replay does not prove the imported compiler, infinite Pell completeness or ZFC calibration. The resulting equivalence is an ordinary mathematical composition using explicitly retained inherited proofs, not a new end-to-end kernel certificate.
