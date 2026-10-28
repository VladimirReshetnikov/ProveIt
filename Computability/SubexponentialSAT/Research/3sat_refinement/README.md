# Refining the October 25, 2026 subexponential SAT algorithm

**Research status:** this package does not establish a better leading worst-case
subexponential exponent. It contains a proved scalar parity replacement, executable
checks of its algebra, and a precisely conditional proposal for a better exponent.
The unproved compact-factorization assumption is stated explicitly in the report.

## Start here

- `3sat_refinement_report.pdf`: complete mathematical report.
- `3sat_refinement_report.tex`: self-contained LaTeX source.
- `code/parity_lift.py`: exact scalar parity coefficients and validation suite.
- `code/weighted_partitions.py`: exact indexing of weighted mode tuples and
  a finite verification of the corresponding grouped summation identity.
- `data/parity_checks.json`, `data/partition_checks.json`: executed validation results.
- `data/source_manifest.json`: pinned upstream sources and hashes.
- `data/research_status.json`: machine-readable distinction between proved results,
  inherited claims, and unproved research assumptions.
- `build_report.py`: rebuild the PDF using pdfLaTeX.
- `verify_package.py`: rerun algebraic checks and check recorded file hashes.
- `SHA256SUMS`: hashes of the deliverables (except this checksum file itself).

The Python programs are small research prototypes, not a complete implementation
of the manuscript's subexponential contraction solver. Their exhaustive paths
are intended only for small finite validation problems.

## Reproduce the checks

Requires Python 3.10 or newer and its standard library only:

```sh
python3 code/parity_lift.py
python3 code/weighted_partitions.py
python3 verify_package.py
```

The fixed default seed is `20261026`. Timing fields describe this small validation
suite and are not SAT performance benchmarks.

## Rebuild the report

Install a TeX distribution with the standard AMS, geometry, booktabs, tabularx,
hyperref, xcolor, microtype, enumitem, fancyvrb, and lmodern packages, then run:

```sh
python3 build_report.py
```

The report uses no generated external figures and no bibliography processor.
The source references are pinned to the inspected GitHub commit
`7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a`.

## Main mathematical conclusions

For sparse degree-k parity tests, replace the truncated-V lift by

    E_i(z) = (1 + product_m (1 - 2m(z))) / 2.

This is an integral polynomial equal to the even-parity indicator on Boolean
inputs. Modulo 2^p, a product of a such factors has no surviving incidence
monomial of degree greater than k(p+a-1). For p=n+1 this is k(n+a),
improving the source's k(2n+a). The arithmetic can use scalar residues, with
no auxiliary length-(n+1) coefficient axis.

The leading dense-input bound remains

    (n+m)^O_k(1) * 2^O_k(n loglog(n) / sqrt(log(n))).

A second application of contraction to compactly indexed mode tuples would,
under the report's unproved factorization assumption and with retuned
preprocessing, yield the proposed stronger bound

    (n+m)^O_k(1) * 2^O_k(n (loglog(n))^(3/2) / log(n)).

The required factorization is not supplied by this package. Compacting index
strings alone is insufficient, because the resulting group tensors have too
many incident wires. This gap is the central research target.

## Attribution and scope

The baseline algorithm and contraction theorem are due to the referenced OpenAI
preprint. This report is an analysis prepared with ChatGPT for Vladimir
Reshetnikov, dated October 26, 2026. The elementary parity identity is standard;
no broad claim of priority for it is made. Its use here is a concrete replacement
in the inspected reduction. The manuscript's sharper theorem and the weaker
bound described by its Lean scope page are kept separate. No Lean proof was
compiled or certified during this work.
