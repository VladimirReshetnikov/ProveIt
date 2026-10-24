# Saturated Pell certificates and quotient recovery for Con(ZFC)

Research contribution prepared for Vladimir Reshetnikov's ProveIt repository, 24 October 2026 (UTC).
Reviewed snapshot: `c1a102936aca437e9999530a0111e6ddab56dc6d`.

## Results

The archive contains eight fixed integer-coefficient polynomials. Every named intermediate in the report is an abbreviation, not another existential variable.

| Domain | Unknowns | Exact total degree | Live binary operations | Literal equation |
|---|---:|---:|---:|---|
| Strictly positive integers | 9 | 999,518 | 1,086 | `nine/equations/h1868_complete.json` |
| Strictly positive integers | 9 | 1,474,688 | 449 | `nine/equations/h1868_simple.json` |
| Strictly positive integers | 9 | 1,628,768 | 435 | `nine/equations/compact2082_simple.json` |
| Strictly positive integers | 11 | 213 | 112 | `positive11/p11_positive_degree213.json` |
| Unrestricted integers | 16 | 184 | 135 | `integer/circuits/integer16_degree184.json` |
| Unrestricted integers | 16 | 192 | 134 | `integer/circuits/integer16_degree192.json` |
| Unrestricted integers | 17 | 88 | 114 | `integer/circuits/integer17_degree88.json` |
| Unrestricted integers | 23 | 10 | 131 | `integer/circuits/integer23_degree10.json` |

Operations are live scalar additions, subtractions, and multiplications in the supplied division-free DAG. A square and a scalar multiplication each cost one operation. Shared registers are reused. Fixed coefficient leaves cost zero operations; their separate storage costs and exact bytes are disclosed. This is an arithmetic circuit metric, not bit complexity or a proof of minimality.

The 435-operation construction improves both degree and operation count over the repository's inspected 440-operation, degree-1,845,940 candidate. The degree-999,518 construction improves the inspected incoming nine-positive degree frontier of 1,158,228. The 11-positive construction improves the incoming degree-257 / 114-operation centered equation in both measures, while the incoming degree-277 / 111-operation alternative remains shorter. At degree 88 the integer construction reduces the inspected 19-variable equation to 17 variables, with five more operations. The degree-ten companion reduces 24 variables to 23. All comparisons are to identified pinned inputs, not a claim of historical priority or a global optimum.

## Read first

- `report.pdf` is the integrated 23-page mathematical report.
- `CANDIDATES.json` is the machine-readable eight-equation catalog, including exact variable lists and circuit hashes.
- `report.tex` and the three `section.tex` files are its complete LaTeX sources.
- `nine/certificates/` contains the new ordinary proofs and independent exact algebra audit.
- `positive11/PROOF.md` and `integer/PROOF.md` retain the expanded proof details.
- `PROOF_STATUS.md` identifies the new results, the inherited ordinary theorems, and the formalization boundary.
- `COEFFICIENT_COSTS.json`, each component's coefficient bindings, and actual `.bin.gz` files specify all fixed integer ports. No program-index coefficient is left unspecified.

## The mathematical claim and its boundary

For each displayed polynomial P on its stated domain D, composition with the identified ordinary native/compiler and logical-calibration theorems proves in ZFC

    (there is no x in D with P(x)=0)  iff  Con(ZFC).

Here Con(ZFC) means absence of a finite syntactic refutation in the repository's fixed ZFC calculus. Neither side is asserted unconditionally. The new changes are complete ordinary arithmetic reductions. The older source/compiler and calculus calibration are explicitly inherited; this contribution does not re-prove that entire chain.

The finite Python checks certify literal algebra, source restoration, coefficient bindings, degree attainment, and circuits. They are not proofs of consistency. This archive does not supply a new end-to-end Lean/Rocq theorem or a derivation inside the encoded object-language ZFC calculus. The repository's unresolved formalization obligations are retained in `provenance/OBJECT_ZFC_AT_PIN.md`. An external proof-assistant theorem, an ordinary mathematical proof formalizable in ZFC, and an exported object-language proof are different artifacts.

## Reproduction

Python 3.10 or later is sufficient. All active verifiers use only the standard library. From the root of the extracted archive:

```sh
python3 verify_all.py --both
```

This checks the file manifest and runs five audits in normal and optimized (`-O`) mode. It stores transcripts in `verification/`. The modes run sequentially; independent component audits run concurrently. No verifier attempts a search for an inconsistent ZFC proof.

The literal circuits can also be rebuilt deterministically:

```sh
python3 nine/build.py
python3 positive11/build.py
python3 integer/build.py
```

These builders overwrite only the corresponding generated local circuit/metric files. The nine-positive majorant is defined by the included 333-term table and exact recurrence; `nine/verify_majorant.py` reconstructs and proves the certificate. The retained original31 native coefficient generator lives in `nine/native_original31/`; the integer coefficient recipe is under `integer/coefficients/recipe/`. Historical source files in provenance are evidence and are not additional automatic release commands.

To compile the report, use a standard TeX Live installation:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error report.tex
```

The report uses standard LaTeX packages and no shell escape, external images, or network access.

## Main mechanisms

1. **Positive Pell saturation.** Replace a redundant squared factor of D in the positive ProductPell certificate by a single D. Pairwise coprimality recovers D=d², and the proof-only Pell coordinate i J d C² retains the required divisibility. The incoming round-11 ten-integer work already used the general saturation idea; this contribution transfers and proves it for the positive certificate.
2. **A bound for the whole radical.** An exact polynomial part of sqrt(DFI), multiplied by 1024 C⁵ i and corrected by one monomial, has a shifted defect with 36,309 positive coefficients. This proves the required uniform bound and lowers the full equation's exact degree to 999,518.
3. **Strong Pell growth.** An existing strong witness i grows fast enough that i³+cT supplies the required weight. Centering at two roots gives the degree-213 eleven-positive equation.
4. **Quotient recovery.** Once c divides f²−1 is proved without the deleted congruences, two integer quotient witnesses can be replaced by one.
5. **Separated rational norm.** A weighted two-root norm merges an ordinary square root with a rational Pell root. The identity S²−4A₀=k²−4 proves separation before either omitted root has been recovered; adjacent-coefficient descent restores integrality.

The new results continue to use the established native source calibration. The report explains why a compiler-independent alternative is still research rather than a completed smaller equation.

## Attribution and repository integration

New material is offered under the repository's MIT No Attribution license (`LICENSE`). Inherited licenses and notices are preserved in each component. `NOTICE.md` and `provenance/SOURCES.json` identify the inputs and provenance. The independent mathematical reviews were performed within the AI collaboration and are not external human peer review.

The package can be added as a new research contribution without changing existing certified endpoints. It contains no environment-specific Python dependency installation and no cache files. All fixed constants, source tables, data, and active audit scripts required by the new finite checks are present.
