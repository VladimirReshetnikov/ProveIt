# Smaller explicit Diophantine forms for Con(ZFC)

This research supplement supplies fully fixed integer polynomials and positive
systems whose **absence of solutions is provably equivalent in ZFC to Con(ZFC)**.
The complete mathematical specification is in `report.pdf`; its editable source
is `report.tex`, `sections/*.tex`, and `signed10/SIGNED10_SECTION.tex`.

The main new equation has **10 unrestricted integer variables**, an exact degree
of **126496·5^31 + 27064 = 589042901992797851562527064**, and an emitted evaluator
of **1,442 binary operations** (851 multiplications, 566 additions, 25 subtractions).
It instantiates Sun's explicit reduction with the repository's calibrated quartic
and combines three local simplifications: a coprime square merger, a quintic
divisibility merger, and smaller signed weights in the final norm.

The ten-variable theorem is attributed to Sun. This package contributes a literal
Con(ZFC) instance, the three proved simplifications, and reproducible concrete data;
it does not claim a new general ten-unknowns theorem or global optimality.

## Choices by objective

| Construction | Variable domain | Variables | Equations | Exact degree | Binary operations |
|---|---|---:|---:|---:|---:|
| Main `signed10/generated/signed10.json` | All integers | 10 | 1 | 126496·5^31+27064 | **1,442** |
| Independent Jones `signed16/generated/signed16.json` | All integers | 16 | 1 | 813056·5^32+10016 | **1,617** |
| `quartic31/quartic31_system60.json` | Strictly positive integers | 31 | 22 | 2 | **60** |
| `quartic31/quartic31_sos125.json` | Strictly positive integers | 31 | 1 | 4 | **125** |
| `positive12/generated/product108.json` | Strictly positive integers | 12 | 1 | 1081 | **108** |
| `positive12/generated/shifted_system102.json` | Strictly positive integers | 12 | 3 | max 1072 | **102** |

The inherited collection already has nine-variable natural/positive equations,
a 67-operation single equation, and a 59-operation higher-degree system. Those
remain useful and are not displaced at their respective objectives.

## Fixed instance and proof boundary

The upstream source snapshot is **8c6eec9d19ef80538c8e61ff6e0180040583446a** of
[VladimirReshetnikov/ProveIt](https://github.com/VladimirReshetnikov/ProveIt/tree/8c6eec9d19ef80538c8e61ff6e0180040583446a/SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms).

All active new forms use the complete **wang943-mixed-121x8801** native tuple in
`coefficients/COEFFICIENT_BINDING.json`. The four ports must always be rebound
together; `MF_source` already includes the native `B-1` shift. Historical tuples
in source/reference files are inert evidence, not alternate active coefficients.

The largest native port has **1,070,004 bits**, versus **1,958,376** in the compared
packages 25/27. The four raw payloads occupy **533,099 bytes**, versus **977,220**.
These figures concern the native tuple, not the largest coefficient of a fully
expanded high-degree equation. Every other fixed leaf has an explicit bounded
recipe. In particular, no unknown recursively enumerable index is used.

The proof chain is:

1. A zero of the displayed polynomial/system exists exactly when the fixed positive
   quartic has a zero.
2. The compatible native compiler equates that with a blank-input K215 halt.
3. The repository's calibrated K215 endpoint equates that with a finite ZFC
   refutation.
4. Negating gives the required consistency equivalence.

The new proofs are ordinary mathematical proofs plus finite exact transcription
and arithmetic audits. **No new end-to-end Lean or Rocq certificate is claimed.**
Selected existing Lean sources are bundled for review, not as a complete buildable
checkout. The ten-variable route imports Sun's 2026 preprint; the independently
provided sixteen-variable route uses the Jones interface and does not depend on it.

## Reproduce

Python 3.11+ and its standard library suffice for all arithmetic checks:

```sh
python3 verify_all.py
```

The driver verifies source pins, rebuilds the literal coefficient ports, runs the
author and independent audits, and writes `verification/SUMMARY.json`. It can be
run from any current working directory. Python optimization (`-O`) is rejected
because assertions are part of the checks. No network access is needed.

To rebuild the PDF with a standard TeX Live or MiKTeX installation:

```sh
make pdf
```

The scripts and data use paths relative to this directory, so the archive can be
incorporated as a new numbered directory in the ProveIt report collection.
`SOURCE_PINS.json` and the per-directory ledgers record immutable upstream sources.
`SHA256SUMS` records the released artifact bytes. The inherited license and machine
notices are under `licenses/`; `NOTICE.md` describes attribution.

## Primary literature

- J. P. Jones, *Universal Diophantine equation*, JSL 47 (1982), 549–571,
  [doi:10.2307/2273588](https://doi.org/10.2307/2273588).
- Z.-W. Sun, *Further results on Hilbert's Tenth Problem*, Science China Mathematics
  64 (2021), 281–306; [arXiv:1704.03504v7](https://arxiv.org/html/1704.03504v7).
- Z.-W. Sun, *Ten unknowns for Hilbert's tenth problem over the integers*,
  [arXiv:2609.01594v2](https://arxiv.org/html/2609.01594v2), 2026 preprint.

The report identifies the exact imported theorems and proves the new local changes.
