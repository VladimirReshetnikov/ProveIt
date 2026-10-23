# Smaller explicit Diophantine forms of ZFC consistency

Research synthesis for ProveIt, 22 October 2026.

The main deliverable is [report.pdf](report.pdf), a 20-page manuscript with
complete LaTeX sources. The new reductions give a fixed equation in **12
positive integers** of degree **1081** and **116 binary arithmetic operations**,
and a fixed equation in **24 unrestricted integers** of degree **2432** and
**163 operations**. Shorter three-equation systems are included.
A new parity layout reduces the largest fixed coefficient from 13,201,251
to **9,766,251 bits** while retaining the 943-tile computation language.

For each presentation, ordinary mathematical proofs formalizable in ZFC give

$$
\mathrm{ZFC}\vdash
\bigl(\text{the stated equation or system has no solutions in its stated domain}\bigr)
\longleftrightarrow \operatorname{Con}(\mathrm{ZFC}).
$$

The proof composes the new arithmetic reductions with the inherited inputless
compiler and the exact K215 blank-halting/ZFC-refutation calibration.
It does **not** decide consistency. The new composition has **not** been
formalized or checked end to end in Lean or Rocq.

## Results

Every binary addition, subtraction, and multiplication is counted, including
multiplication by a fixed numeral. A comparison in a system is free under the
repository convention. Circuit intermediates are polynomial abbreviations,
not additional existential variables. The four fixed coefficient ports are
not unknowns.

| Circuit | Domain | Unknowns | Equations | Exact degree or maximum residual degree | Operations |
| --- | --- | ---: | ---: | ---: | ---: |
| `ratio12_product` | Positive integers | 12 | 1 | 1081 | 116 |
| `ratio12_system` | Positive integers | 12 | 3 | 1072 | 111 |
| **`ratio12_system_shifted`** | **Positive integers** | **12** | **3** | **1072** | **110** |
| `integer24_product` | Integers | 24 | 1 | 2432 | 163 |
| `integer24_system` | Integers | 24 | 3 | 2416 | 159 |
| **`integer24_system_shifted`** | **Integers** | **24** | **3** | **2416** | **157** |
| `integer24_sos` | Integers | 24 | 1 | 4832 | 166 |

The recommended systems are the two shifted variants. They replace the old
transport coordinate by `z_old = z + 1` and compare the two terms of the final
norm directly. This shift preserves existence of positive transport
coordinates only after the compiler has been recovered; it is not an
assumption used in the weak bootstrap.

The positive product improves the previously recorded 12-positive-variable
degree 1145 at 123 operations and matches the previous minimum 116 operations
while reducing that circuit's degree from 1353. The integer product improves
variable count, degree, and operations of the listed wave-3 26-integer
products. These are comparisons with the inspected repository family, not
global minimality claims. The retained 67-operation positive equation,
59-operation larger-variable system, low-degree integer forms, and
nine-natural-variable Jones specialization remain useful alternatives.
See [comparison.csv](comparison.csv) and the manuscript for precise scope.

## The three new ingredients

1. **Relative root separation.** The positive reduction proves that the main
   radicand is larger than the first radicand. Comparing their root scales
   removes an unnecessary factor from an earlier separation weight. A
   strengthened inner estimate permits the smaller weight `M = k I^2 + T^2`.

2. **Signed separation and rational Pell saturation.** The integer reduction
   retains the package-21 norm circuit and proves it sound with only six
   guarded positive coordinates. It treats potentially negative weights,
   complex conjugate branches, and the exceptional zero square-scale and
   auxiliary-quotient cases before applying the inherited negative-scale
   exclusion. Six positive surjections, two odd affine maps, and one square
   map give 24 integer unknowns.

3. **Parity-separated copy positions.** The coefficient adapter puts
   temporal copy tests at even native positions and spatial tests at odd
   positions. The within-cell spatial displacement can then be one native
   digit. The whole-cell factor in the transport coefficient remains.
   Carry, arbitrary-rotation alignment, origin, rank adjustment, and
   simultaneous canonical parity are all checked in the proof.

## Exact fixed coefficients

Use the complete tuple referenced by
[coefficients/COEFFICIENT_BINDING.json](coefficients/COEFFICIENT_BINDING.json).
The circuit ports and payloads are:

| Circuit port | Payload | Mathematical value |
| --- | --- | --- |
| `beta` | `beta.bin.gz` | $B-1$ |
| `K0` | `K.bin.gz` | $D_C+B D_R$ |
| `MC` | `MC.bin.gz` | Native low mask |
| `MF` | `MF_source.bin.gz` | Native high mask plus $B-1$ |

Here $B=2^{5^{10}}$ and $D_R=2^{625}$. The manuscript and
[coefficient proof](coefficients/PARITY_COEFFICIENT_PROOF.md) give finite
recipes for every integer. The gzip files decompress to minimal unsigned
little-endian integers, without a header. Their hashes and exact bit lengths
are in the binding. All four raw payloads total 4,882,894 bytes; the four
deterministic gzip files total 19,820 bytes.

The circuit's `MF` is the **shifted** high mask. The population argument in
the proofs uses the **native** high mask, recovered as `MF_source - beta`.
Never combine coefficients from different layouts. Every circuit in this
archive binds all four ports to this one tuple.

## Offline reproduction

Python **3.10 or later**, using only its standard library, is sufficient:

```sh
python3 -B reproduce.py
```

The command regenerates the seven arithmetic circuits, runs their arithmetic
diagnostics and an independent structural audit, reconstructs the coefficient
tuple, and runs the independent coefficient and language checks. It writes
a summary to `verification/REPRODUCTION.json`. The expected metrics are
also recorded in [RESULTS.json](RESULTS.json).

The coefficient replay creates the four raw `.bin` files as reproducible
outputs. The archive stores their complete deterministic `.bin.gz` forms;
raw files are unnecessary for preservation. No network access, computer
algebra system, proof assistant, or attempted simulation until K215 halts
is required.

To rebuild the PDF, use a standard TeX installation with the packages
listed in `report.tex`:

```sh
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

Equivalent convenience targets are `make check` and `make pdf`.
The checksum manifest records the delivered files. Rebuilding the PDF may
change metadata such as its creation time.

## Artifact map

| Path | Contents |
| --- | --- |
| `report.tex` and `*_section.tex` | Full manuscript sources |
| `report.pdf` | Compiled manuscript |
| `arithmetic/` | Seven literal JSON circuits, generators, arithmetic receipts |
| `proofs/` | New proof notes and independent written reviews |
| `coefficients/` | Complete coefficient backend, exact payloads, language data, checks |
| `references/` | Relevant pinned source proofs, baseline circuits, exact Lean endpoint |
| `verification/` | Independent structural audit and reproduction evidence |
| `RESULTS.json`, `comparison.csv` | Machine-readable new metrics and scoped comparisons |
| `licenses/` | Inherited licenses and notices |

## Proof status and dependencies

The finite checks verify the stated finite properties: exact circuit
structure and counts, live inputs and gates, degree upper bounds, tested
norm identities and inverse reconstructions, the transport shifts,
nonvanishing leading-form diagnostics, coefficient byte identities,
carry and rotation support facts, and local control-helix tests.
They do not replace the mathematical proofs of universal soundness or
completeness, and they do not search for a full witness.

Exact degrees are justified by nonzero leading homogeneous forms in the
manuscript, uniformly for the actual fixed positive `beta`. Sample modular
evaluations corroborate those proofs; they are not the proof of exactness.

The work builds on ProveIt snapshot
`a477d0fc8b6feda53796835564a988015e744d4d`:

[Pinned source collection](https://github.com/VladimirReshetnikov/ProveIt/tree/a477d0fc8b6feda53796835564a988015e744d4d/SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms).

The main inherited components are the inputless 67-operation compiler,
ordinary and normalized signed Pell cores, the package-19 Wang943 language,
the package-20 direct root merger, package-21 economical norm evaluation and
saturation, package-22 positive transport shift, package-23 negative odd-scale
exclusion, and the K215 syntactic-refutation endpoint. Source provenance and
references are retained. Independent reviews here are additional work within
the research collaboration, not an external human or proof-assistant
endorsement.

Inherited material retains its supplied licenses and notices. The new
results are presented for review and incorporation into ProveIt.
