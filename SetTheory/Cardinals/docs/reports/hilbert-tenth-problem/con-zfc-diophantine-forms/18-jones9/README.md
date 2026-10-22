# Explicit Diophantine forms of ZFC consistency: 9, 12 and 27 unknowns

This package combines the exact K215 machine, the native/Pell compiler,
the complete T4 coefficient tuple, the existing 32-variable quartic,
and the constructive Jones nine-variable reduction. It supplies three
complementary constructions, with mathematical proofs and reproducible
finite checks, for incorporation in ProveIt.

**For each stated domain, ZFC proves that absence of a solution is
equivalent to `Con(ZFC)`.** This is an ordinary mathematical result using
the imported compiler and K215 calibration theorems. The new combined
Diophantine endpoint has not been kernel checked in Lean or Rocq.

The comparison and source-acquisition pin is:

`VladimirReshetnikov/ProveIt@f0ae4e0991ca44a7bb4e5671d42e33d775e48035`.

## Start here

- `report.pdf` is the complete paper, with every polynomial definition,
  fixed coefficient recipe, proof, comparison and evidence boundary.
- `report.tex` and its three included section files are the editable source.
- `COEFFICIENT_BINDINGS.json` fixes the actual instance. The four ports in
  every circuit are constants, not existential parameters.
- `MANIFEST.sha256` records checksums for the delivered files.
- `proofs/independent_review.md` records the separate mathematical review.

## Results

Here `N={0,1,2,...}` and `Z>0={1,2,3,...}`. All displayed intermediate
quantities in the paper are abbreviations unless explicitly quantified.

| Construction | Domain | Unknowns | Equations | Exact degree | Binary operations |
|---|---|---:|---:|---:|---:|
| Explicit Jones specialization, new weights | N | 9 | 1 | `161844*5^33+484 = 18841121345758438110351562984` | 20,531 |
| Direct four-root combination | Z>0 | 12 | 1 | 1609 | 151 |
| Direct four-root system | Z>0 | 12 | 3 | 1600 maximum | 147 |
| Signed lower-weight combination | Z | 27 | 1 | 1004 | 137 |
| Signed lower-weight system | Z | 27 | 4 | 952 maximum | 131 |
| Signed full-weight combination | Z | 27 | 1 | 1116 | 136 |
| Signed full-weight system | Z | 27 | 4 | 1064 maximum | 130 |

The nine-variable theorem is a **concrete fixed-instance specialization**,
not a new theorem that recursively enumerable sets admit nine-variable
representations. Its index is fully specified from the supplied quartic.
The new weights reduce this specialization's degree by about 44.46%
relative to the literal source weights, adding seven arithmetic gates.

The direct construction reduces the existing 13-positive-variable family
to 12, at a cost in degree and operations. The signed construction reduces
the existing 29-unrestricted-integer count to 27. None of these claims
asserts a global optimum. The existing 67-operation positive polynomial,
lower-degree systems and 32-variable quartic remain useful alternatives.

Operation counts refer to the supplied shared straight-line circuits:
every binary `+`, `-` and `*`, including a square or a multiplication by
a numeral, is charged. Equality comparisons, shared-register reuse and
fixed coefficient leaves are free. Every fixed power in the nine-variable
DAG is expanded into multiplication gates. These are evaluator counts,
not minimum-circuit proofs. For systems, equality targets need no extra
subtraction gate.

## The actual fixed coefficients

Every circuit is bound to **one whole T4 tuple**. In common notation:

```
beta = B-1
K0   = DC+B*DR
MC   = the T4 complement mask
MF   = MF_native+B-1
B    = 2^(5^18)
```

The shifted `MF` is essential. Circuit aliases `Bm1` and `Kconstant`
mean `beta` and `K0`. The root binding file maps the original T4 metadata
names to these names, including the shifted fourth port. Historical
relative paths inside the unmodified `T4_CONSTANTS.upstream.json` resolve
in its original `upstream/t4/bridge/` layout; use the root binding for
this package's layout.

The ordered tile list has 37,075 entries. Its complete bounded definition
and all coefficients are printed in the paper. No giant integer expansion,
unbounded execution of K215, unspecified recursively enumerable index,
or unknown program parameter is needed to define the polynomial.

The binary expansion of `beta` alone is about 477 billion bytes; the
Jones index constants are larger. Exact recipes, finite coefficient
polynomials and modular evaluators are the intended representation.

## Reproduce the finite arithmetic checks

Python 3.10 or later, standard library only:

JSON exponent, index and degree fields are arbitrary-precision integers.
Use Python's integer-preserving JSON parser or an equivalent parser;
converting those fields to IEEE-754 floating-point values loses information.

```sh
python3 reproduce.py
```

To re-enumerate the complete T4 local language as well:

```sh
python3 reproduce.py --full-t4
```

The default checks authenticate all selected upstream dependencies and
the literal machine-to-transition-JSON binding; regenerate the normalized
quartic, index bound and nine-variable circuits; verify the actual fixed
instance modulo three primes; and regenerate/check the 12- and 27-variable
circuits. Logs and the integrated receipt are written to `verification/`.
The full option invokes the two unchanged upstream T4 checkers in order.
Both options can be invoked by absolute path from another working directory.

Individual commands, from this package root:

```sh
python3 code/build_base.py
python3 code/fixed_coefficients.py
python3 nine/nine_compressor.py base/quartic32.upstream.json nine/generated
python3 nine/check_nine.py base/quartic32.upstream.json nine/generated
python3 nine/verify_fixed_instance.py --package-root . --generated nine/generated --output verification/nine_fixed_instance.json
python3 direct12/algebra12_build.py
python3 direct12/algebra12_verify.py
python3 integer27/build_integer27.py
```

The principal receipts report 346 matching weighted coefficient records,
23 residual majorants, 20 index-bound terms, 24 actual-instance DAG/direct
output comparisons, 840 intermediate comparisons, and exact degree and
operation ledgers. The two mathematical root-combination proofs have
separate identity, inverse-component and degree checks. These checks
support the implementation; they do not decide consistency or replace
the universal compiler and arithmetic proofs.

## Build the paper

With a standard TeX Live installation providing pdfLaTeX, AMS packages,
Latin Modern, `microtype`, `booktabs`, `longtable`, `enumitem`, `xurl`,
`hyperref` and `fancyhdr`:

```sh
make pdf
```

The supplied PDF was compiled and visually inspected. No network is
needed. The source inputs are `nine/nine_section.tex`,
`direct12/section.tex` and `integer27/integer27_section.tex`.

## What the archive certifies and what it does not

The mathematical proof chain is:

```
solution in the stated domain
    iff blank-input K215 halts
    iff there is a finite ZFC derivation of falsity.
```

Negation yields the claimed equivalence. The imported ordinary K215
calibration is explicitly formalizable in ZFC. Existing Lean and Rocq
endpoint records concern the exact machine; they are not a new formal
certificate for this complete Diophantine construction. No internally
encoded ZFC derivation is supplied, and no proof of Con(ZFC) is asserted.

The domain of the nine-variable equation must remain nonnegative;
allowing its final witness to be a negative integer invalidates the
positive-margin argument. The separate 27-variable forms are the
unrestricted-integer results.

`upstream/` is a selected pinned source collection for offline review,
with 27 imported Pell/compiler proof documents, selected Lean definitions,
literal K215 data and notices. It is not the full transitive closure of
the historical projects. See `upstream/SOURCES.json` and its README.

The file manifest identifies the delivered version. Rebuilding the PDF
or rerunning receipts may change build metadata; regenerate the manifest
only when intentionally creating a new release.

## Integration and attribution

Place this directory as a new report package beside the existing wave-2
packages, retaining its relative structure. The main comparison can add
the seven rows above, with the domain and operation conventions intact.
The suggested headline is **explicit 9-natural specialization;
12-positive direct construction; 27-integer signed construction**.

The earlier nine-variable theorem, native compiler, T4 adapter, machine,
ordinary quartic and root-amalgamation sources retain their own credit.
Preserve `NOTICE.md`, `LICENSE`, and the machine-specific notices and
licenses under `upstream/`. No source project is relicensed by this bundle.
