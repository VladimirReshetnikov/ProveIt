# Weak divisibility and shared sign certificates for Diophantine consistency

Research prepared for Vladimir Reshetnikov's ProveIt project, 24 October 2026.
The manuscript and new artifacts were prepared with AI assistance. Separate
mathematical reviews and independently implemented finite checkers are included;
they are not a claim of external peer review or end-to-end formal certification.

## Results

Every variable in the selected equations ranges independently over **all integers**.
For each equation the ordinary mathematical proof, composed with the identified
inherited calibration theorems, establishes

> ZFC proves: the equation has no integer solution if and only if Con(ZFC).

No consistency assumption is used in proving the equivalence. Neither the
manuscript nor the scripts proves either side of the equivalence.

### Small-variable route

| Literal polynomial | Integer variables | Exact total degree | Binary operations |
|---|---:|---:|---:|
| Incoming coprime projection, centered | 11 | 688 | 126 |
| New `integer11_cubic_direct.json` | 11 | 488 | 120 |
| New `integer11_cubic_centered.json` | 11 | 464 | 123 |
| New `integer11_mixed_direct.json` | 11 | 456 | 126 |
| **New `integer11_mixed_centered.json`** | **11** | **416** | **129** |

The principal result reduces degree by 39.53% from the closest inspected incoming
centered equation. The 464/123 companion improves both degree and arithmetic
length. The 456/126 companion reduces degree while preserving operation count.
Operations count all live binary additions, subtractions, and multiplications,
including multiplication by fixed integers and squaring; shared reuse is free.

The six fixed coefficient ports are fully supplied compressed integers. They
are not additional unknowns, symbolic parameters, or integers whose definition
waits for a computation to halt. The actual coefficients are very large.
`norm/coefficients/recipe/` also supplies their finite reconstruction.

The new argument combines weak fifth-power divisibility, a mixed modulus
carrier, coprime fusion, three-adic radical separation, and supported-modulus
interpolation with one fixed strong Pell witness. The degree certificate uses
an exact cancellation and a displayed nonzero leading coefficient at the
authentic fixed tuple. This route retains the repository's native/K215
calibration. It does not use Jones's universal Diophantine expression.

### Direct small-degree route

| Direct quartic | Integer variables | Quadratic residuals | Collected monomials | Coefficient height |
|---|---:|---:|---:|---:|
| Matched incoming derived-label source | 517 | 310 | 6,774 | 3,904,267 |
| **New shared-sign equation** | **478** | **305** | **5,484** | **511,326** |

The exact equation is `P = sum(R_i^2) = 0`, where all 305 quadratic residuals
are listed in `direct/equation.json` and `direct/residuals.txt`. The complete
collected polynomial, with every coefficient, is in
`direct/expanded_polynomial.json`. There are no coefficient ports in this branch.

The direct construction uses the numerical proof calculus C222, with the
inherited proved C222–ZF and ZF–ZFC refutation equivalences. It does not encode
execution of K215 and does not instantiate Jones's universal expression.
Its principal saving comes from recovering signs in the correct order and then
sharing witnesses for pairs of nonnegative quantities with proved positive sums.
A joint guard handles the main Pell base and a nonzero shared ordinate. All
removed coordinates have explicit integral restoration certificates.

These are measured improvements on two identified branches. This release does
not claim a globally simplest equation, a new minimum number of unknowns, or
literature-wide priority for its component methods. The repository already
contains ten-integer constructions. Other quartics make different tradeoffs
between variables, terms, and coefficient size.

## Read first

1. `report.pdf`: the complete research manuscript, including the exact compact
   eleven-variable formula, ordinary soundness and completeness proofs, degree
   certificates, the direct construction, and full scope qualifications.
2. `report.tex` and `direct/section.tex`: editable manuscript source.
3. `norm/MIXED_PROOF.md`, `norm/PROOF.md`, and `direct/PROOF.md`: detailed local proofs.
4. `NOTICE.md`, `SOURCE_SNAPSHOT.json`, and the provenance ledgers: exact sources
   and the boundary between new work and inherited theorems.

## Reproduce the finite checks offline

Use Python 3.9 or later; only the standard library is required. Python 3.12 was
used for the recorded verification. From the extracted archive directory:

```sh
python3 -B verify_all.py
```

The runner first authenticates all manifest-listed files. It then rebuilds every
new circuit and the ten normative direct data files, reconstructs the six large
numerals, runs the separately implemented algebraic audits, and repeats the new
checkers under optimized Python. It checks the manifest again after execution.
The scripts do not search for a solution or simulate a proof-search machine.
The recorded replay receipt uses a core digest that omits itself to avoid a
hash cycle; the final manifest and the verifier still authenticate that receipt.

To save a fresh receipt outside the release directory:

```sh
python3 -B verify_all.py --receipt ../conzfc_replay.json
```

The retained coefficient recipe's original main program explicitly requires
normal Python. That restriction is preserved: the new wrapper launches the
unchanged recipe in a normal child, including when the wrapper runs with `-O`.
All independent new algebraic checkers retain their checks with optimization.
The original recipe's 69,230 basis-convolution checks are replayed normally.

The component commands are:

```sh
python3 -B norm/verify_coefficients.py
python3 -B norm/audit_independent.py
python3 -B -O norm/audit_independent.py
python3 -B direct/build.py --check
python3 -B direct/verify.py
python3 -B -O direct/verify.py
python3 -B direct/independent_guard_audit.py direct
python3 -B -O direct/independent_guard_audit.py direct
```

For a separate reconstruction of the small-variable graphs:

```sh
python3 -B norm/build.py --output-dir ../rebuilt_norm
```

To rebuild the manuscript with a standard TeX installation:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error report.tex
```

The PDF uses standard LaTeX packages listed in the preamble. The supplied PDF
was rendered and visually checked. PDF byte identity is not a mathematical
requirement: TeX versions, font packages, and creation timestamps can differ.

## What the verification proves

The checks establish exact finite claims: data identity, variable closure and
liveness, binary operation counts, all local circuit identities, the full
three-root norm identity, highest-degree certificates, deterministic rebuilds,
integral monic projection identities, guard/frame substitutions, and every
collected coefficient of the quartic. Deliberate circuit corruptions must fail.
Bounded arithmetic controls are labeled diagnostic checks.

The universal Pell theorems, supported-modulus interpolation, arithmetic-source
semantics, and consistency interpretation have ordinary mathematical proofs.
They are not established by sampling or by a successful Python run. Copied Lean
endpoint texts identify inherited proved interfaces, but the full imported Lean
or Rocq dependency closure has not been rebuilt in this release.

## Main file map

| Path | Role |
|---|---|
| `report.tex`, `report.pdf` | Main manuscript |
| `norm/integer11_*.json` | Four literal arithmetic graphs |
| `norm/METRICS.json` | Graph measurements |
| `norm/coefficients/` | Complete fixed numeral tuple and reconstruction recipe |
| `norm/build.py`, `norm/dag.py` | Deterministic graph construction |
| `norm/audit_independent.py` | Separate free-ring and degree audit |
| `norm/verify_coefficients.py` | Authenticated numeral recipe replay |
| `direct/equation.json` | All final quadratic residuals and variable order |
| `direct/expanded_polynomial.json` | Complete expanded quartic |
| `direct/residuals.txt` | Human-readable final residuals |
| `direct/build.py`, `direct/verify.py` | Direct rebuild and independent exact check |
| `direct/independent_guard_audit.py` | Second implementation of guard/frame checks |
| `direct/*certificate.json` | Literal transformation, projection, and translation certificates |
| `inherited/norm/`, `direct/source/` | Scoped inherited proof and source material |
| `verification/` | Recorded release checks and review notes |
| `MANIFEST.json` | SHA-256 and byte size of every released file except itself |

`direct/README.md` describes the sparse polynomial format and evaluation helper.
The historical proof copies may refer to their original repository trees;
those historical paths are not runtime requirements for the delivered checks.

The source snapshot is commit
`45b399ec51dfbecb891dd51d8a9e4b6b7c361ac6` of
[VladimirReshetnikov/ProveIt](https://github.com/VladimirReshetnikov/ProveIt).
All eight incoming archives at that snapshot were inspected. No repository
branch, pull request, or published submission was changed by this work.
