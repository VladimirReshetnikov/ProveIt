# A 1,690-integer direct Con(ZFC) quartic

This component converts the frozen 1,153-natural-variable shared-frame
equation to an ordinary equation in **1,690 unrestricted integers**. The
polynomial has exact degree **four**, **21,381** nonzero expanded monomials,
and maximum absolute coefficient **2,649,643,805,758**. It is also supplied
as the sum of squares of **842** explicit quadratic residuals.

The proof in `PROOF.md` composes with the parent direct C222 proof-calculus
and shared-Pell-frame theorems to establish, in ZFC, that absence of an
integer solution is equivalent to Con(ZFC). It uses no K215 encoding or
Jones universal polynomial. This is a low-degree direct-calculus endpoint;
it does not improve the variable counts of the repository's much
higher-degree norm equations.

## Files and interpretation

| Path | Meaning |
| --- | --- |
| `source/parent_natural.json` | Frozen 1,153-variable natural parent |
| `input/equation.json` | Safe 2,227-integer checkpoint with 1,379 quadratic rows |
| `input/domain_conversion_certificate.json` | All 795 triangular gate definitions and 358 sign guards |
| `signed_output/equation.json` | Final 1,690-integer equation, represented by 842 squared residuals |
| `signed_output/expanded_polynomial.json` | Complete expanded integer polynomial |
| `signed_output/terminal_elimination_certificate.json` | 537 signed monic elimination steps and reverse restorations |
| `signed_output/INDEPENDENT_INTEGER_AUDIT.json` | Independent domain, projection, expansion and rebuild receipt |
| `signed_output/INDEPENDENT_PROJECTION.json` | Separately run projection checker receipt |
| `section.tex` | LaTeX section for the accompanying paper |

Every sparse term is `[coefficient, monomial]`; a monomial is a sorted list
of zero-based coordinate indices, repetitions mean powers, and `[]` means
the constant monomial. The residual-file equation is exactly the sum of
the squares of its listed residuals. The expanded file lists that same
single polynomial directly. Neither presentation uses variable exponents
or unspecified coefficient ports.

## Reproduce and verify

Python 3.10 or later and its standard library suffice. Commands work
offline and resolve all data paths relative to these scripts. From this
directory:

```sh
python3 verify_integer.py
python3 -O verify_integer.py
python3 verify_integer.py --rebuild
```

The default verification only reads supplied artifacts. `--rebuild` builds
in a temporary directory and compares six primary files byte for byte.
To save a fresh audit receipt explicitly:

```sh
python3 verify_integer.py --rebuild --receipt signed_output/INDEPENDENT_INTEGER_AUDIT.json
```

To regenerate the checkpoint, endpoint and elimination certificate in
place:

```sh
python3 build_integer.py --max-support 16
```

The second independent projection checker can also be run directly:

```sh
python3 verify_projection.py input/equation.json signed_output
```

## Why the integer conversion is safe

Before elimination, every one of the original 358 nongate coordinates x
gets the equation `x=a*a+b*b+c*(c+1)` with three private signed variables.
Its values are exactly the nonnegative integers, by the three-square
theorem. The original 795 arithmetic gates are then nonnegative by
induction through their literal triangular definitions. This gives the
2,227-integer checkpoint without guarding each gate separately.

The subsequent 537 monic substitutions preserve the full signed zero set
with explicit inverse maps. Signed coefficients in those inverse maps are
allowed over Z. All affected sign constraints remain in the substituted
rows; reverse restoration recovers the complete guarded parent before
the original nonnegativity induction is used. Residual degree stays at
most two throughout, so their sum of squares stays quartic.

## Verification boundary and licensing

The independent audit imports no builder or elimination optimizer. It
checks exact conversion rows, all restoration identities and the entire
expanded coefficient dictionary. Both malformed-guard and
malformed-restoration negative controls are included. These are finite
algebraic checks. The parent's proof-calculus calibration and unbounded
Pell arguments are inherited mathematical dependencies, and this
component supplies no new end-to-end Lean/Rocq or object-ZFC proof term.

`SOURCE_PINS.json` authenticates the exact frozen natural parent and
records the optimizer adaptations for signed domains. All necessary data
for this domain conversion and its finite checks are included locally.
The accompanying main package contains the complete parent construction
and its provenance. New code and text follow the ProveIt repository's
MIT No Attribution license, reproduced in `LICENSE`.
