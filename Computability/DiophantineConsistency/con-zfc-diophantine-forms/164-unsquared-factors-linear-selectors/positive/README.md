# Inverse-Lucas correction: ten-positive degree 304 in 85 operations

The new principal improves the newest inspected **87-operation/degree-304**
Lucas correction by two multiplications. This is a new polynomial and a new
proof, not merely a different evaluator for the same polynomial.

| Literal graph | Fixed tuple | Live binary operations | Exact degree | Role |
|---|---|---:|---:|---|
| `equation_bV.json` | whole indexed radix67 | 85 | 304 | principal |
| `radix47/equation_bV.json` | whole complemented radix47 | 85 | 304 | smaller supplied ports |
| `equation_V2.json` | whole indexed radix67 | 84 | 410 | dominated control |
| `radix47/equation_V2.json` | whole complemented radix47 | 84 | 410 | dominated control |

Each has ten independently strictly positive integer unknowns. All four
fixed ports are fully supplied, reconstructed and coherently bound. The
whole47 sidecar has largest port 415,904 bits and 207,214 raw coefficient
bytes; the canonical67 tuple has 592,884 bits and 295,388 raw bytes. These
storage gains belong to the incoming encoding and are explicitly reused.

## What is new

Replace the forward correction at R+1 by

    e6=6(k-R-1)-(vk)(k²-4).

The existing ell=vk makes this cheaper and nonnegative correction gives
one signed bootstrap covering all preliminary ranks. The exact inverse
identity recovers the bounded first index modulo q⁴. Full q⁶ recovery would
be false at this stage because of the prime 3; the proof instead projects
with H|6hK, obtains X=2^R and dyadic q, and only then restores q⁶. The new
absolute bounds |rho|<g/3 and kappa+sigma<g/2 complete all ten positive
coordinates without assuming the corrected quotient is nonnegative.

At the named retained native/refutation boundary, ordinary ZFC proves
the absence of a positive zero equivalent to Con(ZFC). No consistency
proof, global minimum or new end-to-end formal-kernel proof is claimed.

Read `PROOF.md`, `radix47/PROOF.md`, and `review/INVERSE_LUCAS_REVIEW.md`.
`report_section.tex` is the article-ready full argument; `coefficients.tex`
and `radix47/coefficients.tex` print both complete finite coefficient recipes.
`report.pdf` is a standalone rendering, with editable `report.tex`.
`PROVENANCE.json` and `SOURCE_PINS.json` identify the current comparison and
the full copied inherited closure. No remote repository was changed.

## Exact offline reproduction

Python 3.10+ and its standard library suffice, from any working directory:

```sh
python3 -B /path/to/positive/build.py --check
python3 -B /path/to/positive/radix47/build.py --check
python3 -B /path/to/positive/verify.py
python3 -O -B /path/to/positive/verify.py
```

The default verification is read-only and includes both tuples. An optional
`--receipt PATH` saves a receipt. Builders without `--check` regenerate their
literal JSON outputs. The independent checker imports no circuit producer:
it proves 37 free-polynomial cuts per graph and complete global leading
forms, checks topology, liveness, all source pins, every fixed coefficient,
the full finite numeral reconstruction, and actual algebraic corruptions.
It rejects 171 mutations per principal and 169 per control. Finite recurrence
controls are expressly diagnostic; the unbounded proof is separate.

On a standard TeX Live installation, `sh build_report.sh` recompiles the
standalone PDF. PDF bytes may vary with TeX metadata and versions; the
literal JSON equations and reconstruction are canonical.
