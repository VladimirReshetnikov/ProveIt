# Short positive-variable consistency equations

This directory contains four explicit polynomials over fifteen strictly
positive integer variables, with the complete, fixed package36 coefficient
tuple. Their lack of positive zeros is equivalent to syntactic Con(ZFC),
by the ordinary mathematical arguments in `SQUARED_MODULUS_PROOF.md` and
the identified inherited compiler and Pell results.

| Authoritative circuit | Binary operations | Exact degree | Parent operations / degree |
|---|---:|---:|---:|
| `generated/p66_degree157.json` | 66 | 157 | 67 / 155 |
| `generated/p68_degree113.json` | 68 | 113 | 69 / 111 |
| `generated/p72_degree80.json` | 72 | 80 | 73 / 80 |
| `generated/p74_degree68.json` | 74 | 68 | 75 / 68 |

The common change replaces the old auxiliary quotient expression

    V_old = c(T_old f - 1) - R f^2

with

    V = f^2(cT - R) - c.

The exact polynomial substitution is `T_old = fT`. It removes one binary
operation because `f^2` is already available. Completeness follows from
the strengthened Chebyshev congruence modulo `f^2`, which permits a positive
integer quotient after reconstructing the auxiliary Pell ordinate. The
proof does not claim that every old assignment has `f | T_old`.

## Files and coefficient binding

- `SQUARED_MODULUS_PROOF.md`: the universal reconstruction argument, phase
  `R = 3 (mod 4)`, soundness, completeness, and degree witnesses.
- `build_and_audit.py`: generation and exact symbolic audits of all four circuits.
- `generated/AUDIT.json`: operation counts, full liveness, exact degrees and
  distinguished nonzero leading coefficients.
- `upstream/`: the four exact parent circuits, inherited P67 proof, and Pell
  audit, all authenticated by `SOURCE_PINS.json`.
- `coefficients/`: the complete inherited package36 coefficient compiler,
  materialized integer payloads, literal machine and tile tables, independent
  coefficient audit, mathematical proof, and original sources/notices/licenses.
- `licenses/` and `upstream/PACKAGE36_NOTICE.md`: additional original package notices.
- `NORM_SUFFIX_CSE.md` and `INDEPENDENT_SEPARATOR_REVIEW.md`: related independent
  algebra and finalizer reviews used by the main ten- and nine-variable results.

The four fixed ports are `beta`, `K0`, `MC`, and `MF`. The circuit metadata
binds them, respectively, to package36 payloads `beta`, `K`, `MC`, and
`MF_source` in `coefficients/COEFFICIENT_BINDING.json`. The high-mask payload
`MF_source` already includes the required shift. Use the whole tuple together.
The main archive's ten- and nine-variable circuits use a different tuple.

## Verification

From the archive root, run `python3 verify_all.py`. It runs all builders in
temporary copies and checks that every regenerated protected artifact is
byte-for-byte identical. To regenerate this directory directly, run:

```sh
python3 coefficients/build_coefficients.py
python3 coefficients/audit_coefficients.py
python3 build_and_audit.py
python3 -O build_and_audit.py
```

These direct commands write their documented output files. They require
only the Python standard library. The release receipt was produced with
Python 3.12.14; gzip header behavior can vary across Python versions.

The finite audit establishes the identities, circuit implementations and
degree claims it checks. The consistency equivalence additionally uses
the inherited unbounded mathematical compiler and Pell arguments. This
directory supplies no new end-to-end proof-assistant certificate.
