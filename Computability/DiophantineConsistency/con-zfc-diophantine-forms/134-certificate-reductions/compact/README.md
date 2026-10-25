# Unscaled ten-positive consistency polynomials

This component supplies two fixed ordinary integer polynomials, each with
ten independent strictly positive integer unknowns. Its main new theorem
recovers a Pell index from partial divisibility, then recovers the full
denominator. It removes the earlier artificial scale mu=q^2+1.

| Literal circuit | Unknowns and domain | Live binary operations | Exact total degree |
|---|---|---:|---:|
| equation78.json | 10 strictly positive integers | 78 | 630 |
| equation79.json | 10 strictly positive integers | 79 | 468 |
| Pinned package 133 parent | 10 strictly positive integers | 84 | 436 |
| Pinned package 133 parent | 10 strictly positive integers | 85 | 328 |

These are reductions in arithmetic cost with a degree increase. They do
not reduce the number of unknowns, and they do not establish a global
optimum. The new ordinary proof composes with the retained indexed
native/refutation calibration to establish the ZFC-provable equivalence
between absence of positive zeros and Con(ZFC). It does not prove either
side separately or assert a new end-to-end proof-assistant certificate.

The complete equation is

    Q*(Z^2-M^2*G*V^2) + (M^2*G-Z^2) = 0.

Every polynomial abbreviation, its domain, the two transport weights, and
both proof directions appear in PROOF.md. The circuit files contain only
binary addition, subtraction, and multiplication; fixed ports are not unknowns.

## Exact files

- **equation78.json**, **equation79.json**: complete arithmetic circuits,
  coordinate order, domain, and coherent four-coefficient binding.
- **PROOF.md**: full new ordinary argument, including the changed index
  deduction, complete positive witness construction, and exact degree proof.
- **section.tex**: the corresponding includable report section.
- **INDEPENDENT_REVIEW.md**: separately performed mathematical review within
  this AI-assisted workflow; not an outside human endorsement.
- **coefficients/beta.bin.gz**, **coefficients/K.bin.gz**,
  **coefficients/MC.bin.gz**, **coefficients/MF_source.bin.gz**: complete fixed
  integers, stored as gzip-compressed unsigned little-endian bytes.
- **rebuild_coefficients.py**: independent finite reconstruction of all four
  integers from the published 436-character code and indexed tile formulas.
- **build.py**: deterministic transformation of the two frozen parent data
  circuits. It does not import or execute upstream programs.
- **verify.py**: independent symbolic cut identities, full leading-form
  propagation, liveness, counts, coefficient-byte verification, and actual
  algebraic corruption controls.
- **CHECK.json**, **CHECK_OPTIMIZED.json**: normal and optimized replay receipts.
- **SOURCE_PINS.json**, **proof_sources/**, **licenses/**, **NOTICE.md**: immutable
  source provenance, inherited ordinary interfaces and their original notices.

The four reconstructed raw hashes agree with the exact indexed tuple of
package 133 at repository commit
1c5367452a0bd4dd7e9e4bceb1508b62dbd2ff61. The fixed payloads have been
deterministically recompressed; the inherited and new gzip hashes are both
recorded, while each raw integer is unchanged. The largest stored port is
592,884 bits. The actual expanded polynomial coefficients can be much larger;
the exact leading forms in the proof exhibit this explicitly.

## Reproduce offline

Python 3.10 or newer with its standard library is sufficient. From this
component directory:

    python3 -B build.py --check
    python3 -B rebuild_coefficients.py
    python3 -B verify.py --output CHECK.json
    python3 -B -O verify.py --output CHECK_OPTIMIZED.json

The two verifier receipts are identical. The checker covers every actual
register through 28 exact polynomial cut identities per circuit and verifies
the full leading forms, with 1,950 and 141 terms. Eight deliberately changed
algebraic circuits are rejected for each endpoint. These finite checks verify
the artifacts and algebra; they do not prove universal nonvanishing by testing
finitely many candidate solutions.

To regenerate the arithmetic circuits, omit --check from the first command.
To regenerate the complete fixed payloads with the prescribed gzip format, use
python3 -B rebuild_coefficients.py --write. Neither step performs machine
simulation or a search for a refutation.

## Inherited proof boundary

The supplied proof_sources/universal_pell.tex contains the exact folding,
rank, fixed-minus parity and auxiliary-completeness lemmas from source 61.
The uniform ratio proof explicitly includes scale one; the source adapter
and indexed calibration documents are also retained. Their upstream paths
and hashes are in SOURCE_PINS.json. The source theorem composes an earlier
native compiler and K215/refutation calibration. This component does not
rebuild every transitive Lean/Rocq dependency; that is a separate
formalization task. No files, branches, or pull requests were changed upstream.
