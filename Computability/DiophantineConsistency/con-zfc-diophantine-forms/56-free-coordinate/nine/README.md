# A free carrier for a smaller nine-variable consistency equation

The primary polynomial is **`generated/calibrated_absorbed_positive.json`**.
It uses **nine strictly positive integer variables**, has exact total degree
**4,686,812**, and is evaluated by **560 live binary operations**. The variable
order is

    b, g, h, s, w, C, i, j, n.

Start with **PROOF.md** for the complete new mathematical reduction. The
parent report supplied with this component contains its typeset presentation.

The result is a mathematical equivalence: using the identified inherited
compiler/calibration theorem and the numerical Jones ratio theorems, the
polynomial has a positive integer zero exactly when the fixed syntactic ZFC
proof calculus has a finite refutation. Hence the absence of positive zeros
is provably equivalent in ZFC to Con(ZFC). Neither consistency nor
inconsistency is assumed or proved. A nine-variable assertion over arbitrary
integers is not made.

## What changed

- **The carrier is an input.** Replace the old derived coordinate
  C=2R+1+bw+phi by an independent positive coordinate. The existing positive
  margin reconstructs the required lower bound on C. The small numerator
  offset (bw)^2 ensures positivity before that margin has been recovered.
- **Delete the unnecessary top bit.** The carry number is now
  R=(S+T)L+L-1-S with L=b B^5741. The exact bit-population threshold is
  N^2, where N=2^16012039 B^2966. No L^2 term is present.
- **Share the source without shifting its targets.** Twenty source rows use
  the shared homogeneous quadratic evaluator; the two targets below twice
  the largest weight are evaluated directly. This hybrid saves 161 gates
  relative to the direct coefficient-term evaluator used by the certificate.
- Combine these changes with the inherited exact quotient absorption and
  near-square majorant, while retaining the complete original package-31
  coefficient tuple.

Against the strongest incoming nine-positive degree point reviewed in
`ZFC_Diophantine_Selective_Quadratic_2026-10-23.zip` (7,344,328 / 738), this
reduces degree by **36.18%** and arithmetic operations by **24.12%**.
The incoming 548-operation form of degree 15,502,748 remains a distinct
tradeoff with fewer operations. No global minimality or new variable-count
record is claimed.

## Presentations

| Circuit | Domain | Exact degree | Operations |
|---|---|---:|---:|
| `calibrated_absorbed_positive.json` | 9 strictly positive integers | 4,686,812 | 560 |
| `calibrated_absorbed_natural.json` | 9 nonnegative integers | 4,686,812 | 567 |
| `calibrated_original_positive.json` | 9 strictly positive integers | 4,686,812 | 562 |
| `calibrated_original_natural.json` | 9 nonnegative integers | 4,686,812 | 571 |

All four paths are under `generated/`. The original-H forms are reference
comparisons; the absorbed positive form is primary. The natural forms are
bijective input-plus-one translations of their positive counterparts.

Named registers are abbreviations, not extra unknowns. Addition, subtraction,
and multiplication each count as one binary operation, including scalar
multiplication and squaring. Fixed powers are expanded into these operations.
Generating the fixed coefficients and integer bit complexity are separate
costs. No variable exponent or unresolved machine index occurs.

The exact leading coefficient under the diagonal input specialization is

    2^94 a^2343092 (a+4)^104 cstar^400,
    a=2^2134940, cstar=2^16012039.

It is strictly positive. The independent degree replay also verifies nonzero
leading residues at the actual fixed coefficients modulo three primes.

## Complete fixed coefficients

`COEFFICIENT_BINDING.json` binds the four original package-31 ports together.
Their compressed payloads are in `coefficients/`; the uncompressed total is
533,099 bytes. MF is the already shifted MF_source port. Do not splice ports
from a different compiler instance.

Every one of the primary evaluator's **15 live fixed leaves** is materialized
under `fixed/`: 4,665,687 raw bytes, 35,486 gzip bytes. `fixed/MANIFEST.json`
specifies the sign-plus-little-endian encoding, bit lengths, and hashes.
`materialize.py` reconstructs these leaves from the complete four-port tuple
and exact recipes. Both fixed powers of two have fixed numerical exponents.

## Offline reproduction

Only Python 3.10 or newer and its standard library are required:

    python3 verify.py

This checks pinned source files, copies the component to a temporary directory,
rebuilds the circuits and all materialized leaves, checks byte identity, and
runs the core auditor both normally and under Python `-O`. The supplied
`VERIFICATION.json` records the completed run. Rebuilding never modifies the
primary JSON or coefficient payloads in the original component.

The core includes independent symbolic reconstruction of all 22 source rows,
71,808 coefficient-extraction interactions, 11,049 generic two-block carry
cases, 33 exact threshold calibrations, norm/majorant identities, live-gate
counts, actual-coefficient leading-form checks, and 1,200 full modular
comparisons between the hybrid, direct, and cancellation-resolved circuits.
Finite cases and modular replays are diagnostics; the universal mathematical
argument is in PROOF.md and the identified inherited theorems.

For a modular evaluation of the actual primary polynomial:

    python3 evaluate.py --modulus 1000003 1 1 1 1 1 1 1 1 1

This example returns residue 2519. A modular zero would not establish an
integer zero. The evaluator does not search for consistency or inconsistency.

To regenerate output deliberately, run `python3 build.py`,
`python3 materialize.py`, and `python3 verify_core.py`; these direct commands
write their documented `generated/` and `fixed/` outputs.

## Files and proof status

- `PROOF.md`: all new source, carrier, quotient, norm, degree, and domain proofs.
- `build.py`, `source_algebra.py`, `circuit.py`: exact polynomial construction.
- `verify_core.py`, `verify.py`: independent arithmetic checks and safe replay.
- `materialize.py`, `evaluate.py`: fixed-value reconstruction and evaluation.
- `generated/`: literal circuits, separate degree-certificate circuits, ledgers,
  exact leading-coefficient data, and the arithmetic audit receipt.
- `upstream/`: byte-preserved source JSON, numerical theorem texts, inherited
  compiler proof, immediate predecessor proofs, and notices.
- `SOURCE_FILES.json`: immutable source-byte hashes and repository provenance.

This is an ordinary mathematical reduction with finite computational
certificates. It is **not** a newly checked end-to-end Lean/Rocq proof of the
explicit native compiler or a derivation exported into the repository's
object-language ZFC calculus. The included Lean files are evidence of the
numerical interface; their external import closure is not packaged as a
standalone Lean build. No such build is claimed.

Preserve LICENSE, NOTICE.md, the coefficient binding, source manifests, and
inherited notices when incorporating the component.
