# Unrestricted finite global stabilization: audited source packet

## Result

One explicit integer polynomial represents **finite legal global stabilization with unrestricted toppling multiplicities** for the same raw eight-field periodic-plus-finite threshold-six Z³ sandpile input used by the earlier binary certificate.

- **3,262 strictly positive witnesses** and one positive ordinary input
- **Exact degree 18**
- **14,571 binary arithmetic gates**
- **1,897 equations** combined by an explicitly emitted sum of squares
- **117 POWER, 28 Sub, six AND and six SPREAD calls**, all expanded into polynomial equations
- **Independent mathematical and exact-source audits: PASS**, relative to the explicitly inherited constructive Pell characterization of exponentiation

The raw tile remains base 32 with digits 0–5; the raw finite patch remains base 32 with digits 0–15. Two paid SPREADs convert those exact digits into a sufficiently large existential radix `b=32^L`. The interior count mask allows every digit from zero through `b/16−1`. A carry-free balance and least action then certify finite stabilization. No time tableau, bounded time horizon, or binary odometer restriction remains.

The count witness is a finite stabilizing supersolution, which need not be the actual legal odometer. This is an existence theorem for finite global stabilization, not a target-firing theorem, a finite-fold representation, or a real-witness equivalence. It does not represent every other infinite-volume notion of stabilizability. No article or universal-loader reconstruction is included.

## Main artifacts

- `PROOF.md`: full theorem, explicit macros, paid geometry, domain order, carry inequalities, least action, completeness, ledger and scope
- `build_stabilization.py`: newly authored fixed-shape builder
- `evidence/polynomial-dag.json`: authoritative complete arithmetic source
- `evidence/build-receipt.json`: gate, witness and macro ledger
- `check_semantics.py` and `evidence/semantics-receipt.json`: fresh finite regressions
- `math-audit/AUDIT.md`: independent proof audit and finite adversarial checks
- `source-audit/SOURCE_AUDIT.md`: independent exact symbolic source audit
- `source-audit/audit-receipt.json`: every residual, macro interface and exposed port checked, exact degree certificate
- `source-audit/replay-and-mutation-receipt.json`: cross-directory normal/optimized replays and 22 expected mutation rejections
- `evidence/manifest.json`: packet hashes and frozen dependency identifiers

## Reproduction

Run only these newly authored scripts:

    python3 build_stabilization.py --output /tmp/stabilization-replay
    python3 check_semantics.py
    python3 math-audit/check_math.py
    python3 source-audit/run_replay_checks.py

No inherited builder, upstream program, arithmetic schedule or Lean process was imported or executed. The exact source audit reads the expanded JSON as inert formal syntax and independently reconstructs all 1,897 residual polynomials; it does not trust the new macro metadata as its specification.

The authoritative DAG SHA256 is

    8622585bcafaf9b3aee84e12f229beb17a33d27d6f1bf0b6cb6bc956ee4ac759

The explicit inherited POWER dependency is mathlib4 commit `ac77769fabe23cb237559e7f56578dbead91499f`, `Mathlib/NumberTheory/PellMatiyasevic.lean`, theorems `matiyasevic` and `eq_pow_of_pell`, pinned source SHA256 `993760c797ad0ff66fa77064a616fce779550bc745cbf6c44e04f392fd0bed0a`. The audits preserve that dependency rather than claiming to reprove it. The old research packets are unchanged.
