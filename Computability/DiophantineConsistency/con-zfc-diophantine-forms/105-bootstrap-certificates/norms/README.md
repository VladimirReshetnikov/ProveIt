# Exact shorter norm circuits

This supplement contains five literal consistency equations with improved
arithmetic evaluators, a general proof, exact standard-library verification,
and the actual fixed numerical coefficients. It is part of a larger research
iteration; the independent factorial-certificate audit is under `proofs/`.

Start with `PROOF.md`. The most useful new integer tradeoffs are:

- 13 unrestricted integers, degree 1408, 176 operations;
- 13 unrestricted integers, degree 1392, 177 operations;
- 13 unrestricted integers, degree 1072, 186 operations.

The 1088-degree predecessor and the eleven-positive 211-degree/110-operation
companion are supplied as well. Every polynomial is exactly identical to its
specified parent; only its evaluator changes. The parent zero-set theorem
therefore transfers without a new witness reconstruction.

## Run

From this directory, using Python 3.10 or later:

    python3 build_and_check.py
    python3 -O build_and_check.py

No network access, installed mathematics package, or absolute external path
is needed. The supported commands regenerate only this packet's new equation
files and its verification receipts. The retained upstream programs are
mathematical evidence; their historical standalone commands and relative
links are not all supported entrypoints of this smaller supplement.

`SOURCE_PINS.json` records the exact repository snapshot, incoming ZIP hashes
and every retained source file. The verifier checks those pins before using
retained code. The original reanchored builder is retained unchanged; the
adjacent adapted copy changes only its local import path.

## Files

- `norms.py`: division-free cleared three-, four- and five-root norms.
- `build_and_check.py`: complete builders and exact universal checks.
- `equations/`: the five new complete polynomial DAGs.
- `CHECKS.json`, `CHECKS_OPTIMIZED.json`: passed independent-mode receipts.
- `upstream/rootfusion/coefficients/`: six actual fixed integer numerals,
  binding metadata and their finite reconstruction recipe.
- `upstream/positive11/coefficients/`: four actual positive-family numerals;
  their whole-tuple binding is separate from the integer family.
- `upstream/`: retained parent graphs, arithmetic engines, proofs and notices.
- `proofs/factorial_bootstrap_audit.md`: independent audit of the other
  research branch's self-scaled factorial certificate.

All degree statements are inherited exact degrees, preserved by proved
whole-polynomial equality. Operations count each live binary addition,
subtraction and multiplication, including squares and scalar products.
They are not bit-complexity or minimal-circuit claims. No new end-to-end
Lean/Rocq certificate or internal-ZFC derivation is claimed.
