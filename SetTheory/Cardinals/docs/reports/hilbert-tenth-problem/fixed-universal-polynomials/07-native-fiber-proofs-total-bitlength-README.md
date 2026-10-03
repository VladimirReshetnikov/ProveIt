# Native total-coordinate-bitlength companion

This small, independently reviewed addendum counts the complete twenty-two-coordinate native fiber by the SUM of the binary bitlengths of its supplied positive coordinates. It assumes the frozen classification in `../entire-fiber/` and uses the hyperbola method from `../second-term/`.

The theorem is in `THEOREM.md`; final-artifact mathematical approval is in `INDEPENDENT-REVIEW.md`. The leading coefficient has denominator 3p−2 in its exceptional baseline term, and is consequently not one third of the previous maximum-height coefficient. The explicit square-root term, O(B^(1/3)) remainder, rounding sandwich, and ranked-total-bit consequence all hold without a smoothing or tie assumption.

## Replay

Python 3 standard library only; no installed package or source checkout is needed. From this directory:

    python3 ../../check_total_bitlength.py
    python3 -O ../../check_total_bitlength.py
    python3 ../../check_total_bitlength_review.py
    python3 -O ../../check_total_bitlength_review.py
    python3 ../../check_provenance.py

Default `../../check_total_bitlength.py` performs exact checks and compares the existing `../../TOTAL-BITLENGTH-RECEIPT.json` without writing. Its optional `--write` mode regenerates only that receipt. The independent reviewer script writes no files. All checks use explicit failures and remain active under Python optimization.

`CHECKS.md` distinguishes exact auxiliary reconstructions, finite-sample threshold checks, and the actual universal proof. Neither checker materializes a padded native tuple, imports upstream code, or claims to exhaust the native fiber. Both upstream frozen packets remain unchanged.

The packet is self-contained for its supporting checks. The mathematical claim remains conditional on the separate frozen classification and its pinned-source provenance, which are not reproduced in full here.
