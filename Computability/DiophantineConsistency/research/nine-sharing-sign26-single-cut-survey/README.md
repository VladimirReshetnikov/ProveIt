# Sign26 literal single-cut syntactic survey

This source-only survey scans the pinned external sign26 seed's 11 residuals of literal form `variable − expression`. For each, it drops that row and uses the syntactic degree of the right side as that coordinate's weight in every remaining AST. The maximum resulting syntactic degree is 4 for q3, Y, ell, Delta and V2minusY2; 5 for kY and cTminusR; 6 for E and tau; and 7 for normalized_S. Result details identify affected rows. Port constants have weight zero; variables have weight one.

These are syntactic upper degrees before cancellation or any congruence with other residuals. The screen does not prove the expanded degrees are exact, does not show nonnegativity/natural representability of signed cuts, and does not rule out a 25-witness sextic construction. A potential nonlocal avenue is to express tau through cTminusR and their quadratic difference, then seek a congruence to reduce the square appearing in N0; no such congruence is supplied here. No Lean theorem or endpoint follows.

Reproduce from the repository's `Computability/DiophantineConsistency` directory with `python3 -I -S -B research/nine-sharing-sign26-single-cut-survey/survey.py` and compare stdout with `result.json`. The script pins the exact external seed bytes. Independent audit requested.

Independent audit: `reviews/nine-sharing-sign26-single-cut-frontier-independent/`. Packet is frozen.
