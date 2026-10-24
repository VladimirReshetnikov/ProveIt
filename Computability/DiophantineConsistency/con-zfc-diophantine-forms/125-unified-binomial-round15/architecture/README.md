# Unified factorial/product certificate

The main new structural identification is

    factorial binomial = reciprocal CRT product
    B = binom((t!)^2+t,t).

The proposed factorial radius is F^2 rather than F*t^2. The inherited square-output factorial fixed-point theorem then identifies F=t!, while the SAME binomial supplies the product of pairwise-coprime moduli 1+F^2/i. Raw ceiling rows force V<B^2 before either interpretation is known, permitting the pure radix q=(B^K)^K. This removes one exact-binomial graph, one power graph and one independently certified Pell index with no replacement guard.

## Principal endpoints

- unified_derived_cantor/natural: 329 nonnegative unknowns, 253 residuals, degree 4, 12,210 collected terms, height 86,844,780.
- unified_slack_shell/natural: 332 nonnegative unknowns, 255 residuals, degree 4, 14,184 terms, height 10,785,132. Its raw data are the lower-height input for the separately developed integer compiler.
- unified_derived_shell/natural: 331 nonnegative unknowns, 255 residuals, degree 4, 15,769 terms, height 15,246,025; a second integer-compiler input.
- unified_slack_cantor/natural: 331 nonnegative unknowns, 254 residuals, degree 4, 10,785 terms, height 86,453,135; a smaller-support natural companion.
- unified_square_derived_cantor and unified_square_slack_shell use the optional squared radix base q=(N^2)^K. They cost one extra natural variable and row; the pure-base endpoints above are preferred after the signed bootstrap is established separately.

The 329-variable endpoint improves the prior derived349N endpoint simultaneously in variable count (349 to 329), rows (268 to 253), terms (12,768 to 12,210), and height (86,915,503 to 86,844,780). This is a comparison with that pinned parent, not a claim of global optimality. The earlier natural350 slack endpoint, for example, had fewer terms than the natural349 parent.

The square-output fixed point and uniform coefficient bound were already in the incoming Synchronized Exponents/Bootstrap material. UNIFIED_PRODUCT_PROOF.md credits them and supplies all new global composition and bootstrap arguments, plus the full forward/reverse arithmetic proof and exact retained calibration boundary.

## Reproduction

From the round15 directory's parent, run:

    PYTHONDONTWRITEBYTECODE=1 python diophantine_zfc_round15/architecture/reproduce_unified_product.py --output /tmp/unified-replay.json
    PYTHONDONTWRITEBYTECODE=1 python -O diophantine_zfc_round15/architecture/reproduce_unified_product.py --output /tmp/unified-replay-O.json
    PYTHONDONTWRITEBYTECODE=1 python diophantine_zfc_round15/architecture/check_unified_product.py --output /tmp/unified-check.json
    PYTHONDONTWRITEBYTECODE=1 python -O diophantine_zfc_round15/architecture/check_unified_product.py --output /tmp/unified-check-O.json

Reconstruction runs in temporary trees and compares all twelve files of each principal/companion variant byte-for-byte. SOURCE_BINDING.json records the twenty-one imported executable files from the reviewed, unchanged round14 release. New code uses only the standard library; the inherited engine is included in the adjoining intake release. No network or repository mutation is required.

CHECK.json and CHECK_OPTIMIZED.json independently expand every raw and final quartic, check exact counts and unified semantic ports, and run 136,675 positive finite arithmetic checks plus one negative control. The tests include all factorial outputs and nearby candidates at horizons 1 through 32, 132,500 lower-digit coefficient instances and 720 pure-radix bounds. These are regressions, not proofs of an unbounded statement or a decision of consistency.

REPRODUCTION.json and REPRODUCTION_OPTIMIZED.json record successful byte-exact reconstruction. The projection_frontier directory records an additional exact cap sweep; cap32 has 331 variables and 11,209 terms, while caps 64 through 512 yield the same 329-variable polynomial.

## Exact polynomial convention

Every term [c,[i1,...,ik]] is c times the product of the indicated zero-based unknowns, with repeated indices representing powers. The empty list is the constant monomial. The one equation is the sum of the squares of ALL listed residuals. expanded_polynomial.json provides the full collected integer coefficient list. No coefficient ports, unspecified schemata, variable exponents or binomial operations remain in these final ordinary quartics.

The natural-domain endpoint preserves finite refutability. Under the explicit inherited direct C222/ZF/ZFC calibration, ZFC proves its unsolvability equivalent to Con(ZFC). No consistency proof or new complete formal proof-assistant endpoint is claimed.
