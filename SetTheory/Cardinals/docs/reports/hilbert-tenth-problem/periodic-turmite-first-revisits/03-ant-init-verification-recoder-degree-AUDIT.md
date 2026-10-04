# Independent degree/SOS addendum audit

Verdict: passed. Frozen raw recoder and addendum sources were preserved.

I source-read ADDENDUM.md and check_degree.py before execution. The proof is correct: only the private growth-Pell equations attain degree six, with leading monomial -w^4 z^2. All other residuals have degree at most four. Thus the SOS degree-twelve part is the sum of the separate w^8 z^4 monomials, each with coefficient one. There are one, seven, or fourteen such terms according to the number of EXP macros. Over the integers, the sum of squared residuals vanishes exactly when every equation holds.

I independently expanded all six literal frozen JSON DAGs using a different monomial representation (variable/exponent tuples rather than repeated variable lists), collected every residual and the full sum of squares, and matched the author's complete polynomial hashes, residual degree distributions, total monomial counts, and degree-twelve terms. This is a direct exact check, not a numerical sample.

Confirmed ledgers:

- EXP: 114 = 46 M + 68 A, 25 positive witnesses
- Forward: 865 = 338 M + 527 A, 196 positive witnesses
- Reverse: 868 = 341 M + 527 A, 196 positive witnesses
- Inline pair: 1738 = 682 M + 1056 A, 392 positive witnesses
- Separate-port pair: 1747 = 685 M + 1062 A, 392 internal positive witnesses
- Positive-port pair: 1748 = 685 M + 1063 A, 392 internal positive witnesses

The naive SOS assembly for E equations adds E multiplications and 2E-1 additions. Hence the inline pair's 228 equations add 683 operations, and the separate-port pair's 231 equations add 692. The assembly introduces no new witnesses. The separate-port conventions remain those of the main audit; free A,B,T or positive A,B,Tplus have not silently been quantified.

The inline-pair SOS has 1877 nonzero monomials after collection and polynomial hash c72894347e3337e7d31cbfd6f60b4fb0dcf7b06b2cd2c3d50796511190ca8422. The separate-port pair has 1892 monomials and hash 20bd02141c21ede431c66048de1ade4c46f4874cac3be064be05931a34661814.

Every free port and positive witness has degree one for this claim. In particular G is a free degree-one port. Substitution G=W^576000, periodic-board equations, endpoint equations, and inherited-history equations are excluded from this degree/count statement. No minimality or optimality is claimed.

The source-reviewed author's checker reproduced its receipt byte for byte in both ordinary and optimized Python. Hash snapshots before and after confirm all addendum and frozen DAG files remained unchanged. No upstream program or Lean source was executed.

Pins:

- Author ADDENDUM.md SHA256 18ff83fb03380703274e9c534148e5a10894b872f4d7119b8686f32b9a9dd2c7
- Author check_degree.py SHA256 93954775af265fad7e7d79e772346387fdb3e5f64c11ae90e7f4e0999fcb90e7
- Own independent code: independent_degree_audit.py
- Full independent result: independent_degree_receipt.json

The own audit script uses verified workspace paths. A relocated release should adapt these explicit paths and rerun it, rather than imply an untested portable execution.
