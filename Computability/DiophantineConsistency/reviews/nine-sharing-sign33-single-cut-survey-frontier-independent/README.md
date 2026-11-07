# Independent single-cut syntactic survey review

`python3 -I -S -B check.py` reproduces the result, independently computing substituted degrees by a variable-weight recursion rather than the author's AST reconstruction. All 19 displayed positive or signed cuts are covered exactly once, at full coordinates 15 through 33. Eleven have maximum remaining residual syntactic degree 3 and eight degree 4. The full per-gate results match the pinned author output.

This only analyzes the specified residuals and their literal single-cut substitutions. Recursive AST degree is an upper bound and may overestimate the polynomial degree after cancellation; no lower bound, other encoding, natural-witness sign condition, Lean bridge or global impossibility follows.
