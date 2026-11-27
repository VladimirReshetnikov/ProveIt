# Three extremal problems from the ProveIt Dirichlet GRH program

27 November 2026

Source snapshot: [ProveIt, commit 4f99495218d1a19087deabd8fb5bbb8f5df72a46](https://github.com/VladimirReshetnikov/ProveIt/tree/4f99495218d1a19087deabd8fb5bbb8f5df72a46/Analysis/GeneralizedRiemannHypothesis).

## Papers

| File | Result | Starting point in the article |
|---|---|---|
| `gram/gram.pdf` | For two-row integer matrices with no zero minor, the least normalized Gram determinant is κ(n−1)⁴ + O(n²), where κ has degree 48. All large minimizers use exactly six positive lattice rows and one horizontal direction. | The arithmetic determinant amplification theorem and its question about the minimum, in [src.tex](https://github.com/VladimirReshetnikov/ProveIt/blob/4f99495218d1a19087deabd8fb5bbb8f5df72a46/Analysis/GeneralizedRiemannHypothesis/Article/sections/src.tex#L421). |
| `euler/euler_packet_descent.pdf` | For elementary abelian character groups of odd prime exponent, an exact reduction discards all lower digits of the packet size. Conic and cubic arguments determine the minimum prime density of disagreement in every rank and size at exponents 7 and 11. | The questions about inadmissible leading digits in [rec.tex](https://github.com/VladimirReshetnikov/ProveIt/blob/4f99495218d1a19087deabd8fb5bbb8f5df72a46/Analysis/GeneralizedRiemannHypothesis/Article/sections/rec.tex#L5321). |
| `filters/filter_hessian.pdf` | At a multiple frequency the Hessian of optimal support width in the odd centered polynomial coefficients is strictly totally positive. An explicit seven-frequency family first pays a width penalty at order fourteen. | The splitting theorem in [fil.tex](https://github.com/VladimirReshetnikov/ProveIt/blob/4f99495218d1a19087deabd8fb5bbb8f5df72a46/Analysis/GeneralizedRiemannHypothesis/Article/sections/fil.tex#L343) and the [subsequent sixth-order calculation](https://github.com/VladimirReshetnikov/ProveIt/blob/4f99495218d1a19087deabd8fb5bbb8f5df72a46/Analysis/GeneralizedRiemannHypothesis/docs/incoming/grh_cayley_and_filters.zip). |

The project treats RH and Dirichlet GRH from its pinned upstream Lean development as input. The three mathematical theorems here are unconditional. Applying the filter at Dirichlet zeros uses the common real part of those zeros. The Euler results concern natural density at a fixed character group. All new proofs are given in the papers. The Python programs certify the stated finite subarguments or examples. No Lean formalization of these new results is included. Claims of novelty are relative to the cited results, and publication priority has not been established.

## Rebuild and verify

From the corresponding subdirectory, run pdfLaTeX twice on `gram.tex`, `euler_packet_descent.tex`, or `filter_hessian.tex`. The Gram source inputs `degree.tex` and the supplied vector figure `six_rows.pdf`. The other two manuscripts are single-file TeX sources.

- In `gram/`, run `python3 verify_constant.py` and compare stdout to `constant_verification.json`. It isolates the global one-variable maximum, certifies irreducibility modulo 53, and verifies the field degrees. Run `python3 examples.py` to reproduce `examples.json`. To regenerate the figure, run `python3 make_figure.py` with NumPy and Matplotlib installed.
- In `euler/`, run `python3 check_euler.py` and compare stdout to `check_euler.json`. The check covers the five quadratic cases in the order-eleven proof, explicit attaining examples, and a complete small-rank enumeration.
- In `filters/`, run `python3 check_filter.py` with SymPy installed and compare stdout to `verification.txt`. The script checks the exact covariance integrals and all 119 nonempty minors for ranks 3 through 9.

Python 3.10 or later is sufficient for all three programs. Run with assertions enabled (the default). The JSON and text outputs were replayed during preparation of this archive.
