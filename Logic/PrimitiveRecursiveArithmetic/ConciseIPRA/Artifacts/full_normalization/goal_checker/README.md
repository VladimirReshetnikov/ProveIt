# Complete goal-directed checker family

The four standalone checkers and their exact certificate contract are described in FORMAT.md.
The primary implementation is code/full_checker.py, with the readable block normalizer.
The alternate code/full_expression_checker.py uses the same three normalization cases in one expression.
code/raw_checker.py and code/zero_checker.py are matched controls authored for this comparison.

Run `python3 reproduce.py` to remeasure the whole programs, regenerate deterministic gzip-9 files,
and replay all positive and negative fixtures in both ordinary and optimized Python.
The script also compares the new shared traversal with the separate forward implementation.
Finite regression tests supplement the mathematical proof and are not a formal verification.

The mathematical calculus has six rules: Hyp, Refl, Tr, QE, DE, DI.
Automatic Hyp/Refl checking does not change that mathematical rule count.
The primitive computation-equation inventory is empty; normalization is inside the trusted code.

The sources under reference are comparison/support material, never imported by a checker.
The inherited ProveIt fixtures and related source are covered by reference/LICENSE-ProveIt.txt.
