# Fibonacci and Lucas in iPRA (research packet)

- `FibonacciLucasIPRA.tex`: human-readable constructive proof catalogue and formalization plan.
- `FibonacciLucasIPRA.pdf`: compiled eight-page paper.
- `FibonacciLucasSketch.lean`: Lean 4 definitions and COMMENTED proof interfaces; **not typechecked** and **not an iPRA derivation**.
- `check_identities.py`: finite numerical regression checker (not a mathematical proof).

The target is ProveIt's `Logic/PrimitiveRecursiveArithmetic/Derivations` library, with final statements as object-language derivations in `Prf PRAAx`. The proof catalogue currently covers recurrence, addition, matrix laws, Cassini/Catalan/d'Ocagne, Lucas products, finite sums, binomial transforms, formal generating series, parity, divisibility/gcd, modular periodicity, prime-index Lucas congruence, tilings and cycle-independent-set counts. Analytic convergence and deep Diophantine classifications are not claimed.

Build PDF: `pdflatex -interaction=nonstopmode FibonacciLucasIPRA.tex` (run twice for ToC).
Check test: `python3 check_identities.py`.
