# Sum-of-squares degree reduction

The 86-operation expression is the product of four integer factors `A`, `L`,
`N`, `S` minus one. Its existing model-uniform factor-unit theorem proves that
any zero has **each** factor equal to one. Hence the 13-variable equation

```
(A - 1)^2 + (L - 1)^2 + (N - 1)^2 + (S - 1)^2 = 0
```

has exactly the same zeros in the arithmetic models in question. Three factors
already have the form `1 + residual`; canceling those additions and
subtractions gives the 87-live-operation graph in `candidate.json`. The four
residuals have degrees 15, 13, 18 and 10, so the resulting polynomial has
exact degree **36**, including after fixing the actual ports and shifting the
unknowns to range over the natural numbers. The only degree-36 contribution is
the square of the degree-18 auxiliary residual; a specific leading coefficient
is a nonzero power of the fixed positive beta. `verify.py` checks the exact
residual polynomials, the circuit wiring and this degree argument. The degree
certificate is an integer-polynomial calculation, not a Lean degree theorem or
a minimality claim.

`AdaptiveDirectOrdinateSquareSums.optimized_zero_iff_original` proves the
same-valuation equivalence for arbitrary integer ports in **every IΣ₁ model**;
`current_zero_iff` includes the fixed ports and the positive shift. The
model-level proof uses signed pairs, so it does not assume that an arbitrary
model is the standard integers. The generated
`AdaptiveDirectOrdinateSquareSumsLiteral.literal_eq_optimized` proves by
reflexivity that the literal 87-gate Lean expression is exactly the optimized
expression. The generating script pins the 86-gate parent, checks every gate
is live, and emits both the JSON graph and the Lean literal.

The model and literal passed two focused, matching [Lean replays](../../reviews/adaptive-square-sums-model-replay/README.md)
against the same matched historical 258-module provider, with selected direct
inputs and companions guarded. Transitive project, package and dynamic ancestry
is inherited; this is not a fully source-current closure. The passage from the model equivalence to a Lean
proof of an iPRA derivation is being assembled; it must be checked separately
before claiming that endpoint. The graph has 13 variables, 87 unshifted binary
operations (48 multiplications, 21 additions, 18 subtractions) and degree 36;
these are distinct metrics and no global minimum is claimed.

The separate [equation36.tex](../../equation36.tex) and
[equation36.pdf](../../equation36.pdf) show the degree-36 equation, the exact
87-gate circuit and the same complete base-10 fixed integer used by the
14-variable page. `verify_display36.py` parses the displayed 24 polynomial
abbreviations and verifies them against the pinned parent graph; it checks the
sum wiring and all rendered gate rows and rejects two controlled mutations.
It does not interpret arbitrary TeX. Both normal Python and `python -O` pass.
Two independent `pdflatex` runs produced identical PDF SHA-256
`c40aad3e0610da92da0d32102f20488eac12dd950cdf3a3e8bc88f263b2f5dd4`;
both pages were visually inspected and the log contained no overfull boxes.
