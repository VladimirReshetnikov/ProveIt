# Research status and proof boundaries

## Claims supplied with mathematical proofs

1. The all-shift, all-order rectangular-Schur identity for the c_n(t) family.
2. A universal Toeplitz factorization with a boundary parameter.
3. A general confluent spectral expansion for rectangular Schur polynomials,
   including exact polynomial degrees and nonzero leading coefficients.
4. The exact minimal generic recurrence for the Cigler family.
5. The exact generic generating-numerator degree and reciprocity sign.
6. The period-four signed sequence's exact denominator and numerator symmetry.
7. A sharp fixed-parameter convergence equivalent, locally uniform on (0,1).
8. The reduced-denominator classification at every real parameter.
9. A parity-wise coefficient-unimodality consequence for odd shifts, conditional
   only on the explicitly imported classical Schur-module/SL2 facts.

The article re-proves the previously established parity factors and
coefficient-support properties; these are not listed as novel discoveries.

## What is corrected, not proved as printed

Cigler arXiv:2111.14492v3, equation (85), uses a positive numerator-reciprocity
sign. At shift 4 its own numerator 1-t^3 z^2 transforms to its negative.
For shift 2a the correct sign is (-1)^(a+1). The article also gives the
correct generating function for the period-four signed shift-3 sequence.
It therefore does not claim the literal entirety of printed Conjecture 18.

## Verification actually performed

See `data/verification.json` for ranges. All checks passed:

- 1,092 original-Hankel / Schur integer comparisons;
- 1,092 universal Toeplitz-factorization checks;
- 36 ordinary and 18 period-four signed recurrence/numerator checks;
- 2,052 numerator reciprocity coefficient comparisons;
- 143 exact confluent leading-coefficient comparisons by spectral projection;
- 36 exceptional-parameter checks;
- 56 full polynomial Hankel-Schur identities, with coefficient-shape checks.

The tests are finite and do not prove the theorems for all indices. The PDF
was compiled and rendered for layout inspection. No Lean/Rocq checker and no
independent human referee verified these new proofs in this session.

## Explicit limitations

- Historical priority is not exhaustively established.
- General classical-character factorizations and stretched-Schur recurrence
  existence are not claimed as new.
- Product distinctness is required for the general spectral minimality theorem.
  Node distinctness alone does not imply it.
- Nonreal roots of unity can create spectral cancellations not classified here.
- The fixed-t asymptotic is not uniform up to t=1.
- Ordinary coefficient unimodality is false; even-shift parity-wise
  unimodality is posed as a question, not asserted.
- Not every assertion of the original Conjecture 17 is settled here.
- Repeated-variable spectral coefficients are rational functions; evaluating
  them separately at t=0 or +/-1 is not justified. Use the polynomial identity
  and the separately proved specialized formulas.
