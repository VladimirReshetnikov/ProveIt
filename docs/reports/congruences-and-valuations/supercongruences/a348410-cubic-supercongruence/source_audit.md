# Source audit — 19 September 2026

## Selected conjecture

**OEIS A348410:** https://oeis.org/A348410

The entry was opened directly. Its formula section attributed to Peter Bala on
21 February 2022 still displayed the prime-power congruence with modulus p^(3r)
for p >= 5 as a conjecture. The coefficient formula and initial values were also
read there. The asserted open status in this package is limited to that inspected
record; a search cannot establish exhaustive historical priority.

## Known generating-function work

**Tong Niu:** https://arxiv.org/abs/2605.16553 — version 1, 15 May 2026.

**Helmut Prodinger:** https://arxiv.org/abs/2605.21255 — version 2, 23 May 2026.

These treatments were consulted for the algebraic generating function. Their
results are acknowledged, not claimed as new in the present note. Prodinger's
paper also extracts a recurrence. None of the main congruence proof depends on
these papers. A separately surfaced recurrence-paper search result was not used
as evidence about the supercongruence.

## Framing theorem audit

**L. Felipe Müller:** https://arxiv.org/abs/2104.10754 — version 1, 21 April 2021.

The theorem statements were checked in both the HTML and the actual PDF, including
PDF page 3 (Theorem 1.1) and page 4 (Theorem 1.2). Proposition 5.2(3) supplies the
framing coefficient formula. The quoted version is important: no claim is made
about an uninspected revision or subsequent correction.

The appendix gives an exact counterexample to the explicit all-eligible-primes
conclusion of Theorem 1.1: V(x)=3x/(1-x)+9x^3/(1-x^3) is a rational 2-function
over Q with period 3. Its parameter-1 framing has f(1)=3 and f(5)=13428, whose
difference is 50 modulo 125. The weighted sum in Theorem 1.2 (also 6.2) is
361/16, congruent to 1 modulo 5, for the same input and n=p=5.

The all-prime rational-2 input condition is proved in the appendix by splitting
p=3 from p!=3; it is not inferred merely from a finite test. The arithmetic is
also independently recomputed by the supplied verifier.

This one-prime example does not by itself disprove a different, weaker assertion
allowing unspecified finite prime exceptions or a scalar multiple. The package
carefully limits its criticism to the explicit statements it actually refutes.
The A348410 proof does not use either disputed statement.
