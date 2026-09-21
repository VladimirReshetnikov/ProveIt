# Source provenance and status

Consultation date: 20 September 2026 (America/Los_Angeles).

## Exact target

Source: https://oeis.org/A001006

The targeted material is the four-part comment attributed to Peter Bala,
dated 10 February 2022, under the heading "Conjectures". It is not the
separate Batalov divisibility conjecture, the Sun sum-integrality conjecture,
or one of the empirical Hankel-transform comments in the same entry.

With M_n denoting A001006, U_n denoting A005717 (extended by U_0=0),
and D_n denoting A005773, the four targets are the following statements:

1. For prime p = 1 (mod 6) and n,r >= 1, M_(n*p^r-2) = -U_(n-1) (mod p).
2. For prime p = 5 (mod 6) and n >= 1, M_(n*p-2) = -D_n (mod p).
3. For prime p >= 3 and k >= 1, M_(n+p^k) = M_n (mod p) for
   0 <= n <= p^k-3.
4. For prime p >= 5 and k >= 2, M_(n+p^k) = M_n (mod p^2) for
   0 <= n <= p^(k-1)-3.

The identities and parameter bounds were checked against the rendered entry.
The comment still used a conjecture label at consultation; that is not a
claim that every consequence lacked a proof somewhere in the literature.

## Auxiliary identifications

* https://oeis.org/A002426 — T_n, central trinomial coefficients.
* https://oeis.org/A005717 — U_n, adjacent trinomial coefficients;
  the OEIS offset begins at one, whereas this article sets U_0=0.
* https://oeis.org/A005773 — D_n; its comment by David Callan dated
  7 February 2004 records the coefficient identity underlying
  D_n=T_(n-1)+U_(n-1) for n >= 1.

## Earlier results relevant to attribution

A001006 includes Rob Burns's comment dated 11 November 2024 explaining
that the n=1 boundary statements are consequences of his 2017 work.
The present note does not present those special cases as new discoveries.

Nadav Kohen, Uniform Recurrence in the Motzkin Numbers and Related
Sequences mod p, arXiv:2403.00149 (2024).
https://arxiv.org/abs/2403.00149
https://arxiv.org/html/2403.00149v1

Nadav Kohen, Density and Symmetry in the Generalized Motzkin Numbers
mod p, arXiv:2411.03681 (2024).
https://arxiv.org/abs/2411.03681
https://arxiv.org/html/2411.03681v1

The latter paper contains the M_(p-2) boundary result (Proposition 6),
the central-trinomial digit rule (Proposition 7), and Motzkin boundary
digit patterns (Proposition 9). These make clear that much of the
prime-modulus material overlaps with already available results. The
article provides a unified proof rather than assigning unsupported priority.

Hao Pan and Zhi-Wei Sun, Supercongruences for central trinomial
coefficients, Frontiers in Combinatorics and Number Theory 2 (2026), 55–62.
https://arxiv.org/abs/2012.05121v3
https://arxiv.org/html/2012.05121v3

First posted 9 December 2020; version 3 dated 13 March 2026. Theorem 1.1
proves that (T_(pn)-T_n)/(pn)^2 is p-adically integral for p>3 and gives
its residue modulo p. This is stronger than the arithmetic input used
in the present self-contained proof. Lemma 2.1 contains an equivalent
root-of-unity squared-binomial identity. The optional refinement in
Section 7.2 explicitly invokes their stronger theorem.

## What the archive does not claim

No exhaustive priority search, journal acceptance, or proof-assistant
verification is claimed. The article's proof can be checked directly
without accepting the finite experiments as proof. No external paper
is bundled or reproduced in full. No OEIS edit has been made.
