# Sources and provenance

Consultation date: September 20, 2026.

## Exact targets

**OEIS A143007**

- https://oeis.org/A143007/internal
- Consulted internal header: revision 75, May 30, 2026, 16:40:32.
- Original sequence author: Peter Bala, July 22, 2008.
- The formula section labels the family on diagonals `(n,n+k)` a
  conjectural result for other diagonals. The article proves that exact
  formula for every nonnegative integer k.
- The array definition, the main-diagonal identification with A005259,
  and the alternative finite binomial formula used in the independent
  implementation checks are also recorded here.

**OEIS A108625**

- https://oeis.org/A108625/internal
- Consulted internal header: revision 98, May 30, 2026, 16:40:25.
- Relevant comments: Peter Bala, July 18, 2008.
- The comments describe the main subdiagonal and main superdiagonal
  zeta(2) formulas conjecturally. Both are proved as k=1 cases of the
  article's all-offset theorems.
- Unlike A143007, this array is not symmetric. Its orientation is checked
  algebraically in the article's appendix.

These records describe the consulted OEIS versions, not the full history
or literature status of the formulas. Full OEIS pages are not reproduced
in this archive; the article restates the mathematical formulas and gives
its own proofs and exposition.

## Classical diagonal sequences

- https://oeis.org/A005259 — zeta(3) Apéry numbers, finite sum, recurrence,
  and known main-diagonal asymptotic.
- https://oeis.org/A005258 — zeta(2) Apéry numbers, finite sum, recurrence,
  and known main-diagonal asymptotic.

The article's main-diagonal results are recoveries of these classical
identities, not claims of their first discovery. No other conjecture in
these diagonal entries is claimed to be solved.

## Primary literature for context

Henri Cohen, *Apéry Acceleration of Continued Fractions*, arXiv:2401.17720
(2024). Sections 3–4 discuss two-dimensional/staircase acceleration and
zeta(2), zeta(3).

- https://arxiv.org/abs/2401.17720
- https://arxiv.org/pdf/2401.17720

Armin Straub, *Multivariate Apéry numbers and supercongruences of rational
functions*, Algebra & Number Theory 8(8) (2014), 1985–2008.
DOI: 10.2140/ant.2014.8.1985.

- https://arxiv.org/abs/1401.0854
- https://doi.org/10.2140/ant.2014.8.1985

Roland Bacher, Pierre de la Harpe, and Boris Venkov, *Séries de croissance
et polynômes d'Ehrhart associés aux réseaux de racines*, Annales de
l'Institut Fourier 49(3) (1999), 727–762. DOI: 10.5802/aif.1689.

- https://www.numdam.org/item/AIF_1999__49_3_727_0/
- https://doi.org/10.5802/aif.1689

The bibliographic title and year for the Bacher–de la Harpe–Venkov source
have been taken from the actual 1999 journal record. The OEIS hyperlink
and its displayed bibliographic label do not match completely; the
article does not perpetuate that mismatch.

## Proof versus attribution

The finite telescoping certificates, potential identities, convergence
estimates, recurrence eliminations, and fixed-offset asymptotic derivations
are all written out in the article. The main theorems do not rely on an
external proof of an OEIS conjecture. The primary literature is cited to
situate the work and to avoid presenting classical Apéry acceleration as
a newly invented general method. No exhaustive priority claim is made.
