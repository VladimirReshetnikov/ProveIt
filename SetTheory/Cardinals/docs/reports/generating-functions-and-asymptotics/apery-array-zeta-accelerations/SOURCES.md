# Sources and provenance

Consultation date: September 20, 2026. The A108625 formula-field wording was
re-checked on September 21, 2026 while merging the two source archives (see
"Reconciled reading of A108625" below). Public pages were retrieved through
web browsing, not inferred from an old recollection of OEIS. This is a source
audit, not an assertion that an OEIS conjecture label establishes worldwide
novelty. The notes below are a selective transcription of the relevant labels
and formulas, not archived copies of the complete pages.

## Exact targets

**OEIS A143007**

- https://oeis.org/A143007/internal
- Consulted internal header: revision 75, May 30, 2026, 16:40:32.
- Original sequence author: Peter Bala, July 22, 2008.
- The formula section labels the family on diagonals `(n,n+k)` a
  "Conjectural result for other diagonals". The article proves that exact
  formula for every nonnegative integer k.
- The array definition, the main-diagonal identification with A005259,
  and the alternative finite binomial formula used in the independent
  implementation checks are also recorded here. That alternative sum is
  `Sum_j C(m,j)^2 * C(m+n-j,m)^2`, equivalently
  `Sum_j C(n,j)^2 * C(n+m-j,m-j)^2`; both forms appear in the two verifiers.
- The target is the zeta-acceleration family, NOT the separate
  supercongruence statement elsewhere in the same entry.

**OEIS A108625**

- https://oeis.org/A108625/internal
- Consulted internal header: revision 98, May 30, 2026, 16:40:25.
- The formula field carries two separate labels, "Conjectural result for
  superdiagonals" and "Conjectural result for subdiagonals", each stated for
  `k = 0,1,2,...`, and each attributed to Peter Bala. The
  superdiagonal numerator is `5*n^2 + 6*k*n + 2*k^2` with boundary term
  `H_k^(2)`; the subdiagonal numerator is `5*n^2 + 4*k*n + k^2` with boundary
  term `2*E_k^(2)` and an extra factor `(-1)^k`.
- The entry's earlier comments, dated July 18, 2008, describe the main
  diagonal and its two immediate neighbours, which are the k = 0 and k = 1
  cases of the same families.
- The entry calls its own array `T`. The article writes `C(m,n)`, and the
  independent verifier writes `U(n,m)`; in every case the first coordinate
  is the lattice dimension and the second the radius.
- The entry also gives `U(n,m) = Sum_j C(n,j)^2 * C(n+m-j,m-j)`, checked
  independently in the supplementary code.
- Unlike A143007, this array is not symmetric. Its orientation is checked
  algebraically in the article's appendix, not inferred from a numeric
  prefix. Transposing it would interchange the two zeta(2) conjectures and
  alter their constants and signs.
- The separate supercongruence and other conjectural formulas in this entry
  are not addressed.

### Reconciled reading of A108625

The two source archives disagreed on what A108625 states. One recorded only
the main superdiagonal and main subdiagonal, from the comments of July 18,
2008, and therefore described the all-offset families as newly stated here.
The other recorded two formula-field labels covering all k. The entry itself
was re-read on September 21, 2026: the formula field does carry both
"Conjectural result for superdiagonals" and "Conjectural result for
subdiagonals", each written for `k = 0,1,2,...`. The second reading is
correct, and the article now says so. The mathematics is unaffected — both
archives proved the all-k statement — but the scope sentence is not: the
contribution is the proof of families that the entry already states, not
their first statement.

These records describe the consulted OEIS versions, not the full history
or literature status of the formulas. Full OEIS pages are not reproduced
in this archive; the article restates the mathematical formulas and gives
its own proofs and exposition.

## Classical diagonal sequences

- https://oeis.org/A005259 — zeta(3) Apéry numbers, finite sum, recurrence,
  and known main-diagonal asymptotic. Begins 1, 5, 73, 1445, 33001, ... .
- https://oeis.org/A005258 — zeta(2) Apéry numbers, finite sum, recurrence,
  and known main-diagonal asymptotic. Begins 1, 3, 19, 147, 1251, ... .

The article's main-diagonal results are recoveries of these classical
identities, not claims of their first discovery. No other conjecture in
these diagonal entries is claimed to be solved; in particular the
irreducibility conjectures appearing in either classical entry are untouched.
An initially considered square-sum identity in A005258 was NOT selected as a
target and is not represented as proved here.

## Existing literature and priority

**Ofir David, *The conservative matrix field*, arXiv:2303.09318v3, 2023.**

- Abstract and revision record: https://arxiv.org/abs/2303.09318
- Full HTML consulted: https://arxiv.org/html/2303.09318v3
- Version 3 was revised December 4, 2023.
- Examples 16, 19 and 25 and Section 5 discuss related conservative fields.
  Example 25 displays the same cubic factors up to a sign convention and the
  quadratic pair used here after duality. Its Section 5 establishes
  convergence and relates a diagonal trajectory to Apéry's irrationality
  argument.

The self-contained scalar finite-sum proof in this archive does not rely on
those matrix-field results as black boxes. Nevertheless, this substantial
overlap precludes any unsupported claim that the method, its polynomials, or
all its consequences originate in this article. An OEIS label can persist
after an identity follows from a broader theorem in the literature.

This acknowledgement is carried over from the second source archive and is
the most important single transfer made during the merge; the base archive
cited only Cohen, below, and was materially incomplete without it.

**Henri Cohen, *Apéry Acceleration of Continued Fractions*, arXiv:2401.17720
(2024).** Sections 3–4 discuss two-dimensional/staircase acceleration and
zeta(2), zeta(3). Retained as additional classical context.

- https://arxiv.org/abs/2401.17720
- https://arxiv.org/pdf/2401.17720

**Armin Straub, *Multivariate Apéry numbers and supercongruences of rational
functions*, Algebra & Number Theory 8(8) (2014), 1985–2008.**
DOI: 10.2140/ant.2014.8.1985. Cited as context for multivariate Apéry
arrays; its arithmetic theorems are not required by the three series proofs.

- https://arxiv.org/abs/1401.0854
- https://doi.org/10.2140/ant.2014.8.1985

**Roland Bacher, Pierre de la Harpe, and Boris Venkov, *Séries de croissance
et polynômes d'Ehrhart associés aux réseaux de racines*, Annales de
l'Institut Fourier 49(3) (1999), 727–762.** DOI: 10.5802/aif.1689.

- https://www.numdam.org/item/AIF_1999__49_3_727_0/
- https://doi.org/10.5802/aif.1689

The bibliographic title and year for the Bacher–de la Harpe–Venkov source
have been taken from the actual 1999 journal record. The OEIS hyperlink
and its displayed bibliographic label do not match completely; the
article does not perpetuate that mismatch.

**Roger Apéry, *Irrationalité de zeta(2) et zeta(3)*, Astérisque 61 (1979),
11–13.** The bibliography is verified through the records linked from the
classical OEIS entries; the present article does not claim to reproduce that
paper's entire irrationality proof.

## Proof versus attribution

The finite telescoping certificates, potential identities, convergence
estimates, recurrence eliminations, and fixed-offset asymptotic derivations
are all written out in the article. The main theorems do not rely on an
external proof of an OEIS conjecture. The primary literature is cited to
situate the work and to avoid presenting classical Apéry acceleration as
a newly invented general method. No exhaustive priority claim is made.

## What has and has not been established

**Established in the article:** all three infinite identities for every fixed
nonnegative integer shift; exact finite identities; error signs and rational
bounds; certified decimal prefixes; convergence along all unbounded monotone
lattice paths; the classical main-diagonal cubic and quadratic recurrences;
a three-term recurrence on every shifted *cubic* diagonal, with its companion
solution and Wronskian; and sharp fixed-shift leading asymptotic constants.

**Not claimed:** priority over all prior literature; uniform asymptotics for
a growing shift; a new proof of irrationality from error estimates alone; any
formal proof-assistant certification; or resolution of unrelated conjectures
in the same entries. No OEIS entry was edited or submitted during this work.

**Known gap, stated as such:** neither source archive proved an all-offset
recurrence for the quadratic array. The zeta(2) recurrence is established
only on the main diagonal. The merged article says so explicitly in
Section 7.3, "The shifted-diagonal recurrence".

**Arithmetic caveat:** along a shifted cubic diagonal the denominator
sequence is integral, but the companion numerator sequence need not be.
The approximation estimates are therefore not, without an additional
denominator argument, a self-contained proof of irrationality.
