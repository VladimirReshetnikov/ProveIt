# Proportional-depth iterated Bell asymptotics: source audit

Checked 2026-10-02. Definition throughout: `g(z)=exp(z)-1`, `H(n,m)=n![z^n]g^{∘m}(z)`, `n>=1`. Write `β=n/m`. This is a targeted source audit, not an exhaustive novelty certification.

## Main finding: a direct 2002 antecedent

The leading proportional-depth Fatou-contour formula has a clear antecedent in **Thomas Prellberg, “On the Asymptotic Analysis of a Class of Linear Recurrences,” FPSAC 2002**, slide 17/26 (physical PDF page 59, zero-based page 58). A corresponding account appears in a September 23, 2002 INRIA seminar, summarized by Marni Mishna and published in *Algorithms Seminar 2002–2004*, F. Chyzak (ed.), INRIA (2005), pp. 47–50, especially p. 49.

Primary author slides: https://webspace.maths.qmul.ac.uk/t.prellberg/talks/recurrence.pdf

Seminar account: https://algo.inria.fr/seminars/summary/Prellberg2002a.pdf

Conference abstract confirming the announced topic: https://www-igm.univ-mlv.fr/~fpsac/FPSAC02/fpsac02.pdf

### Exact mathematical mapping (our derivation of the specialization)

Prellberg considers the formal functional equation

`X(z)=a(z)X(f(z))+b(z)`, with `f(z)=z+cz²+dz³+...`,

and decomposes `[z^n]X(z)=sum_m X_{n,m}`. His inverse-iteration coordinate satisfies

`f^{-1}(μ(s))=μ(s+1)`.

Choose `a(z)=a0` for any fixed `0<a0<1`, `b(z)=z`, and `f=g`. Then

- `c=1/2`, `d=1/6`, hence `1−d/c²=1/3`
- `X(z)=sum_{m>=0} a0^m g^{∘m}(z)` as a coefficientwise formal series
- `X_{n,m}=a0^m H(n,m)/n!`
- The auxiliary homogeneous equation `Y(z)=a0 Y(g(z))` is solved by `Y(μ(s))=a0^s`, up to an irrelevant constant factor

The displayed two-index equivalent on slide 17 specializes exactly to

`H(n,m)/n! ~ (m/2)^n m^{−1−β/3} J(β)`,

where, with the source's contour orientation,

`J(β)=(2πi)^{-1}∫_C μ(s) exp(βs) ds`.

Indeed the factors `a0^m` cancel, and `a0^s` in the integral cancels against `Y(μ(s))`. If `I(β)=−(2πi)^{-1}∫_C μ′(s) exp(βs) ds`, integration by parts gives `J(β)=I(β)/β`, provided the boundary terms vanish. This is the same prefactor supplied for the present project. A translation of the Fatou coordinate changes the contour amplitude by an exponential factor, so coordinate normalization must be matched before comparing numerical constants.

For `m=λn` exactly, Stirling's formula converts this to

`H(n,λn) ~ sqrt(2π) λ^{−1−1/(3λ)} J(1/λ) n^{2n−1/2−1/(3λ)} (λ/(2e))^n`.

This is an algebraic specialization, not a newly located verbatim theorem about the sequence `H`.

### What is and is not established in the located source

- The source explicitly displays a leading **two-index equivalent**, rather than merely the exponent or an n-th-root scale
- Its final numbered theorem is stated for the **sum over m**, `[z^n]X(z)`; the two-index formula is an intermediate analytic step
- Stated setup: `a,b,f` analytic near zero, `f(z)=z+cz²+dz³+...`, `c>0`; the constant-`a` theorem uses `0<a0<1`
- An asymptotic expansion for the inverse-iteration coordinate is described to all orders
- No explicit uniformity region for `β=n/m`, quantified bivariate remainder, strict positivity result for `J(β)`, or all-orders expansion for `X_{n,m}` is stated in the sources located
- The four-page account and presentation are proof outlines, not a full contour/tail proof. In particular, contour deformation and uniform remainder domination are not developed enough there to audit rigor independently
- The last presentation slide labels higher correction terms as computed by a different, non-rigorous method, and lists computation of the contour integrals as remaining work
- There are visible transcription/typographical inconsistencies: the general inverse-coordinate expansion has the expected positive logarithmic coefficient for `g`, but the partition-chain application prints the opposite sign; the seminar theorem also appears to omit an integral factor in its general constant. Therefore use the original slide 17 formula and carefully checked normalization, not every printed ancillary formula uncritically

**Safe positioning:** credit Prellberg's 2002 bivariate announcement and parabolic method. Present an independently justified proportional-depth theorem, with any verified uniform bounds and positivity proof, without claiming novelty for the leading equivalent, any displayed formal coefficients, or the existence of earlier formal higher terms. No later full proof was located in this scoped search; that does not establish that none exists.

The existing Takeuchi report supplies a precise warning about the printed theorem's scope. Put `f(z)=z/(1−z)`, `a(z)=z`, `b(z)=1`, and let `B(z)` be the formal OGF of ordinary Bell numbers. Since `B(z)=1+f(z)B(f(z))`, the exact solution is `X(z)=1+zB(z)`, hence `X_n=B_{n−1}`. The printed local analyticity/positivity hypotheses hold with `c=d=a1=1`, yet the printed general equivalent would require a nonzero constant times `B_n`; instead `B_{n−1}/B_n~W(n)/n→0`. Thus a restriction or normalization is omitted from the broad outline. This counterexample does **not** disprove Prellberg's specific iterated-Bell bivariate announcement or the Takeuchi application. It does show that these short sources cannot serve as black-box quantitative transfer theorems. Internal cross-check: `/workspace/shared/oeis-takeuchi-asymptotics-result/takeuchi-asymptotics.tex`, subsection “A limitation of the printed general theorem.”

## The originally supplied Bell references

### Skau–Kristensen (2019)

Ivar Henning Skau and Kai Forsberg Kristensen, *An asymptotic Formula for the iterated exponential Bell Numbers*, arXiv:1903.07979.

https://arxiv.org/pdf/1903.07979

They use `B_n^(r)` with generating function `1+g^{∘(r+1)}(z)`, so `B_n^(r)=H(n,r+1)`. Lemma 1 gives a polynomial of degree `n−1` in `r`. Theorem 1 explicitly fixes `n` and lets `r→∞`, obtaining `B_n^(r)~n! r^{n−1}/2^{n−1}`. Its statement supplies no uniformity when `n` grows. It cannot be substituted into `r≈λn` to obtain a multiplicative equivalent.

### Carlson–Makarychev–Mosenzon (2025/SODA 2026)

Charlie Carlson, Yury Makarychev, Ron Mosenzon, *Hardness of Approximation for Shortest Path with Vector Costs*, arXiv:2510.21058v1, Sections 5.1 and 9.

https://arxiv.org/html/2510.21058v1#S5.SS1

Their `B_k(p)=H(p,k+1)`. Theorem 5.7, with `k0=log*_e p−1`, states n-th-root order bounds: for `k>k0`, `B_k(p)^(1/p)=Θ(p(k−k0)^(1−1/p))`; there is another iterated-log regime for smaller k. At `k≈λp`, this gives the coarse scale `Θ(p²)` for the root. It does not determine the exponential-base constant, a polynomial correction, or the multiplicative amplitude. The paper's displayed prose-to-formula transition preceding Theorem 5.7 has an apparent exponent typo `1/k`; the theorem itself clearly uses `1/p`.

## Critical branching overlap and its range restriction

S. V. Nagaev and V. I. Vakhtel, *Limit theorems for probabilities of large deviations of a Galton–Watson process*, **Discrete Mathematics and Applications 13(1)** (2003), 1–26; Russian original **Diskretnaya Matematika 15(1)**, 3–27.

Primary record and Russian full text:

https://www.mathnet.ru/eng/dm183

https://www.mathnet.ru/php/getFT.phtml?jrnid=dm&option_lang=eng&paperid=183&what=fullt

Publisher DOI in the MathNet record: https://doi.org/10.1515/156939203321669537 . The supplied `10.1163/156939203321669537` is another historical publisher DOI for this article.

Theorems 1–2, Russian p. 5 (PDF page 3), assume offspring generating-function radius `R>1`, `k/t→∞`, and **`k=o(t²)`**. Their logarithmic correction is governed by `γ=1−2C/(3B²)`, where `B=f″(1)`, `C=f‴(1)`.

Our inference: for Poisson(1) reproduction, `B=C=1`, hence `γ=1/3`. With `Z_0=1`, exact generating-function identities give

`H(n,m)=E[(Z_m)_n]=E[Z_{m−1}^n]`.

The leading exponential-tail approximation places the n-th-moment saddle near `k≈nt/2`. For `t≈λn`, this is `k≈t²/(2λ)`, outside `o(t²)`. Formally evaluating their correction there suggests the power `n^(−1/(3λ))`, but such substitution is not a valid use of the theorem, and cannot establish the amplitude. The Fatou-contour result resolves precisely the boundary-scale information missing from that application.

English institutional copy was found in search indexing but could not be downloaded reliably during this audit. The range and γ were independently read from the primary Russian PDF; the mathematics is unambiguous despite imperfect OCR. Search URL:

https://opus.bibliothek.uni-augsburg.de/opus4/files/55382/Limit%20theorems%20for%20probabilities%20of%20large%20deviations%20of%20a%20GaltonWatson%20process.pdf

## OEIS: exact diagonals, conjectures, and slope search

The array **A144150** is `A(n,k)=H(n,k+1)` for `n>=1`:

https://oeis.org/A144150

**A139383** is `H(n,n)`. Its August 14, 2015 Kotesovec conjecture is

`H(n,n) ~ 2c n^(2n−5/6)(1/(2e))^n`, `c≈2.86539`.

https://oeis.org/A139383

Thus the requested normalization's λ=1 amplitude is `2c≈5.73078`, not `c`. The entry also conjectures `H(n,n+1)/H(n,n)→e`.

**A261280** is `H(n,n+1)`, with the corresponding conjectural constant `c≈7.7889` when denominator is `2^(n−1)e^n`:

https://oeis.org/A261280

**A346802** is `H(n,n+2)`. Kotesovec's August 11, 2021 conjecture uses denominator `2^n e^n` and constant `42.345...`, consistent with `2c e²`:

https://oeis.org/A346802

All these OEIS asymptotics remain explicitly labeled conjectures in the entries inspected. OEIS sequence existence is not a proof or a comprehensive literature survey.

Exact integer terms were generated independently by the Stirling recurrence `H(n,m+1)=sum_{j=1}^n S(n,j)H(j,m)` with `H(n,0)=δ(n,1)`:

- `H(n,2n)`, n=1 onward: 1, 4, 51, 1380, 64660, 4663253, 479576930, 66668459896
- `H(n,floor(n/2))`, n=1 onward: 1, 1, 1, 15, 52, 2471, 19302, 1855570, 26097835
- `H(n,2n+1)`, n=1 onward: 1, 5, 70, 1989, 95986, 7059156, 736075320

OEIS JSON queries for the distinctive runs `1,4,51,1380,64660`, `15,52,2471,19302,1855570`, and `1,5,70,1989,95986` returned `null` with HTTP 200. A control query `1,2,12,154,3455` returned A139383. Raw responses are preserved in `search-evidence/`. This supports **“no dedicated entry was found by these searches,”** not “these sequences are absent from OEIS.” Some alternative requests received 403, whereas the recorded curl responses succeeded.

## Related aggregate observable: partition lattice chains

Prellberg's motivating application is the total number `Z_n` of strict chains between the endpoints of the partition lattice, OEIS A005121. Its generating function solves `2Z(z)=z+Z(g(z))`. Thus `Z(z)=sum_{m>=0}2^(−m−1)g^{∘m}(z)`, or `Z_n=sum_m 2^(−m−1)H(n,m)`. This exact identity explains why a two-index iterated-Bell estimate occurs in that work.

The known aggregate asymptotic is `Z_n~C_L(n!)²(2 log 2)^(−n)n^(−1−log(2)/3)`, where the Lengyel constant is about `1.0986858055`. The depth sum is concentrated heuristically near `m=n/log 2`, so it probes a proportional-depth slope. However, an equivalent for the depth sum alone does not prove a local equivalent for each m.

Found primary bibliography:

- Tamás Lengyel, *On a recurrence involving Stirling numbers*, European Journal of Combinatorics 5(4) (1984), 313–321. https://doi.org/10.1016/S0195-6698(84)80035-9
- László Babai and Tamás Lengyel, *A convergence criterion for recurrent sequences with application to the partition lattice*, Analysis 12 (1992), 109 onward. https://doi.org/10.1524/anly.1992.12.12.109

The direct bivariate formula was verified in Prellberg, rather than inferred only from these aggregate results. Full original papers for the two bullets above were not audited in this pass.

## Other potentially misleading recent titles checked

- *Higher Order Bell Symmetric Functions*, arXiv:2505.18504v2, studies plethystic analogues and representation-theoretic coefficient averages, not a proportional-depth scalar Bell equivalent: https://arxiv.org/html/2505.18504v2
- Li–Shi–Zhang, *Large Deviations for a Critical Galton-Watson Branching Process*, Acta Math. Appl. Sin. Engl. Ser. 41 (2025), 456–478, concerns random sums indexed by the branching population, not a local population tail at quadratic size: https://link.springer.com/article/10.1007/s10255-024-1058-y

## Saved primary-source evidence

- `prellberg2002-slides.pdf`, `.txt`
- `prellberg2002-summary.pdf`, `.txt`
- `prellberg-slide17.png`: rendered and visually checked physical PDF page 59, the exact two-index formula
- `search-evidence/A346802.html`
- `search-evidence/*.txt`: exact OEIS query outputs and HTTP status

The files named `nv2003.pdf` and `nv2003-russian.pdf` are failed downloads (HTML), not usable PDFs. Primary Nagaev–Vakhtel text was accessed through the web reader instead; do not treat those local failed files as sources.
