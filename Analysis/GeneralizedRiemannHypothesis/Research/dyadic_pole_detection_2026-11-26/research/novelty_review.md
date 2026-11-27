# Novelty and source review

Review date: 26 November 2026. This is a targeted literature search, not a certificate of priority. Exact statements and mechanisms were compared before choosing the proposed contributions.

## Proposed contributions and responsible scope

Write

\[
c_N=\inf_{z\in\mathbb C}\max_{0\le j<N}|1+z^{2^j}|.
\]

For every even integer \(N\ge2\), let \(L=2^{N-1}\), and let \(r\in(0,1)\) solve \(r+r^L=1\). The proposed sharp result is

\[
c_N=\sqrt{1-r+r^2},
\qquad
z=r\exp(\pm2\pi i/3)
\]

with the displayed two points as the only minimizers. The proof uses the angle itinerary under successive squaring in the left half-plane, together with the strict concavity in \(\log v\) of

\[
\arccos\!\left(\frac{v+d/v}{2}\right),\qquad d=r^{L+1}.
\]

The case \(N=2\) is a known problem dating at least to the 1956 Miklós Schweitzer competition. The even family for \(N\ge4\), its sharp simultaneous visibility interpretation for positive dilation filters, and the exact three-filter result below were not found in the targeted searches listed here. That is evidence of a potentially original result, not proof that no earlier equivalent theorem exists. The manuscript should say that these results are derived here and that priority remains unverified.

The separately derived three-filter value is

\[
c_3=\sqrt{t+t^2}=0.88200326758470582856\ldots,
\quad t^4-2t^2-3t+2=0,\quad t\in(0.51,0.52).
\]

Its only minimizers are

\[
z_\pm=\frac{t^2-1}{2}\pm\frac{i}{2}\sqrt{t+1}.
\]

An independent convex polynomial certificate, including an explicit quantitative stability estimate, is supplied in Section 4.2 of `report.tex`. The certificate has been checked by exact polynomial arithmetic, not just numerical optimization.

## Exact prior art for the two-filter case

**1956 competition; 1968 published collection.** Gábor Szász, L. Gehér, I. Kovács, and L. Pintér, editors, *Contests in Higher Mathematics: Hungary, 1949–1961. In memoriam Miklós Schweitzer*, Akadémiai Kiadó, Budapest, 1968. The problem appears as 1956 Problem 2 on printed page 23, and its solution is §3.3, Theory of Functions, Problem 2, beginning on printed page 103. It asks for the exact minimum of \(\max(|1+z|,|1+z^2|)\) over complex \(z\).

Primary institutional bibliography:

<https://real-eod.mtak.hu/14558/>

Primary institutional scan:

<https://real-eod.mtak.hu/14558/1/AkademiaiKiado_007070.pdf>

The bibliography and the exact problem statements on pages 23 and 103 were verified through the institutional page and indexed scan text. The complete 78 MB scan exceeded the web viewer's size limit, so this review does not claim a full inspection of every surrounding remark in the book.

**2013 independent online presentation.** Mathematics Stack Exchange, “Find the complex \(z\) such \(\max(|1+z|,|1+z^2|)\) is minimum,” question posted 6 November 2013; answer by chenbai posted 7 November 2013. That answer identifies the value \(\sqrt{3-\sqrt5}\). A subsequent answer by River Li, displayed as 18 June on the page retrieved in 2026, gives a complete weighted sum-of-squares proof and both equality cases via conjugation.

<https://math.stackexchange.com/questions/554618/find-the-complex-z-such-max1z-1z2-is-minimum/5141006>

In particular, neither the exact two-filter constant nor its golden-ratio extremizers should be presented as new.

## Nearby analytic mechanisms already in the literature

### One-sided bounds and Landau's theorem

The inspected repository is `lsernau/grh-lean`, pinned for this review to commit `72fead102f663d5c7a407964a13dc0cf9d977207`.

<https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207>

The guide and these source files were read:

- `grh/GUIDE.md`;
- `grh/src/Lib/Analytic/Landau.lean`;
- `grh/src/New/Reduction/Zeros/Criterion.lean`;
- `grh/src/New/Reduction/Zeros/PrimeError.lean`.

The general analytic ingredient is classical: an eventual one-sided bound for a real error term, together with compatible signs of real-axis residues, rules out sufficiently far-right poles of its Laplace transform. `Landau.lean` explicitly cites Montgomery–Vaughan (2007), Lemma 15.1, and Widder (1941), Chapter II, Theorem 5b. A generic version of this argument must not be claimed as new.

The repository's arithmetic criterion applies this mechanism to weighted prime errors for quadratic twists, using zero-density information to prevent cancellation of the pole one wants to detect. The proposed work isolates the finite-dilation multiplier geometry; it does not reproduce or improve the repository's theta-lift, form-counting, determinant, or zero-density arguments.

Masatoshi Suzuki, “On variants of Chebyshev's conjecture,” first posted 11 November 2024, revised version dated 10 November 2025, *The Ramanujan Journal* 68, article 95 (2025), DOI `10.1007/s11139-025-01238-9`, already obtains RH and Dirichlet-GRH criteria from signs of weighted von Mangoldt sums.

<https://arxiv.org/abs/2411.07436>

The proof exposition associated with the recent RH result also discusses one-sided estimates on arbitrarily large power windows, so merely weakening eventual bounds to a sparse family of long windows would not establish novelty:

<https://andrewodesky.com/rh/s/landau.html>

<https://andrewodesky.com/rh/overview.html?print=the-reduction-to-an-upper-bound-a-method-of-landau>

### Several poles and positive trigonometric kernels

A. E. Ingham, “On Two Conjectures in the Theory of Numbers,” *American Journal of Mathematics* 64(1) (1942), 313–319, derives oscillation bounds from finite trigonometric sums built out of boundary-pole residues and Fejér-type weights.

Primary paper scan:

<https://personal.math.ubc.ca/~gerg/teaching/592-Fall2018/papers/1942.Ingham.pdf>

Harold G. Diamond, “Two oscillation theorems” (1971), develops precisely the issue of several nonreal poles overcoming a real residue. Under suitable weak independence of pole heights, it obtains joint bounds involving sums of the absolute residues. Its proof uses products of positive Fejér kernels, and its remarks improve the associated coefficient to a cosine expression. Thus a general claim that positive trigonometric combinations yield stronger joint pole tests would duplicate a well-developed classical mechanism.

Primary paper scan:

<https://personal.math.ubc.ca/~gerg/teaching/592-Fall2018/papers/1971.Diamond.pdf>

### Two boxcar filters and Diophantine approximation

The use of several averaging widths to avoid common sinc zeros is also established prior art. Relevant primary sources include I. M. Johnstone, G. Kerkyacharian, D. Picard, and M. Raimondo, “Wavelet Deconvolution in a Periodic Setting,” *Journal of the Royal Statistical Society, Series B* 66(3) (2004), 547–573:

<https://academic.oup.com/jrsssb/article/66/3/547/7098441>

and Marianna Pensky and Theofanis Sapatinas, “Multichannel boxcar deconvolution with growing number of channels,” *Electronic Journal of Statistics* (2011):

<https://sciences.ucf.edu/math/mpensky/wp-content/uploads/sites/9/2016/09/EJS597_Published-2011.pdf>

The latter explicitly controls joint boxcar multipliers using simultaneous badly approximable tuples. The current manuscript therefore does not claim novelty for irrational-width boxcar visibility, Diophantine sinc bounds, or their general deconvolution principle.

## Search record for the proposed sharp constants

Searches used both available engines. Exact-match, symbolic, numerical, and mechanism-based queries included the following, with and without quotation marks and common exponent formatting variants:

```text
"max" "|1+z|" "|1+z^2|" "|1+z^4|"
"minimum" "1+z^4" "1+z^2" "1+z"
"min" "max" "z+1" "z^2+1" "z^4+1"
"t^4-2t^2-3t+2"
"0.882003267"
"0.777929764"
"max" "|1+z" "2^j" minimum
"1+z^{2" minimum modulus
"1+z" "1+z^2" "1+z^8"
"r+r^8=1"
"0.920395115"
"dyadic" "complex" "golden ratio" minimax
"dyadic" "lemniscates" minimum
"lacunary" "minimax" "complex" polynomials
"dyadic" "minimax" "polynomial" "modulus"
"lemniscate" "1+z" "1+z^2"
"dyadic powers" "minimum"
complex number "powers of 2" "minimum" modulus "1"
complex number "successive squaring" "minimum" distance -1
complex powers "disk centered at" "-1" "squaring"
"powers" "complex" "max" "2π/3" minimum
```

These searches repeatedly located the known two-polynomial problem, the familiar dyadic product identity, and unrelated extremal or lemniscate literature. They did not locate the asserted exact even-bank family, the three-filter quartic, or the stated stability certificate.

This review has no access to every mathematical database, nonindexed competition archive, thesis, or publication in all languages. A publishable priority claim would need further independent literature review. The exact proofs remain meaningful mathematical results regardless of whether a prior equivalent result is eventually found.
