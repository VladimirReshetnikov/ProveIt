# Public sources and version notes

The complete bibliography is in the article. Sources were checked on 2 October 2026.

## Counting problem and prior constants

- https://oeis.org/A227578 — ordered arbitrary-positive-coordinate decrements; general fixed-k asymptotic scale recorded as a conjecture
- https://oeis.org/A059231 — k=2 column and algebraic generating function
- https://oeis.org/A227580 — k=3 leading constant recorded 18 July 2013
- https://oeis.org/A227583 — k=4 leading constant recorded 19 July 2013
- https://oeis.org/A227596 — k=5 leading constant recorded 20 November 2016

The corresponding individually retrieved public oeisdata records had headers A227578 #48 (24 July 2021), A227580 #12 (20 December 2020), A227583 #23 (13 March 2026), and A227596 #15 (20 December 2020). The package contains freshly computed data, not copies of those complete records. Posted recurrence code is not treated as a proof of the counting recurrence.

## Primary analytic methods

- Alexander Raichev and Mark C. Wilson, *Asymptotics of coefficients of multivariate generating functions: improvements for smooth points*, EJC15 (2008), R89. https://doi.org/10.37236/813
  The published PDF was read, including Definition3.1 and Theorem3.2 on printed page4. Its SHA-256 is 9769f2306f32e790879ca959ebbf52f24b71b2545abdf54c41f8e47a66cbb8bf. The older arXiv version https://arxiv.org/abs/0803.2914v1 lists A.F.M. ter Elst as an additional author; the article keeps those versions distinct.
- Leonard Lipshitz, *The diagonal of a D-finite power series is D-finite*, Journal of Algebra113 (1988), 373–378. https://doi.org/10.1016/0021-8693(88)90166-4
  The closure theorem and primary bibliographic data were cross-checked in the author-hosted ACSV text, Theorem2.4.10, and the bibliography of Bostan–Lairez–Salvy, *Multiple binomial sums*. The original Lipshitz PDF was not re-read. Chen–Li's https://arxiv.org/abs/1110.5577 discusses a repair to a proof reduction; the diagonal theorem remains the established result used here.
- Corless et al., *On the Lambert W function*. https://doi.org/10.1007/BF02124750

## Model and attribution boundaries

- Bostan, Bousquet-Mélou and Melczer, *Counting walks with large steps in an orthant*. https://doi.org/10.4171/JEMS/1053 — general orbit-method precedent; its finite-step framework is not silently substituted for this infinite rook-step model
- Kung and de Mier, *Catalan lattice paths with rook, bishop and spider steps*. https://arxiv.org/abs/1109.1806 — the planar neighborhood
- Kauers and Zeilberger, *The computational challenge of enumerating high-dimensional rook walks*. https://arxiv.org/abs/1011.4671 — unrestricted rook walks, not the chamber count
- Denisov and FitzGerald, *Ordered exponential random walks*, ALEA20 (2023), 1211–1246. https://doi.org/10.30757/ALEA.v20-45 — published Section2.2 includes the geometric-increment harmonic determinant. The associated harmonic polynomial is prior machinery. The simultaneous-update process in that paper is not declared equivalent to the present random-turn model.

The literature search was targeted. No assertion of exhaustive priority clearance is made.
