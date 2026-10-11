# Primary-source prior-art ledger for the Gamma normalizers

This ledger is a bounded literature check, not a claim of exhaustive
priority research. Sources were read as primary documents.

## Young 2023/2024

Young's 2023 lecture, *Global series for height 1 multiple zeta functions*,
4 July 2023, is publicly hosted at
https://iecl.univ-lorraine.fr/wp-content/uploads/2023/07/tuesday-12-young-p.pdf.
The published article with the same title is European Journal of
Mathematics 9, Article 99 (2023), DOI 10.1007/s40879-023-00695-0.
Only the published abstract/metadata and the full lecture were inspected;
the subscription article was not obtained.

Young's *Series of Height One Multiple Zeta Functions*, Integers 24
(2024), #A43, DOI 10.5281/zenodo.11221606, was inspected in full:
https://math.colgate.edu/~integers/y43/y43.pdf.

Known: the reciprocal-Gamma singular Laurent terms at s=1; the first
regular coefficient as a Cauchy/Bernoulli-second-kind series; multiple
Hurwitz integrals for the same coefficient; and strict-depth Laurent
constants in Ramanujan sums of complete harmonic star sums.

The 2023 lecture, numbered slides 3 and 6, explicitly gives the correct
sign convention. The 2024 prose uses an inconsistent phrase for the
literal linear coefficient. See `young_sign_audit.md` for the narrow
correction and exact change of coefficient convention.

## Sesma: Roman harmonic numbers and the finite Gamma generator

Javier Sesma, *The Roman harmonic numbers revisited*, Journal of Number
Theory 180 (2017), 544--565, DOI 10.1016/j.jnt.2017.05.009.
Primary preprint: https://arxiv.org/pdf/1702.03718.

Equation (49), Proposition 3(a), gives

    n!/(1-t)_n = sum_(m>=0) c_n^(m) t^m.

For integer x=n+1 this is exactly

    Gamma(1-t)Gamma(x)/Gamma(x-t)
       = sum_(m>=0) C_m(x)t^m/m!.

Thus C_m(n+1)/m! is the existing Roman harmonic number c_n^(m),
equivalently the complete harmonic star sum with m unit indices.
Equation (29) already gives its complete polynomial in generalized
harmonic numbers; (30) gives the beta-logarithmic integral. Equations
(24) and (26) identify negative Roman degree with strict harmonic sums.
The paper explicitly confines its treatment to integer degree (page 3),
while citing Coffey Appendix B for generalized Stirling numbers with
complex degree. It does not present the all-depth ordinary integral
over the meromorphic degree variable appearing in the proposed article.

## Coffey: the ordinary m=2 integral and complex Gamma derivatives

Mark W. Coffey, *Series representations of the Riemann and Hurwitz zeta
functions and series and integral representations of the first Stieltjes
constant*, arXiv:1106.5146 (2011):
https://arxiv.org/pdf/1106.5146.

Proposition 3(b), equation (1.19), gives the convergent ordinary integral

    gamma_1 = zeta(2) + integral_0^1
       {gamma*psi(x) + (psi(x)^2-psi'(x))/2} dx.

This is exactly the m=2 case of

    integral_0^1 C_m(x) dx = m! (c_m-lambda_(m-1)),

because C_2=(psi+gamma)^2+zeta(2)-psi' and lambda_1=-gamma_1.
Therefore this first case should be identified as a recovery of a known
identity rather than a new result.

Appendix B, equations (B.1)--(B.9), discusses complex-degree derivatives
of (s)_(lambda-1)=Gamma(s+lambda-1)/Gamma(s), generalized Stirling
numbers, and their Bell-polynomial/polygamma realization. This quotient
has the reciprocal direction to the normalized C_m generator when s is
the differentiation parameter. The derivative and interpolation methods
are therefore established ingredients.

## Recommended attribution boundary

The normalized Gamma quotient and its Bell coefficients should be
introduced as standard special-function objects/interpolations. Present
the session's contribution as the proved residue cancellation, its use
to isolate the strict-depth coefficient in an ordinary integral, the
comparison to finite parts of scalar digamma powers, and the scalar
Gamma-Appell residue normalization theorem. The first Cauchy-series
coefficient identity and the general star/strict relationship are prior
art. No worldwide novelty claim is warranted by this limited search.
