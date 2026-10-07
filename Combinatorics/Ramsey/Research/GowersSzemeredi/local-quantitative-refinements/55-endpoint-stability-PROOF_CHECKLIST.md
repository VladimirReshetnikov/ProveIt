# Proof-obligation checklist

This is an authoring checklist for the supplied proof, not a report by an external
reviewer. No human or proof-assistant verification is asserted.

| Obligation | Resolution in article |
|---|---|
| Normalized versus unnormalized cube averages | Definition (1.1); all averages normalized |
| Nonclassical phases at small characteristic | Multiplicative-difference definition, not a coordinate polynomial restriction |
| Existence of a closest phase on a finite group | Closed subset of a finite product of circles |
| Uniform entry as group size varies | Explicitly imported Eisner–Tao Theorem 1.1 |
| Local estimate without that entry theorem | Theorem 7.1 applies to any supplied phase satisfying the correlation condition |
| Sparse perturbations can have large sup norm | Exact finite product expansion; no small-sup-norm Taylor assumption in the upper bound |
| Four-vertex dependencies over composite groups | Ordinary, exceptional index-two, or unimodular independent classification |
| Signs on an imaginary tangent | The sum of vertex parities is even on every xor-zero four-set |
| Fifth-order terms could cause a D^(5/2) error | Exact real-part identity and six-triple Hölder give O((v+a)v^2) |
| Amplitude losses might change the optimum | Positive amplitude term retained in the local inequality |
| Odd-group factor 1/2 in Fourier fourth powers | Negation-pair decomposition plus bounded-function skew relation |
| Even-group optimum is really two-torsion | Profile Phi(tau), uniquely maximized at tau=1 |
| Inversion of the defect inequality | Explicit two-stage substitution with displayed cubic constant |
| Lower examples may have a closer nonconstant phase | Uniform phase-class gap before computing true distance |
| Cubic remainder uniform in the lower examples | Bounded tangent, symmetric cube difference, uniformly bounded derivatives |
| Exact U^2 formula uses the correct branch | Largest Fourier coefficient forces D <= 2-sqrt(2) when epsilon <= 1/2 |
| Rigidity is not an unsupported converse | Only necessity is stated; explicit families provide existence |
| Computational checks are not universal proof | Scope and tolerances recorded explicitly |
| Global Szemerédi improvement | Not claimed |
| Publication priority | Not established |

## Independent ways to check the key coefficients

The even-group coefficient comes from the exact family
`epsilon=(1-cos(q*t))/q`, `D=2(1-cos(t))`.
It also equals `8*(q*(q-1)/8 + q*(q-1)*(q-2)/24)/q^3`.

The odd-group coefficient comes from the conjugate-pair family and cancellation
of its fourth moment during elimination of `t^2`. It also equals
`8*(q*(q-1)/8 + (6^d-2*4^d+2^d)/16)/q^3`.

The script checks these algebraic equalities with exact fractions and checks the
asymptotic ratios separately at high precision. The mathematical proof does not
depend on either computation.
