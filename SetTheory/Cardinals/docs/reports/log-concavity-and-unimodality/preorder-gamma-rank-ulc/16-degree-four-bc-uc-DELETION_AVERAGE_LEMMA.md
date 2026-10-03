# Deletion-average lemma for a fixed three-center side

Status: independently audited and approved (2026-10-01), as part of the outward-star last-gap proof.

Let Q be the matching-support polynomial on three fixed centers and arbitrary labeled exterior vertices. All activities are one. Let H be any specified set of m exterior vertices, including possibly vertices with no neighbor among these three centers. For x∈H, let Q_{−x} denote the side polynomial after deleting x. Set

R(t)=Σ_{x∈H}Q_{−x}(t)=m+A t+C t²+D t³.

Then the EXACT degree-three homogenization

R_h(z,t)=m z³+A z²t+C zt²+D t³

is Lorentzian. In particular C²≥3AD.

## Proof

Add a private dummy for each of the three centers. The transversal matroid on the exterior vertices and these three dummies has rank three: a basis consists of chosen exterior vertices that match a selected subset of the centers, together with the private dummies for the remaining centers. Every such support is one basis, regardless of how many matchings realize it.

Its homogeneous basis polynomial is Lorentzian. Identify all dummy variables with z, all exterior variables indexed by H with s, and all remaining exterior variables with t. Nonnegative linear substitutions preserve the Lorentzian property, so the resulting homogeneous degree-three polynomial q(z,s,t) is Lorentzian. The degree in s is at most m.

Polarize s into m variables s1,...,sm, using the degree bound m. The polarization operator replaces s^k by

e_k(s1,...,sm)/binomial(m,k).

Brändén–Huh Proposition 3.1 states that polarization preserves the Lorentzian property. Set s1=0 and s2=...=sm=t. A monomial whose exterior support uses k vertices from H acquires factor

binomial(m−1,k)/binomial(m,k)=(m−k)/m.

Consequently m times the resulting polynomial is R_h(z,t): a given Q-support remains after deleting exactly m−k of the eligible vertices. Specialization at zero, diagonalization, and multiplication by a nonnegative scalar preserve the Lorentzian property. This proves the claim. The m=0 case is the zero polynomial and can be treated separately.

This argument does not divide a homogenized polynomial by a monomial. It also does not assert Lorentzianity of R with all original exterior variables retained separately; that stronger statement is false.

## Verified sources

Brändén and Huh, *Lorentzian polynomials*, Proposition 3.1 (polarization/depolarization), Theorem 2.10 (nonnegative linear substitutions), and the matroid characterization in Theorem 3.10. Author PDF: https://web.math.princeton.edu/~huh/Lorentzian.pdf . In this version Proposition 3.1 appears on printed page26 / PDF page26.

## Reduction of the full 1+3 last gap

Write Q(t)=1+L t+B t²+T t³ and let Q⁺ be Q after adding one universal exterior vertex. Thus Q⁺(t)=1+(L+3)t+(B+E1)t²+(T+E2)t³. The full 1+3 polynomial is exactly Gamma=Q⁺+tR.

Suppose the side ratio T/B is nondecreasing whenever an exterior vertex is added (zero cases interpreted by cross multiplication). Then for each x∈H,

Q_{−x,3}/Q_{−x,2} ≤ Q⁺_3/Q⁺_2,

and summing cross products gives D(B+E1)≤C(T+E2).

Combining this with C²≥3AD proves the last gap immediately:

3 Gamma₃²−8 Gamma₂ Gamma₄
=3(C+T+E2)²−8(A+B+E1)D
≥ C²/3−2C(T+E2)+3(T+E2)²
=(C−3(T+E2))²/3 ≥0.

Thus the remaining sufficient claim is the seven-type side monotonicity inequality

T(n+e_i)B(n)−T(n)B(n+e_i)≥0

for every population vector n≥0 and every nonempty neighborhood type i⊆{1,2,3}. Adding the universal vertex is included among these seven cases. This claim is now proved analytically by summing the private-dummy Rayleigh inequalities in the augmented rank-three transversal matroid; Wagner's rank-three Rayleigh theorem applies. The complete construction, boundary cases and full proof appear in UNBALANCED_LAST_GAP_PROOF.md beside this note. Exact seven-type certificates independently verify the ordinary-population case.
