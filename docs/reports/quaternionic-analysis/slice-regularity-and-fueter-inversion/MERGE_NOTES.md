# How this document was merged

This package is one article assembled from **ten separately delivered
manuscripts**.  They are not ten papers on ten topics.  Manuscript 03 is an
expository survey, *Classical Complex Theorems over the Quaternions*, dated 20
September 2026.  The other nine were all written on 21 September 2026 as
independent attempts at the same follow-up problem — the global inverse Fueter
problem — and one of them (07) ships a verbatim copy of 03 as its
`source_context/`.

So the nine are nine runs at one question.  They agree on the answer.  What
they do not agree on is notation, and in a few places on how sharp a statement
can be made; both are recorded below.

## The ten sources

| id | archive | title | pp |
|---|---|---|---:|
| 01 | `Global_Fueter_Primitives_and_Spherical_Residues.zip` | Global Fueter Primitives and Spherical Residues | 25 |
| 02 | `global_fueter_inversion.zip` | Global Fueter Inversion | 21 |
| 03 | `quaternionic_analysis.zip` | Classical Complex Theorems over the Quaternions (the original) | 27 |
| 04 | `quaternionic_analysis_research (1).zip` | Global Fueter Primitives, Affine Monodromy, and Spherical Singularities | 21 |
| 05 | `quaternionic_analysis_research (2).zip` | Affine Monodromy and Spherical Residues in Quaternionic Analysis | 23 |
| 06 | `quaternionic_analysis_research(1).zip` | Global Fueter Primitives and Spherical Singularities | 22 |
| 07 | `quaternionic_analysis_research.zip` | Global Fueter Primitives: Period Obstructions, Spherical Defects, Sharp Energy Laws | 18 |
| 08 | `quaternionic_fueter_research (1).zip` | Period obstructions, reflection symmetry, and a sharp residue-energy law | 19 |
| 09 | `quaternionic_fueter_research.zip` | Affine Monodromy and Spherical Principal Parts in Quaternionic Fueter Inversion | 20 |
| 10 | `quaternionic_periods_research.zip` | Periods, Global Fueter Primitives, and Integrable Spherical Singularities | 21 |

All ten are preserved verbatim under `sources/`, and all ten verification
programs under `code/`, namespaced by source id.  Nothing was discarded: the
deduplication is in the *article*, which states each shared theorem once.

## What the nine agreed on

Every one of the nine states the same two closed quaternion-valued one-forms

    omega_g = (1/2)(-P dx + Q dy),    theta_g = (1/2)((xP + yQ) dx + (yP - xQ) dy)

for an axially monogenic `g = P + IQ`, proves that a single-valued
slice-regular `f` with `Delta_4 f = g` exists exactly when both have vanishing
periods, reconstructs `f(x+Iy) = (x+Iy)C + V`, and finds the monodromy to be
affine, `q -> qa + b`.  They agree that the cokernel of the Fueter map has real
dimension `8m`, and they agree on the leading constant of the logarithmic
energy law.  Nine independent derivations reaching the same constants is the
main evidence that the theory is right.

## Where they did not agree

Thirteen conflicts were found and resolved.  Most are collisions of notation,
but several are mathematical, and two of those would have produced a false
statement if the merge had been mechanical.

### 1. The symbol M_g and the sharp constant in the leading-size law at a critical singularity

**In the sources.** 01 (§9, notation table) and 02 (§8) and 06 (§8) define M_g(rho) = sup over |z-p| = rho AND over I in S of |P + IQ| — the true quaternionic supremum over the whole conjugacy sphere — and 01 (thm:leading 9.2) and 06 (thm:asymptotic) prove rho M_g(rho) -> (1/(pi v)) sqrt(R_p(a,b)^2 + 2 v |Im_H(b conj a)|). 10 (§7, 'profile norm') defines M_g(x,r) = (|P|^2 + |Q|^2)^{1/2} — the axial PAIR norm — and 08 (||g||_ax), 09 (m_g) and 01 itself (second half of thm:leading 9.2) prove the limit (1/(pi v)) sqrt(R_p(a,b)^2), with no correction term.

**Resolved.** Both laws are correct, in different norms; the contradiction is entirely in the symbol, and it is the most dangerous item in the merge. The two constants genuinely differ: taking p = iota, a = 1, b = i gives R_p^2 = 2 and |Im_H(b conj a)| = 1, so the spherical-supremum constant is 2/pi and the pair-norm constant is sqrt2/pi. I verified 01's algebra independently — writing the leading term as K = (pa+b)/(2 pi iota (z-p)) = X + iota Y, one gets P = -(2/v)Y + O, Q = (2/v)X + O, |P|^2+|Q|^2 = R_p^2/(pi^2 v^2 rho^2), and 2|Im_H(P conj Q)| = 2|Im_H(b conj a)|/(pi^2 v rho^2) using the rotation identity, which reassembles to exactly 01's formula — and I verified numerically that 01's stated certificate 1.4724221755937 (for u = 0.3, v = 1.2, a = 1 - 2i + j/2 + k, b = 1/2 + i - j + 2k) and 06's stated certificate 1.611890081993 (for u = 0.3, v = 1.7, a = 1 - 2i + j/2 + 3k, b = -0.4 + i + 2j - k) both reproduce from the SAME spherical-supremum formula. So 01 and 06 independently derived the same law and both are right. The merge must define ||g||_ax and ||g||_sph as separate symbols, state the two limits separately, and keep 01's warning that the correction vanishes iff Im_H(b conj a) = 0 and NOT iff a and b commute — the example a = 1, b = i is a commuting pair with a nonzero correction.

### 2. The symbol eta_g: which second one-form is it?

**In the sources.** 10 (eq:intro-eta) writes eta_g = (1/2)((xP+yQ)dx + (yP-xQ)dy) — the primitive-INDEPENDENT second closed form, the object the whole theory is built on. 03 (thm:fueter-inverse) writes eta = (C + rQ/2)dx + (rP/2)dr — the primitive-DEPENDENT form of the local two-integration construction, the object the nine extensions exist in order to REPLACE. 05 (eta_C), 06 (eta) and 08 use eta in 03's sense.

**Resolved.** They are different one-forms, related by eta_C - d(xC) = theta_g, which I verified directly: d(xC) = C dx + x omega_g = (C - xP/2)dx + (xQ/2)dy, and subtracting gives exactly theta_g. A merge that keeps 10's naming will silently identify the two and destroy the central argument of the paper, since the whole point (stated in 02 Remark 3.3, 04 §3.1, 05 eq:remove-primitive, 06 eq:eliminateC, 08 §3.1, 09) is that the second obstruction does NOT depend on a chosen first primitive. Adopt theta_g for the closed form and reserve eta_C for 03's form, displaying the identity that connects them.

### 3. The letter T (or script T): the Fueter map, the holomorphic invariant, or the normalized inverse?

**In the sources.** 04 (T F = Delta_4 I F), 06 (T F = Delta_4 I F) and 10 (T f = Delta_4 f) use T for the FUETER MAP. 09 (eq:intro-T, thm:T) uses T g for the HOLOMORPHIC INVARIANT equal to F''. 01 (notation table) uses script-T for the NORMALIZED INVERSE on the zero-period subspace. 02 (§7) and 07 (§6) use J for the splitting section while 04, 06, 08 and 09 use J for the invariant.

**Resolved.** Three incompatible meanings of T and two of J, each attached to a different arrow in the same commuting diagram. Nothing here is mathematically wrong, but a mechanical merge produces statements such as 'T g = F''' and 'ker T = Aff_H' in adjacent sections, which are then contradictory. Resolution: write the Fueter map as Delta_4 I(.) with no letter, the invariant as H_g, the section as S, the projection as Pi, and drop T and J entirely.

### 4. The offset symbols s and t near a singular sphere

**In the sources.** 05 (§3.2, lem:principal) sets s = x - u and t = y - v. 08 (§4.1) sets t = x - u and s = y - v — exactly swapped. 01 (notation) and 07 (§4) instead use s and t for the CENTRE, p = s + iota t. 02 and 10 use X = x - u, Y = y - v; 07 uses xi, eta for the offsets.

**Resolved.** Three mutually exclusive meanings of the pair (s,t) in a family of papers whose central formulas are written in exactly those variables. This is not a difference of opinion about mathematics but it is an assertion of incompatible things about the same symbols in formulas that the merge must place side by side; for instance 05's P = (c s + v h t)/(pi v rho^2) and 08's P = (1/pi)[((xa+b)t + r a s)/(r rho^2) + a l/r] are the same formula with s and t interchanged. Resolution: p = u + iota v for the centre, xi = x - u and eta = y - v for the offsets, and no use of s or t at all in this part of the document. I verified that once translated, all nine explicit branch-free mode formulas are literally the same function.

### 5. The hypothesis under which two residues are a COMPLETE invariant at an isolated sphere

**In the sources.** 01 (thm:critical 8.3), 02 (cor:critical 8.4), 04 (cor:removable 9.3), 06 (cor:removable), 07 (cor:critical), 08 (thm:growth (i)) and 09 (cor:sharp) all require the POINTWISE bound M_g(rho) = O(rho^{-1}). 05 (thm:L1) and 10 (thm:L1) require only LOCAL L^1 INTEGRABILITY across the sphere and reach the same conclusion.

**Resolved.** 05 and 10 are right and the other seven are strictly weaker. L^1 is a formally weaker hypothesis — O(rho^{-1}) implies L^1 since dV ~ rho d rho, but not conversely a priori — so the L^1 theorem subsumes all seven critical-growth theorems. A posteriori the two classes coincide, precisely because the L^1 theorem shows every L^1 germ equals a mode plus a smooth field and the modes are O(rho^{-1}); but that is a consequence, not a hypothesis. The boundary is exactly where 05 and 10 both place it: Delta_4 I((z-p)^{-1}c) has zero periods, exact order rho^{-2}, is NOT locally L^1 (its planar integral diverges like int rho^{-1} d rho), and is not removable. The merged document should state the classification with the L^1 hypothesis, keep both independent proofs (05's distributional defect, 10's W^{1,1} lemma), and then derive the critical-growth version as a corollary.

### 6. The growth-free energy lower bound and its leading coefficient

**In the sources.** 07 (thm:lowerenergy) proves E_g(eps,R) >= 8 int ((v-rho)^2/rho)(|a|^2 + |ua+b|^2/(v^2+rho^2)) d rho, giving liminf E/log = 8 R_p(a,b)^2, the sharp constant. 08 (thm:energybound) proves E_g >= 8 R_p^2 int ((v-rho)/(v+rho))^2 d rho/rho, also giving the sharp liminf but a weaker finite-radius correction. 01 (cor:energy-lower-general 9.5) proves the SHELL bound int_{dT_rho}|g|^2 dS >= (8(v-rho)^2/rho) max{|a|^2, |b|^2/(|p|+rho)^2}, whose leading constant is 8 v^2 max{|a|^2, |b|^2/|p|^2} — strictly SMALLER than the sharp 8(v^2|a|^2 + |ua+b|^2) whenever a and b are both nonzero.

**Resolved.** All three are true; only 07 and 08 are sharp, and 07 dominates 08 pointwise. I reproduced 07's Gram computation: the two circle functionals a = (rho/2) int (P sin phi + Q cos phi) d phi and ua+b = (rho/2) int (v P cos phi - (v sin phi + rho) Q) d phi are exactly orthogonal in L^2([0,2pi];R^2) with squared norms pi rho^2/2 and pi rho^2(v^2 + rho^2)/2, so Bessel gives 07's inequality directly, while 08 uses an operator-norm bound (v+rho)/(v-rho) and Cauchy–Schwarz, which loses the orthogonality; since (v+rho)^2 > v^2 + rho^2, 07's integrand is strictly larger. 01 openly states that its coefficient is 'not asserted to have the sharp coefficient', and with u = 0, v = 1, a = b = 1 its bound gives 8 against the sharp 16. Adopt 07's inequality, state 08's closed form 8 R_p^2[log(R/eps) + 4v/(v+R) - 4v/(v+eps)] as its corollary, and drop 01's.

### 7. Whether the remainder in the energy law is merely bounded or converges

**In the sources.** 02 (thm:energy 9.3) states the energy as 8(|ua+b|^2 + v^2|a|^2) log(eps_0/delta) + O(1). 01 (thm:energy 9.4), 05 (thm:energy), 07 (thm:exactenergy), 08 (thm:energyexact) and 10 (thm:energy) all state that subtracting the logarithm leaves an actual finite LIMIT, + E^ren + o(1).

**Resolved.** The five are right and 02 is weaker; the error analysis needed for the limit is already present in 02's own proof (the cross term is O(rho^{-1}(1+|log rho|)) and the square of the remainder is O((1+|log rho|)^2), both integrable against the area factor rho), so 02 simply did not push the statement. Adopt the finite-limit form, and adopt 01's explicit expression E^ren = int_0^R (J_g(s) - 8 R_p^2/s) ds, which is the only closed form for the constant anywhere in the family. Note also that only 08 and 10 verify the constant numerically against an independent quadrature (252 and 181 respectively, both of which I confirmed from the residue data).

### 8. Whether the criterion at a puncture is 'h_{-1} = h_{-2} = 0' or 'h_{-2} = 0'

**In the sources.** 02 (cor:residues 6.2) states that the two periods vanish exactly when the two Laurent coefficients h_{-1} and h_{-2} of the invariant both vanish, presenting them as independent. 06 (cor:momentresidues) and 08 (eq:principalK) likewise display both polar coefficients as free data. 01 (prop:Laurent-reality 8.5) and 09 (thm:res-encoding) prove that they are NOT independent: h_{-1} = (iota/v) Re_C(h_{-2}), so h_{-2} = 0 alone forces h_{-1} = 0 and hence both periods to vanish.

**Resolved.** 01 and 09 are right and 02's criterion is redundant (though true). I verified the constraint directly: a = 2 pi iota h_{-1} in H forces h_{-1} = -iota a/(2 pi); writing h_{-2} = c + iota d, the requirement b = -2 pi iota(p h_{-1} + h_{-2}) in H kills the iota-component, giving c = -v a/(2 pi), hence a = -(2 pi/v)c and b = 2 pi d + (2 pi u/v)c, and h_{-1} = iota c/v = (iota/v) Re_C(h_{-2}). It also follows that H_g can never have an isolated pole of order exactly one at a nonreal p — a statement absent from 02, 06 and 08 and consistent with their own formulas, since p a + b = 0 forces a = b = 0 when v > 0. The merged document should state the constraint as a theorem and derive the vanishing criterion in the sharp form.

### 9. Which flux, and with which weight, recovers the slope residue a

**In the sources.** 02 (cor:moments 9.2) recovers a from M_1 = int_{S_p}(q - u) sigma(q) dS_q, a MOMENT OF THE SURFACE DENSITY, obtaining M_1 = -8 pi v^3 a. 05 (prop:flux) computes only the total flux and states that it misses a. 10 (cor:twoflux) recovers a from a CONSERVED BOUNDARY FLUX Phi_1 = int_{dT_rho} H_u n g dS with the weight H_u(q) = 3(Re q - u) + Im q, obtaining the same value -8 pi v^3 a but at any finite radius.

**Resolved.** 10 is the correct and usable version, and the difference is not cosmetic. A flux weighted by the naive q - u would be the direct analogue of 02's moment, but it is NOT radius-independent: I computed sum_mu d_{x_mu}(q-u) e_mu = 1 + i i + j j + k k = -2, so q - u is not right-Fueter-regular and the Green identity does not make its flux conserved. Only the coefficient 3 repairs this: sum_mu d_{x_mu} H_u e_mu = 3 - 3 = 0. Both expressions agree numerically because H_u restricted to S_p equals q - u, but 02's requires knowing the density while 10's does not. A merge that presented 02's moment as a computable flux would be wrong. The merged document should also record the identification, absent from both, that H_u = -(1/4)Delta_4((q-u)^3) = 3 P_1(q-u) is exactly the degree-one entire axially monogenic polynomial of 01 and 04 — I verified Delta_4(q^3) = -4(3x_0 + Im q) symbolically — so the two residues are recovered by pairing the field against the two lowest entire axially monogenic polynomials.

### 10. Whether the approximating rational slice functions have quaternionic coefficients

**In the sources.** 09 (§sec:runge) states that the rational stems are 'upper-stem rational functions; after reflection to the lower component their induced slice functions need NOT be rational functions with coefficients in H on a connected symmetric planar domain'. 10 (thm:runge) states for its class that 'a common denominator can be chosen to be a real polynomial with zeros in E, and the numerator has right quaternionic coefficients' — i.e. they ARE genuine rational slice functions with H coefficients.

**Resolved.** Both are right, because the pole sets differ, and the merged document must say so or the two statements read as a flat contradiction. 09's pole set is ONE-SIDED (only the chosen upper points), so the reflected function is defined piecewise and is not a single rational function. 10's pole set E = {p_j, conj p_j} is conjugation-symmetric, and then the symmetrization argument does give H coefficients: I checked that if R is rational with R(conj z) = kappa(R(z)) and poles in a symmetric set, taking the common denominator d(z) = prod (z - p_j)^{m_j}(z - conj p_j)^{m_j}, which has real coefficients, forces the numerator N = Rd to satisfy N(conj z) = kappa(N(z)) and hence to have coefficients in H. 02 and 07 also use symmetric pole sets and so agree with 10. Adopt both statements with their pole-set hypotheses displayed.

### 11. How the 8m count is indexed: upper-meridian winding basis, or conjugation-exchanged hole pairs

**In the sources.** 01 (thm:realaxis 6.2), 05 (remark after thm:exact), 06 (prop:reflected) and 09 (cor:real-holes) count m as the size of a finite winding basis of the UPPER MERIDIAN U = D ∩ {y > 0}. 02 (lem:holes 4.2), 04 (thm:reflection-range 7.3), 07 (thm:range), 08 (thm:reflection) and 10 (thm:real-holes) count m (or h, or k) as the number of CONJUGATION-EXCHANGED PAIRS of complementary components of D.

**Resolved.** The two counts agree, but no manuscript on either side proves the equivalence, and each presents its own index as the definition. The missing link is in exactly one place: 07 (§sec:topology) proves that every conjugation-INVARIANT hole meets the real axis, since a connected reflection-invariant set avoiding the axis would split into disjoint upper and lower parts. Given that, invariant holes produce no cycle in the upper meridian, and each exchanged pair produces exactly one — so the two indices coincide. The merged document must state 07's lemma explicitly and derive the identification; otherwise the reflection theorem and the product-domain theorem look like two different theorems with two different m's. 08's phrasing 'not 8(s + 2k)' and 04's Remark 7.4 'the answer is not eight times the first Betti number' should both be kept as the warning.

### 12. Whether the normalization C(z_*) = V(z_*) = 0 is four conditions or eight

**In the sources.** 01 (thm:continuous 5.2) and 05 (cor:normalization) describe it as the unique primitive that vanishes on the ENTIRE sphere x_* + y_* S. 04 (remark after cor:local 3.3) and 09 (Remark after thm:global) describe it as equivalent to F(z_*) = 0 in H_C — eight real conditions — and warn that it is explicitly NOT the four-real-dimensional condition f(x_* + I_* y_*) = 0 at one quaternionic point.

**Resolved.** These are the same fact stated in opposite-looking language and both are correct: vanishing of A + IB at every I in S forces A(z_*) = B(z_*) = 0, which is exactly F(z_*) = 0, which is eight real conditions, and the map (a,b) -> z_* a + b from H^2 to H_C is a real isomorphism because y_* > 0. A careless merge would install two different normalizations of the same inverse operator. State it once, with both descriptions and the isomorphism that reconciles them.

### 13. Where the arctangent / spherical Cauchy kernels come from, and whether a published surjectivity statement is being corrected

**In the sources.** On attribution: 09 (§sec:real) cites Colombo–Sabadini–Sommen 2011, Theorem 5.1, for the arctangent primitives and sphere-integrated Cauchy kernels; 01 (rem:known-modes 4.2), 02 (honest limitations), 05 (§1.3), 06 (§ counterexample) and 10 (Remark on known kernels) all cite Colombo–Pena Pena–Sabadini–Sommen 2014, Example 2, instead. 01 goes further and asserts the specific normalization G_{iota;0,1} = 2 N^+ and G_{iota;1,0} = 2 N^-, which no other manuscript states. On the editorial question: 06 (§1.1) asserts that an unqualified same-domain surjectivity sentence in Kraussharr–Perotti, Annali di Matematica 201 (2022), §4, p. 2539, 'needs a topological qualification' and that its counterexamples address it; 07 (§1.1) and 08 (§1.2) instead take Perotti, CMFT 24 (2024), Theorem 2 — surjectivity when every component of the symmetric planar set is simply connected — as the correct predecessor whose hypothesis is being removed; 04 (§12.2), 05 (§1.1), 08 (Remark after thm:reflection) and 10 explicitly decline to assert that any published theorem is incorrect.

**Resolved.** Two separate disagreements, neither resolvable from the manuscripts alone. On attribution, at most one of the two cited loci is the primary source for the arctangent kernels; the merged bibliography must check both papers directly before printing either, and 01's identification with N^+ and N^- should be stated only with its normalization spelled out (I confirmed it is internally consistent with 01's own definitions: L_iota' = 1/(pi(1+z^2)) makes L_iota = arctan(z)/pi up to a constant, so a kernel with primitive arctan(z)/(2 pi) is half of G_{iota;0,1}). On the editorial question, the positions are mutually incompatible as stances even though no two contradict on mathematics: 06 alone names a published sentence as needing correction, while four others pre-emptively deny doing so. The merged document must take exactly one position. The defensible one is 08's and 04's: state the necessary-and-sufficient criterion, exhibit the explicit obstructed fields on H \ S, observe that an unqualified same-domain surjectivity assertion is therefore false as stated, and decline to adjudicate any particular published theorem without auditing its own domain, locality and branch hypotheses.


## Notation

One symbol per concept, throughout.  The table below is the reconciliation; the
right-hand column is what the sources called the same thing.

| concept | this document | in the sources |
|---|---|---|
| The Cauchy–Fueter operator, its conjugate, and the Laplacian | `D = d_{x_0} + i d_{x_1} + j d_{x_2} + k d_{x_3}; conj(D); Delta_4 = conj(D)D = D conj(D) = sum_{mu=0}^3 d^2_{x_mu}. No factor 1/2 anywhere; normalization Delta_4 q^2 = -4.` | D or cD or \Dir or \D in all ten; Delta_4 as \lap (02,03,05,06,07,10), \Lap (08,09), \Fu (01), \Lap/\lap (04). Unanimous content. |
| The Fueter map on stems, f = I(F) -> Delta_4 I(F) | `Write it as Delta_4 I(F) throughout; NEVER abbreviate it by a single letter T.` | T F (04, 06, 10), Fu F (09), plain Delta_4 (01, 02, 05, 07, 08). Banned because 09 uses T for the holomorphic invariant and 01 uses script-T for the normalized inverse; three incompatible meanings of one letter. |
| The planar base and its circularization | `U for a connected open subset of C^+ = {x + iota y : y > 0} (product setting); D for a connected conjugation-invariant planar set meeting R (slice setting); Omega_U and Omega_D for their circularizations.` | Identical in all ten, except that 07 also uses D for the operator; the merged document uses D only for the planar set and writes the operator as D in upright math with a fixed macro, or renames it. 04 additionally uses D_zeta for a squared distance — replaced below by rho^2. |
| The two coordinates of a point of the base | `z = x + iota y with y > 0; q = x + Iy with I in S.` | r for the axial radius in 01, 04, 06, 08, 09; y in 02, 03, 05, 07, 10. Adopt y and reserve r, R for radii of balls and tubes. |
| The centre of a singular sphere and the offsets from it | `p = u + iota v with v > 0; S_p = u + vS; xi = x - u; eta = y - v; rho = /z - p/ = dist(q, S_p).` | CRITICAL COLLISION. Centre: p = s + iota t (01), p = u + iota v (02, 05, 06, 08, 09, 10), zeta = s + iota t (07), zeta = u + iota v (04, 08). Offsets: s = x-u, t = y-v (05); t = x-u, s = y-v (08 — exactly swapped); X = x-u, Y = y-v (02, 10); xi = x-s, eta = y-t (07). So s and t mean the centre in 01/07 and the offsets, in opposite orders, in 05 and 08. Nothing may be merged until this is normalized. |
| The axial components of the target and of the primitive stem | `g(x+Iy) = P(x,y) + I Q(x,y); F = A + iota B holomorphic with F(conj z) = kappa(F(z)); f = I(F)(x+Iy) = A + IB.` | Unanimous in all ten. 03 additionally uses C and H for the two components of Delta_4 f — a collision with the potentials below; the merged document does not reuse those letters. |
| The two potentials | `C = B/y (the slope potential) and V = A - xB/y (the constant potential); dC = omega_g, dV = theta_g, f(q) = qC + V, F(z) = zC + V.` | C and E (01, 06, 09), C and H (02, 04), C and D_0 (05), C and V (07), C and D (08, 10). H collides with the quaternions and with 01's invariant; E collides with the Cauchy–Fueter kernel and with the energy; D collides with the operator and the planar set. Only 07's V is free. |
| The two closed one-forms | `omega_g = (1/2)(-P dx + Q dy) (first, slope) and theta_g = (1/2)((xP + yQ)dx + (yP - xQ)dy) (second, constant). Reserve eta_C = (C + yQ/2)dx + (yP/2)dy for the PRIMITIVE-DEPENDENT form of the local construction, with eta_C - d(xC) = theta_g.` | omega/beta (01), alpha_0/alpha_1 (02), omega/theta (04, 06, 07, 09), alpha/beta (05, 08), omega/eta (10), omega/eta (03, primitive-dependent). 10's eta_g and 03's eta are DIFFERENT OBJECTS differing by d(xC); 01/05/08's beta_g collides with 04's beta_gamma, which is a period, not a form. |
| The two periods (the affine monodromy coefficients, the spherical residue) | `a_gamma(g) = oint_gamma omega_g (the slope period) and b_gamma(g) = oint_gamma theta_g (the constant period); Per for the total period map; res_{S_p}(g) = (a,b) for the pair taken on a small positive circle about p.` | a_gamma, b_gamma (01, 02, 05, 06, 07, 08, 09, 10); alpha_gamma, beta_gamma (04); (h,k) with Res^aff (05's residue definition); res^aff (04, 06); a(g;p), b(g;p) (09); res_{p,1}, res_{p,0} (10). Note 10's res_{p,1} is the SLOPE residue and res_{p,0} the CONSTANT one, the reverse of the subscript convention used for the modes. |
| The logarithmic modes | `G_{p;a,b} = Delta_4 I( ((za+b)/(2 pi iota)) log(z-p) ), with period pair wind(gamma,p)(a,b); G^sym_{p;a,b} for the reflected version built from (1/(2 pi iota)) log((z-p)/(z - conj p)). Basis: G_{p;1,0} (slope mode) and G_{p;0,1} (constant mode).` | G_{p;a,b} (01), K_p^{(1)}/K_p^{(0)} and G_p^{(j)} (02), A_zeta/B_zeta and A^sym/B^sym (04), Psi_a/Phi_a (05), G_{p,a,b}/G^sym (06), G_zeta^{a,b}/K_zeta^{a,b} (07), E_zeta(a,b) (08), G_{zeta;a,b}, U_zeta, V_zeta and hat-G (09), G_{p,1}/G_{p,0} and T I(H_p) (10). Nine names for one family. |
| The holomorphic invariant and its Laurent coefficients | `H_g = -(1/2)(P + y P_y) - (iota y/2) P_x = (1/2)(-P + y Q_x - iota y P_x) = F''; expansion H_g = sum_n h_n (z-p)^n with h_n in H_C.` | H_g (01), W_g (02), J g (04, 06), J g = K (08), T g = J_g (09). Coefficients c_n (01, 02, 04, 06), j_n (09). 01's H collides with the quaternions and with 02/04's second potential H; 09's T collides with the Fueter map. |
| The moment-real class (the exact image of the invariant) | `O_mom(U) = {h holomorphic U -> H_C : oint_gamma h dz in H and -oint_gamma z h dz in H for every closed gamma}.` | O_mom (04), the two displayed conditions unnamed (06, 08), Hol_ra (09). Absent from 01 and 02. |
| The affine kernel | `Aff_H = {q -> qa + b : a, b in H}.` | Aff_H (01, 04, 06, 07, 08, 09, 10), written out (02, 03, 05). |
| The splitting section and the projection | `S for the right inverse of Per, Pi = id - S Per for the projection onto the Fueter image.` | S and Pi (01, 05, 06, 09), J and (id - J Per) (02, 07), S and R (06 uses R for the projection), S and Pi_U (10), S (04, 08). 02/07's J collides with the invariant in 04/06/08/09; 06's R collides with radii; 01's script-S is fine. |
| The two norms on an axial field, and their sphere/tube maxima | `//g//_ax(z) = (/P/^2 + /Q/^2)^{1/2} (axial pair norm) and //g//_sph(z) = max_{I in S} /P + IQ/ (spherical supremum), with //g//_ax <= //g//_sph <= sqrt2 //g//_ax; M_g(rho) = max_{/z-p/ = rho} //g//_sph and m_g(rho) = max_{/z-p/ = rho} //g//_ax. A bare M_g is never written.` | MOST DANGEROUS COLLISION. M_g(rho) means the SPHERICAL SUPREMUM in 01, 02 and 06 but the AXIAL PAIR NORM in 10; the pair norm is N_g in 05, //g//_ax in 08, m_g in 09, //g//_K (spherical) in 06, //g//_{Omega_K} (spherical) in 07. The two differ by up to sqrt2 and carry DIFFERENT sharp asymptotic constants. |
| The residue norm | `R_p(a,b)^2 = /ua + b/^2 + v^2 /a/^2 = //pa + b//^2_{H_C}, positive definite and invariant under a real translation of the origin.` | script-R_p (01), Q_a(h,k) (05), q_zeta(a,b) (07), W_{u,v}(a,b) (08), S = /c_0/^2 + /c_1/^2 (10), written out (02, 06). Five names for one quantity. |
| The pair norm on H^2 governing the spherical supremum | `n(alpha,beta) = max_{I in S} /beta + I alpha/ = (/alpha/^2 + /beta/^2 + 2 /Im_H(beta conj alpha)/)^{1/2}.` | the fraktur n of 06; unnamed in 01, which writes the identity max_I /P+IQ/^2 = /P/^2 + /Q/^2 + 2/Im_H(P conj Q)/ instead. Absent from the other eight. |
| Energy, the shell density, and the renormalized constant | `E_g(eps,R) = int_{eps < rho < R} /g/^2 dV; J_g(rho) = int_{dT_rho} /g/^2 dS; E^ren_g(R) for the finite remainder. Reserve E(q) = conj q/(2 pi^2 /q/^4) for the Cauchy–Fueter kernel alone.` | E_g(eps,R) (07), script-E_g (08), E(eps,R) and J (01, 05), unnamed truncated integral (02, 10). The letter E simultaneously denotes the Cauchy–Fueter kernel (03, 05, 06, 07, 10), the second potential (01, 06, 09), the energy (01, 05, 07, 08) and a pole set (10). |
| The surface source | `D g = sigma_p delta_{S_p} with sigma_p(s) = (2/v)(sa + b) for s in S_p; delta_{S_p} is surface measure, not a probability measure.` | sigma(q) = (2/v)(qa+b) (02), sigma_a(p) (05), 2((ua+b)/v + I_p a) (07), j_{a,b}(q) (10). Identical after expanding s = u + I v. |
| Counting symbols | `m = rank of the winding basis of the upper meridian = number of conjugation-exchanged hole pairs; l = number of conjugation-fixed holes (contributes nothing); n = number of singular spheres; N = transverse growth order; k = Laurent index; d = polynomial degree at infinity.` | CHRONIC COLLISION. Holes: m (01, 05, 06, 09, 10), h (02, 04, 07), k (08). Fixed holes: s (02, 04, 08), l (01). Spheres: m (01, 05), t (04), h (07), n (none). Growth order: N (02, 06, 07, 08, 09), m (04). Laurent index: k (02, 07, 08, 09), m (06), i (04). 08 uses k for BOTH the number of conjugate pairs and the Laurent index; 04 uses t for the number of spheres while 01 and 07 use t for Im p. |
| Entire axial polynomials and the flux weights | `P_k(q) = -Delta_4(q^{k+2})/(2(k+1)(k+2)), normalized by P_k(x) = x^k on R; flux weights P_0 = 1 and 3 P_1(q-u) = 3(Re q - u) + Im q.` | script-P_k (01), Delta_4(q^{n+2}) a_n unnormalized (04), H_u (10). The identification 3P_1(q-u) = H_u = -(1/4)Delta_4((q-u)^3) is verified and is new to the merge. |
| The two residue notions inherited from Part I, kept apart from the new one | `Res_c f for the slice Laurent residue at a REAL isolated singularity; Res^F_a f = int_{/q-a/=r} n(q) f(q) dS_q for the isolated-point Fueter flux residue; res_{S_p}(g) = (a,b) for the affine SPHERICAL residue. Three distinct objects, three distinct symbols, never abbreviated to a bare Res.` | Res and Res^F (03); res^aff (04, 06); Res^aff (05); 'affine period residues' (08); 'affine spherical residues' (09); res_{p,0}, res_{p,1} (10); Res in 06's preamble macro. 02 writes Res for the ordinary complex residue of the invariant, a fourth meaning. |

## Bibliography

The ten bibliographies hold 81 `\bibitem` entries naming 26 distinct works.
Three are cited by all ten manuscripts: Ghiloni--Perotti (2011),
Colombo--Sabadini--Sommen (2011), and
Colombo--Peña Peña--Sabadini--Sommen (2014).  The merged bibliography
lists each work once.  The supplied expository manuscript is not among them: it
is Part I of this document.

One attribution is left open deliberately.  The manuscripts disagree about
which paper is the primary source for the arctangent / spherical Cauchy
kernels, and the disagreement cannot be settled from the manuscripts
themselves; both loci are cited, and the merged text says that the question is
unresolved rather than picking one silently.

