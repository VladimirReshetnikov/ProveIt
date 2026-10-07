# Internal AI cross-check: abstract, introduction, and applications

Date: 7 October 2026 UTC.

This is an internal AI mathematical cross-check of the manuscript, not external peer review or proof-assistant verification. The scope is the abstract and `sections/introduction.tex` and `sections/applications.tex`, with the relevant statements in `sections/u4.tex`, `sections/cosets.tex`, Gowers's Section 3, and the pinned preceding ProveIt report consulted for comparison. The check concerns logical implications, normalization, numerical constants, and the stated division between earlier results and present extensions. It does not establish worldwide publication priority.

## Verdict

The fourth-order expansion, its extension to every finite abelian group of odd order, the improved uniformity multiplier, and the indicator formulation are mathematically correct under the stated hypotheses. The bounds in the abstract and introduction agree with the body of the manuscript. The prior-versus-present comparisons are appropriately limited to the sources inspected.

Two small wording corrections were communicated to the manuscript editor: distinguish positive-defect coset equality from zero defect in the abstract, and restrict the statement about a character's unit Gowers norms to orders at least two. Two further suggested clarifications concern Gowers's degree convention and the absence of a full third-energy equality classification. The precise recommendations appear below; this report records the reviewed draft, so the editor may already have incorporated them.

## 1. Centering cancels all terms through degree three

For three distinct Boolean vertices, translate the affine base point by the first vertex and reflect the appropriate cube coordinates. The first vertex becomes zero, and the other two become distinct nonzero Boolean row vectors. Their supports provide a minor of determinant ±1:

- If neither support contains the other, use one coordinate from each support difference.
- If one is properly contained in the other, use one coordinate in the smaller support and one in the difference.

Together with the affine base variable this gives a unimodular three-variable submap. It is invertible on every abelian group; conditioning on the remaining coordinates proves joint uniformity. The same argument with fewer variables handles one and two vertices. Consequently every corresponding centered correlation vanishes. No restriction on odd order is used at these degrees.

## 2. Affinely dependent four-vertex supports are parallelograms

Any three distinct Boolean vertices are affinely independent over the reals. Thus four dependent vertices span an affine plane. Projection onto two appropriately chosen coordinates is injective on this plane, because its linear part has rank two. The images of the four vertices are distinct points of the two-dimensional Boolean square and hence are all four corners. Applying the inverse affine map gives an ordinary parallelogram relation among the original vertices.

The joint uniformity of any three vertex forms then identifies the fourth moment with

\[
\mathbb E_{a,b,c} f(a)f(b)f(c)f(a+b-c)
=\|f\|_{U^2}^{4}.
\]

This identification uses realness, as assumed. It does not silently discard complex conjugations from a complex-valued assertion.

## 3. Affinely independent four-vertex supports vanish on every odd-order group

After the same reflection, choose a nonsingular three-by-three Boolean minor \(B\). The bordered matrix

\[
\begin{pmatrix}1&\mathbf 1^{T}\\\mathbf 1&J-2B\end{pmatrix}
\]

has entries ±1. Subtracting its first row from the remaining three rows proves that its determinant is \(-8\det B\). Its four row norms are two, so Hadamard's inequality gives \(8|\det B|\le16\). A nonzero integer determinant is therefore ±1 or ±2.

Multiplication by two is an automorphism of every finite abelian group of odd order. Thus multiplication by \(\det B\) is invertible, and the adjugate formula proves that the selected coordinate map is invertible. Including the affine base variable gives joint uniformity of the four forms, so their centered correlation vanishes. Primality, cyclicity, and the absence of three-torsion are not needed. In particular, the proof applies to products of odd-order groups and to odd prime powers.

As a small independent arithmetic diagnostic, all 512 three-by-three Boolean matrices were enumerated using the integer determinant formula. The distribution was

| Determinant | −2 | −1 | 0 | 1 | 2 |
|---|---:|---:|---:|---:|---:|
| Number of matrices | 3 | 84 | 338 | 84 | 3 |

The universal argument rests on the displayed determinant proof, not this enumeration.

## 4. The coefficient and the remainder

There are six ordered one-coordinate solutions of \(a+b=c+e\) in \(\{0,1\}\), hence \(6^d\) on the Boolean cube. The two identical-pair families have total size \(2\cdot4^d-2^d\). Every other solution has four distinct vertices: a repeated entry either cancels across the equation or forces all entries to coincide coordinate by coordinate. Each parallelogram support has eight ordered representations. Thus

\[
P_d=\frac{6^d-2\cdot4^d+2^d}{8}
\]

is correct, including \(P_2=1\), \(P_3=12\), \(P_4=100\), and \(P_5=720\).

For a centered term with \(r\) selected vertices, apply the cube Cauchy–Schwarz inequality with \(f\) at those vertices and the constant function one elsewhere. It gives the absolute bound \(\|f\|_{U^d}^{r}\), since \(\|1\|_{U^d}=1\). Summing by support size gives precisely the stated remainder. There is no missing group-size factor and no requirement that \(f\) be bounded by one. At \(d=2\) the remainder is empty and the formula becomes the exact identity \(Q_2(\rho+f)=\rho^4+Q_2(f)\). Values with \(\rho=0\) are interpreted as the displayed polynomial, so the zero exponent contributes one.

## 5. Uniformity exponent and the original notation

The present convention is \(Q_d(f)=\|f\|_{U^d}^{2^d}\), with probability averages. Gowers's norm in Lemma 3.10 uses unnormalized sums, so its \(2^d\)-th power is \(N^{d+1}Q_d(f)\). His condition “\(\alpha\)-uniform of degree \(d-1\)” is exactly

\[
Q_d(f)\le\alpha.
\]

Writing \(q=2^d\), this means \(u\le\alpha^{1/q}\); the quartic term therefore has exponent \(4/q\), and the term of degree \(r\) has exponent \(r/q\). The number of ordered additive cubes is \(N^{d+1}Q_d(1_A)\). All factors and exponents in the application agree with Gowers's Lemma 3.10. His comparison \(N^{d+1}(\rho+\alpha^{1/q})^q\) is quoted correctly.

Suggested clarification: explicitly add that \(\|f\|_{U^d}^{q}\le\alpha\) is Gowers's “\(\alpha\)-uniform of degree \(d-1\)” condition. The inequality as written is already correct; the sentence would make the degree shift visible.

## 6. The fourth-order constant and its propagation

The main uniformity theorem gives

\[
\|f\|_{U^4}^{16}\ge\frac{4795}{832}\|f\|_{U^2}^{16}.
\]

Taking a fourth root gives exactly

\[
\|f\|_{U^2}^{4}\le\kappa\|f\|_{U^4}^{4},
\qquad \kappa=(832/4795)^{1/4}.
\]

For \(d\ge4\), monotonicity permits replacing the last factor by \(\|f\|_{U^d}^{4}\). This proves the proposed leading coefficient, with no additional exponentiation of \(\kappa\). The lower bound on the cube excess follows from \(\|\rho+f\|_{U^d}\ge|\mathbb E(\rho+f)|=\rho\).

Independent decimal evaluation gives

\[
\begin{aligned}
\kappa&=0.6454070108505990837483\ldots,\\
100\kappa&=64.54070108505990837483\ldots,\\
100/\sqrt2&=70.71067811865475244008\ldots,\\
100(1-\sqrt2\kappa)&=8.72566520044034597281\ldots.
\end{aligned}
\]

The stated 8.73 percent decrease is therefore correct. It concerns the quartic coefficient relative to the preceding \(1/\sqrt2\) bound. It is not a claim that the full cube upper bound or a global density-increment bound improves by that percentage. The manuscript correctly makes this distinction.

The lower endpoint in the abstract also checks:

\[
(39037448/404304625)^{1/4}
=0.5574336443118300911711\ldots.
\]

## 7. Attribution and scope

The pinned previous report explicitly contains the centered cancellation, the quartic coefficient \(P_d\), the Boolean-minor proof on odd-order groups, and the sharper third-order multiplier \(1/\sqrt2\). It also states that the higher-dimensional optimal constants remain open. The applications correctly credit these inputs and claim the smaller fourth-order multiplier as the new substitution. The surrounding text does not present the quartic expansion as newly discovered.

The introduction credits the classical torsion-free maximum, the first gap implicit in inverse Pollard, and Hegyvári's endpoint recurrence/congruence/construction. It limits the further energy claims to results proved beyond the statements found in inspected sources. It similarly credits the prior coset envelope for defect at most \(1/100\) while identifying the enlarged range, remainder, and equality conclusions as the present additions. The comparison with the different macroscopic energy and norm-extremizer settings is appropriately qualified.

The application of the first three energy levels with the strict threshold \(E(A)>M_m-8(m-3)\) is correct for \(m\ge5\): the set is a progression or the classified second-level model. The text correctly states that this does not improve the general Balog–Szemerédi exponent. The discussion of collision counts also retains the distinction between a necessary domain geometry and label compatibility. No claimed new global Szemerédi threshold follows from these local results alone.

## 8. Wording corrections identified in the draft

1. The abstract says that every coset-envelope equality case is a coset with a subcoset removed. Zero defect is instead an unpunctured coset. Use “every positive-defect equality case,” or list the unpunctured case explicitly.
2. The introduction says that a nontrivial character has all its Gowers norms equal to one. Under the manuscript's declared convention, its \(U^1\) seminorm is zero. Use “all its \(U^j\) norms for \(j\ge2\) are one.” The same wording occurs in the uniformity section and should be made consistent there.
3. The phrase “two further classifications” following the inverse-Pollard discussion could suggest a full third-level equality classification. “The second-level classification and third-level exclusion” states exactly what is proved.
4. Add the degree-\(d-1\) uniformity dictionary mentioned in Section 5 of this report if it is not already supplied by the final normalization appendix.

These are exposition corrections. The review found no failure of the main application inequalities or of their stated quantitative constants.
