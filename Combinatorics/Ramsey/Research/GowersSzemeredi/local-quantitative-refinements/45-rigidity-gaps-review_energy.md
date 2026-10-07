# Internal AI proof cross-check: ordered-energy results

Status: this is an internal AI-assisted proof cross-check performed within the preparation workflow. It is not a human peer review, an external referee report, or a proof-assistant verification.

The original review examined the ordered-energy proof notes subsequently incorporated into `sections/energy.tex`; the final section was checked for incorporation of the simplification and minor correction below.

## Verdict

The stated first-gap bound, complete second-level classification, unit-Schur-defect classification, third-level exclusion bound and construction, and torsion-free extension are correct. I found no substantive gap in the analytic proofs. The adopted reordering—prove the unit-Schur-defect lemma before second-level equality—substantially simplifies the second-level proof and avoids relying on the four-point classification.

There is one minor off-by-one sentence in the sharpness discussion, recorded below. The publication-priority cautions are appropriate: in particular the first-gap estimate follows from published inverse Pollard theory and should not be claimed as a new bound.

## 1. Endpoint identity and zero defect

The recurrence

\[
 E(A)=E(B)+4m-3+4T(B,a),\qquad D(A)=D(B)+e(B,a)
\]

has the correct multiplicities. Exactly two occurrences of the largest element have to occur on opposite sides of the equation; the remaining two entries must coincide, giving `4(m-1)`. The all-largest quadruple contributes the remaining `1`.

Each ordered pair `z<x` in `B` determines at most one candidate `y=a-x+z`, so the formula for `e` counts failed pairs exactly. The completed point lies strictly between the smallest and largest members of the corresponding ordered triple, validating the global identity

\[
 D(A)=\#\{x<y<z\in A:x+z-y\notin A\}.
\]

The proof of `e=0` is also correct. Once `D^+(B)=B\setminus\{0\}`, subtraction by its least positive member stays in `B` until zero. This gives every element as an integral multiple of the least difference and fills the intermediate multiples. No discreteness assumption about the original real set is being smuggled in.

## 2. Unit Schur defect

The proof covers all possible locations of the unique deficient index.

* Before that index, the reflection equalities force `c_i=id`.
* If the deficient index `k>=3`, its positive representation count forces `c_k` to be an integer multiple of `d`; the count `k-2` gives `c_k=(k+1)d` exactly. If a subsequent index existed, its reflection would send the present point `2d` to the absent point `kd`, a contradiction.
* If `k=2`, the next two reflection equalities (available because `n>=4`) imply `c_3=d+c_2`, `c_4=2d+c_2=2c_2`, contradicting the unique defect at index two.

The transformation `C=a-B` preserves the ordered Schur-triple count exactly. For `min B=0`, `max C=a`, so `e(B,a)=1` and `|B|=n>=4` give

\[
 a=(n+1)d,\qquad B=\{0,2d,3d,\ldots,nd\}.
\]

Thus the conclusion about the entire extended set `A` needs no hypothesis on the energy of `B`. This is the precise strong form needed by the third-level induction.

## 3. Simplified complete second-level classification

The simplified proof adopted in the final section is valid for `m>=5`:

1. If `B` is an AP, the explicit endpoint calculation gives the right-hole set `H_m`.
2. If `B` is not an AP, the first-gap inequality gives `D(B)>=m-3`, while zero endpoint defect is impossible. Equality `D(A)=m-2` therefore forces `e(B,a)=1`.
3. The unit-Schur-defect lemma applies because `|B|=m-1>=4` and immediately gives the left-hole set `L_m`.

The four-point list is independently correct, but can be an optional small-cardinality proposition instead of an inductive prerequisite. In the four-point calculation the three positive differences of a non-AP triple are indeed distinct, and checking their two-at-a-time successes gives precisely the parallelograms and the reflected `H_4` case listed in the notes.

## 4. Third-level induction

All three prefix cases work:

* An AP prefix with a nonexceptional extension has endpoint defect at least `2n-3`, exceeding the needed `2n-4`.
* A second-level prefix has `D(B)=n-2`. In either normalized orientation its difference `1` has multiplicity `n-2`. It fails for every integer endpoint `a>=n+2`; all differences fail for a noninteger endpoint. At `a=n+1`, the right-hole prefix instead has its difference `2` fail with multiplicity `n-2`, while the left-hole prefix extends to another excluded second-level set. These are all possibilities.
* For a nonexceptional prefix, induction gives `D(B)>=2n-6`; endpoint defects `0` and `1` are excluded by the two endpoint lemmas, hence `D(A)>=2n-4`.

The base `m=5` follows from integrality and second-level equality: a nonexceptional set has `D>3`, thus `D>=4`.

The sharpness construction is correctly counted. For `B=R_n` and `a=n+1`, every positive difference except `2` is successful, and difference `2` has multiplicity `n-2`. Its total defect is exactly `2n-4=2m-6`. Since `m>=5`, this is strictly larger than `m-2`, proving directly that the construction is not a second-level set.

### Minor correction incorporated

A gap-sequence sentence in the original proof notes was off by one; this has been corrected in the final manuscript. In the **gap sequence**, `H_m/L_m` have the gap `2` at the last/first position, whereas `J_m` and its reflection have it at the second/penultimate position. The final manuscript correctly distinguishes an interior gap from a first or last gap. The already computed, distinct energy defects also establish nonexceptionality directly.

## 5. Torsion-free extension

The extension is valid because only the finitely generated subgroup containing `A` needs to be embedded in the real line. Such a subgroup is `Z^r`, and choosing `r` rationally independent real numbers gives an injective additive map.

Additive quadruples are preserved in both directions. For an extremal model in the image, its common step is an actual difference of two image points, so it lifts to the group and injectivity pulls back all model relations. This handles the AP, right-hole, and left-hole classifications. It does not require an embedding of an arbitrary, possibly very large, torsion-free ambient group into the real line.

The finite cyclic limitation is necessary and is correctly stated. The torsion-free maximum `M_m` is a different endpoint from the finite-subgroup maximum `m^3`.

## 6. Published first-gap implication

I independently opened the primary PDF:

E. Nazarewicz, M. O'Brien, M. O'Neill, C. Staples, *Equality in Pollard's theorem on set addition of congruence classes*, Acta Arithmetica 127.1 (2007), Theorem 3.

URL: https://www.impan.pl/shop/en/publication/transaction/download/product/82135

For `2<=t<=m-2`, sufficiently large prime modulus, and `(A,-A)` with a non-AP `m`-set, its four equality alternatives are all excluded. Vosper handles `t=1`. Thus the strict popular-sum inequality asserted in the notes follows from this primary source.

The parity strengthening and layer-cake calculation in the notes are correct. Since nonzero differences come in opposite pairs,

\[
 S_t\equiv t\pmod2,
\]

so strictness yields an excess of at least `2` at each `1<=t<=m-2`. The identity

\[
 E(A)=(2m-1)m^2-2\sum_{t=1}^{m-1}S_t
\]

then gives the first gap `4(m-2)` exactly.

Two presentation details will keep this attribution airtight:

1. To cover real or torsion-free sets, say explicitly that the finite set can first be mapped to the integers by a Freiman 2-isomorphism. Identify its finitely generated subgroup with `Z^r` and choose a sufficiently large integer linear functional avoiding the finitely many nonzero elements of `2A-2A`. Then choose a prime avoiding wraparound. This is a finite-set construction; it is not an injective group embedding `Z^r -> Z`.
2. The PDF's extracted text drops the complement bar in the exceptional case of **Vosper's** theorem on page one. Its exceptional large complementary-set case is excluded by choosing a sufficiently large prime. Do not accidentally read it as saying that every `(A,-A)` is Vosper-critical. In inverse Pollard's Theorem 3, the case `|A|=|B|=t+1` with `B=g-A` is genuinely without a complement, and is excluded for `t<=m-2`.

This establishes that the first gap is already implicit in published work. The elementary proof and the two finer structural statements can still be presented as additions to the pinned repository, with publication priority for the latter expressly unestablished. I did not find a reason to weaken those structural theorems themselves.

