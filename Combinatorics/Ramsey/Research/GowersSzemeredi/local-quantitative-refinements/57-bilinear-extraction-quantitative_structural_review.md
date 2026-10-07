# Independent proof and arithmetic review

This is an AI-assisted internal mathematical review performed during preparation
of the article. It is not external peer review or proof-assistant verification.
The review inspected the full arguments, rather than relying on the finite
enumerations. Baseline repository commit:
`128f514afce0bf7eb48133fb30dd3f8e034ea3a2`.

## Quantitative Section 13 proof

The exact initial fibre exponent is 14,409,429. Keeping that value yields
the purification count exponent 44,943,021,421 and the safe integer density
exponent D=2,996,201,429. The resulting exact comparison exponents are
2,109,325,806,153 for square density and 6,283,489,820,278,788 inside the
double-exponential length parameter. They are strictly smaller than 2^41
and 2^53, respectively. The explicit purification threshold exponent
89,669,901,532 is strictly smaller than 2^37.

The proof checks included:

- The initial Fourier selection works for disc-valued functions: the U2
  fourth moment is bounded by the square of the largest Fourier modulus,
  because Parseval supplies a squared-mass bound of one.
- The article uses a forward derivative D_h f(x)=f(x+h) conjugate(f(x)),
  while the original/pinned difference is f(x) conjugate(f(x-h)). Their
  iterated derivatives differ by translation by minus the sum of the
  directions. Fourier coefficients at the same frequency therefore differ
  by a unit scalar, and the modulus hypotheses and conclusions agree.
- Both fibre restrictions retain their precise energy normalization, and
  restrictions in the second direction preserve the first Freiman property.
- The Fejer feature relation is a formal polynomial identity, and all
  unintended bounded relations are charged using a polynomial zero count.
  Prime characteristic injectivity is supplied by the explicit threshold.
- Repeated physical vertices are selected once. Their actual good survival
  probability is at least the labeled product, which is the direction needed.
- A single positive score gives retained mass and a high good proportion in
  the same selected subset. Independence between different arrangements is
  never used.
- The earlier square-extraction theorem has one threshold for all actual
  densities above a fixed positive lower bound. Its output includes proper
  progressions, equal lengths, the same nonzero step, retained original-domain
  support, and agreement with a global multiaffine formula.
- Near the U4 endpoint, phase normalization has loss at most two in the
  cube defect, by the pointwise inequality 1-r <= 2(1-Ar) for 0<=A<=1
  and -1<=r<=1. The L1 normalization bound also holds at zeros.
- Dominant Fourier frequencies can be chosen symmetrically. Unit-character
  orthogonality, the exact derivative cocycle, and the triangle inequality
  give separate-addition error at most 18 epsilon.
- Rowwise BLR correction is valid with its strict local threshold; rows
  outside that threshold are charged their full mass. Symmetry then gives
  a bilinear correction without an additional small-global-error premise.
- The endpoint constants 332, 173/256, and 191/256, and its overlap with
  the printed length comparison, have been checked exactly.

The completed quantitative section was checked after its final constant
sharpening. The use of a fixed rho0 below the actual normalized arrangement
proportion makes the purification threshold uniform in the actual set
density. The direction of the fifteenth-root and ceiling inequalities is
correct for a=alpha/2<1. The all-parameter extraction and endpoint cases
cover the full interval 0<alpha<1, and alpha=1 is vacuous for the strict
nonuniformity premise. The stated N0 distinguishes the explicit purification
threshold from the still inherited common-square threshold.

The script `quantitative_exact_checks.py` recomputes all exponent arithmetic,
checks twelve exact finite Fejer choices, checks the BLR majority correction
on 1,249 maps including 36 maps of nonzero defect satisfying its hypothesis,
and checks the symmetric coefficient calculation on 636 coefficient maps.
Its recorded output is `quantitative_exact_checks.json`. No floating-point
arithmetic is used.

## Further endpoint results in the final article

The final endpoint section was audited after addition of the several-variable,
general-group, and cubic-integration results. No mathematical error was found.

- The symmetric-table argument correctly confines all errors to tuples with
  nonzero coordinates. Dividing by their product is legitimate on that set.
  Coordinate replacement compares two tuples sharing the corresponding
  coordinate-independent predictor, so each replacement costs at most twice
  its error without assuming independence of those prediction errors.
  The resulting bound is 12s times the additive-test error.
- In the general-group induction, the corrected rows take values in the
  finite abelian group Hom(A1,H). A nonzero homomorphism has kernel of index
  at least two. This justifies the factor two from evaluated tests to
  homomorphism-valued tests, and hence the factor 38 and the threshold
  38^(s-1)*tau<1/6. The closed formula for C_s agrees with its recurrence.
- The first cubic descent averages squared Fourier moduli; discarding the
  frequency-correction set costs at most its measure, while the remaining
  mean deficit costs D. This gives 163D. No pointwise threshold is silently
  substituted into this average.
- The cubic and quadratic demodulations have the displayed signs and
  coefficients. The identities Q3(u)=E_h,k |E_x D_h D_k u|^2 and
  Q2(v)=E_h |E_x D_h v|^2 justify the two degree descents exactly.
- The cubic correction constants 163, 326, 6194, 17604, and 12390 and
  the positivity of the square-root argument under the stated threshold
  were verified independently. The final unit scalar cannot generally
  be absorbed into a polynomial with coefficients in the prime field.
- The error-order example has only finitely many polynomial phase classes
  modulo scalar. At the constant function there is a strict positive
  distance to every nonconstant class, so continuity preserves the
  constant phase as the best class for sufficiently small perturbations.
  Distinct four-cube vertex forms have a two-by-two minor equal to +1
  or -1. They are therefore pairwise independent under the uniform cube
  distribution, including cubes where some realized vertices coincide.
  This gives the variance coefficient sixteen and the claimed limiting
  distance-to-deficit ratio 1/8.

The exact verifier additionally checks both demodulating identities at
the polynomial-coefficient level, all 120 rank certificates for pairs
of four-cube vertex forms, the cubic constants, and the general-group
recurrence through order twelve. These remain finite algebra checks;
the all-order and asymptotic assertions rest on the written proofs.

### Final all-degree integration and scope audit

The final all-degree polynomial-phase corollary and generalized
error-order proposition were reviewed after their addition to the article.
No mathematical correction was needed.

- For a unimodular input with Q_(r+2) deficit at most D, the dominant
  selector has additive-test error at most 9D. The symmetric-table
  correction therefore costs at most 108rD. Keeping the average squared
  Fourier modulus, rather than imposing a pointwise threshold, adds only
  the original mean deficit D. The one-step descent factor is 108r+1.
- The r-fold difference of X^(r+1)/(r+1)! has coefficient equal to the
  product of the directions in front of X. Its remaining terms are
  independent of X. Demodulating by this polynomial consequently turns
  the selected Fourier coefficient into a zero-frequency coefficient
  without changing its modulus. The Gowers recursion gives the claimed
  decrease from order r+2 to order r+1.
- The condition p>=k implies that every integrated degree is at most
  k-1<p, so every required factorial is invertible. The accumulated
  defect is exactly K_k*epsilon, where
  K_k=2*product_(r=1)^(k-2)(108r+1). The initial factor two is solely
  phase normalization. No further small-error condition enters the
  symmetric correction. The stated epsilon<=1/K_k makes the final
  square root real and includes the empty-descent case k=2.
- The bound K_k<=2*109^(k-2)*(k-2)! follows term by term. Scalar
  alignment gives the stated squared L2 estimate even when the displayed
  lower bound on correlation is negative. In particular, there is no
  hidden assumption that this lower bound is positive.
- The error-order argument remains valid for every k>=2: any two distinct
  cube vertex forms have a minor of absolute value one, including in
  characteristic two. Their cross-covariances vanish. The cube variance
  is 2^k*sigma^2, and the ratio of optimal squared distance to the
  uniformity deficit tends to 2^(1-k). Finiteness of the polynomial
  phase classes on a fixed field justifies the local choice of the
  constant phase class. No uniformity in the field size is needed for
  this obstruction.

The verifier was extended to compare direct products with recursive K_k
values through k=12, check the factorial upper bound, expand all r-fold
demodulating polynomial identities through r=5 over the integers, and
check cube pair-rank certificates for k=2 through k=6. These supplement
the written all-degree arguments and are not proofs by finite search.

The final introduction and research/integration sections were also checked
for scope. They explicitly distinguish the written proof from a new Lean
verification, retain the sufficiently-large-prime quantifier and imported
square-extraction threshold, and make no claim of a new complete
Szemeredi bound or established publication priority. The stated proposed
questions remain questions rather than conclusions of the local bounds.

## Bounded Schur-defect classification

The general partition theorem and its preliminary terminal-structure theorem
were checked independently. In particular:

- Two consecutive perfect rows imply a complete initial progression. The
  reflected translate of the earlier prefix has exactly the size needed to
  be the next prefix with its minimum removed; comparing the increasing
  lists gives the common step.
- The suffix starting with the first defective row has at most twice the
  defect budget in length. This includes the case when its final row is
  perfect.
- The lower bound L>=s+1 is needed: it gives a positive representation in
  every later row, which forces integrality by induction. It also rules out
  the truncated branch in the gap estimate e_j>=min(g_j-1,L).
- At the boundary n=5s-1, the earliest possible hole is at least 3s while
  the largest set element is at most 6s-1. Thus the strict exclusion of
  sums of two holes remains valid at equality in the theorem's threshold.
- Every failed reflection entry corresponds bijectively to a preceding
  hole. This gives the exact identity e_j=a_j-j, rather than merely an
  inequality.
- Conversely, a nondecreasing integral displacement vector of total s has
  at most s positive entries. Its holes satisfy the needed no-two-hole
  inequality, proving sufficiency. Normalization by the smallest point
  makes the partition and positive dilation unique.

No gap was found in the general theorem. Its threshold is a sufficient
threshold; it is not asserted to be optimal except at the separately
classified deficits one and two.

## Schur defect two and the third energy level

The complete case split according to the first defective row was checked.
The following delicate points were verified explicitly:

- For k>=4, the representation count 2k-1-q forces q=k+2 at a row of
  defect two, and q=k+1 at a first row of defect one. The positive
  representation condition excludes all nonintegral or overly large q.
- In the second row of the defect-one case, the isolated value q=2k+2
  contributes only one representation; it cannot produce the required
  k-1 representations. The argument includes k=4.
- At k=3, only the branch {1,2,4,5} can continue to a fifth point, and it
  continues uniquely as {1,2,4,5,6}. Its next row cannot be perfect.
- At k=2, all possible double-summand and mixed-summand coincidences were
  checked. None produces a fifth point at total defect two. In particular,
  the special ratio b=3a/2 leads only to {2,3,4,6}.
- The endpoint difference multiplicities for H_n and L_n are correct.
  At H_n's endpoint n+2 the extra failed difference-three class has size
  n-3, which is positive in every case where it is invoked.
- In the third-prefix branch, Schur model I reflects to an (n-1)-point
  progression with endpoint n+1. Its exact energy defect is 2n-5,
  contradicting the necessary 2n-6. Model II gives J_m.
- The exceptional five-point Schur set gives exactly the additional
  six-point energy class [0,6] minus {3}. Its gap sequence differs from
  those of both eventual classes, even after reversal and scaling.
- The one-hole energy formula follows from counting missing completions;
  precisely min(j,m-j) candidate pairs have their middle entry at the
  deleted point and must be removed.
- Transfer to a torsion-free abelian group is justified by an additive
  injection of the finitely generated subgroup into R. Every classified
  model has a pair at unit distance, so the real step is the image of an
  actual group difference, and all relations pull back.

The final structural LaTeX section was also checked against the proof notes.
A harmless typesetting typo, a literal `quad` in the two-model display,
was reported to its author for correction. No mathematical correction was
required by this independent review.
