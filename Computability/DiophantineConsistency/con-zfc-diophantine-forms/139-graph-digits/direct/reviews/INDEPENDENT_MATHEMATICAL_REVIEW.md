# Independent review of pooled digits and the semantic fused cap

Reviewer: a separately tasked research agent in the same AI-assisted workflow.
This is not an external human endorsement. Review performed against the files
in `direct_work/PROOF.md`, the literal builder, the pinned package-129 report
and normalized source, and the selected `four64` and `four32` raw equations.

## Disposition

The new ordinary arithmetic arguments in Sections 2--6 pass this review.
No circular use of the factorial, binomial, or exponentiation semantics was
found. The full inherited C222/ZF/ZFC calibration was not independently
reproved or rebuilt. The conclusions remain relative to the precisely retained
ordinary calibration and unmodified arithmetic source theorem.

## What was checked

1. **Pooling.** A pooled row with nonnegative slacks implies every old
   individual remainder bound, with explicit polynomial slack restoration.
   The converse is not asserted for arbitrary old witnesses. The proof
   correctly supplies a stronger summed-coefficient budget on fresh witnesses.

2. **The three low-digit bounds.** With R=2+t+x+y+F and K=2R,
   N=B^(2R)>=4^R and q/N^2=N^(2R-2). For ordinary representatives,
   j<=R-2 and n<=10N^2 imply
   n^j<q/N^2 because 10^(R-2)<N^2. The factorial index F^2+t is bounded by
   R^2+R<=4^R, and 2R^2<=4R^2-4R for R>=2. For J, the inherited literal-DAG
   bound J<=N^(3*2^22), together with 3*2^22*(t+1)<=2t!, gives the required
   low-digit bound. The invocation F=t! is explicitly in completeness only.
   Since every pool has at most five members and N^2>=6, their digit sums
   are at most q-1, including j=0. The integer quotient q/N^2 makes the
   strict slack calculation valid.

3. **Raw growth before semantics.** The retained report's frame is
   W=16+sum(atoms), Z=z+1, L^2-((W+1)^2-1)(WZ)^2=1, A=L+sigma.
   Pell classification and Y_e(W+1)=e mod W force e>=W and hence
   A>W^3+1 without interpreting any proposed power or binomial. The
   common-root-compatible choice of A remains cofinal because L and A
   are separate coordinates.

4. **Fused-cap soundness.** The new row yields |Y_i-k_i|<=sqrt(V).
   H>=2 implies V=Y_H>=2A>2W and V>4. Thus Y_i<V and each decoded index
   j_i<H<W. Reduction modulo A-1 turns the error sum into a nonnegative
   integer smaller than A-1, so every index error vanishes. The condition
   H<=V needed by the full indexed anchor follows directly from the new row.

5. **Fused-cap completeness.** When H>=2m+1, doubling and Pell growth give
   V>2(2A-1)(A-1)Y_m^2>(r+H)Y_m^2. Thus the numerator of the new quotient
   is positive and divisible by A-1. The already retained CRT lift makes
   a>N^2, H>=2a^2>2N^4, while every seed index is at most 2N^2. Hence the
   doubled-gap premise is supplied without adding a nominal-index condition
   to the polynomial. It is correctly used only in completeness.

6. **Restoring the old cap.** After index recovery, each Y_i-k_i is divisible
   by A-1, giving the old error quotient. Since k_i<H, the old aggregate
   slack is nonnegative by Y_H-rY_(H-1)>H. Therefore the source theorem
   is applied only after all changed rows have been restored.

7. **Literal scope.** The semantic H polynomial in the builder agrees with
   the pinned full anchor's R_mod_4Y and initial aggregate-cap rows. The
   selected four-pool variants retain the exact factorial B<q digit bound.
   An independent script reconstructs every changed raw row without importing
   the producer or its certificate, and checks every other row unchanged.
   It also rejects three perturbed row constants. This is not a finite test
   of the unbounded lemmas, but guards the intended formulas' literal binding.

## Remaining boundaries

The nonnegative contractions and quartic expansion are covered by the
producer's separately implemented checker; this review inspected their
interface rather than duplicating their entire implementation. The inherited
logical interfaces and original power/binomial compiler are mathematical
dependencies. None of the computations proves consistency or the absence
of integer zeros.
