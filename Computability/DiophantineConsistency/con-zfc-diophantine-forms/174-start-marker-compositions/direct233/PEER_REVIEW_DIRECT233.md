# Independent final review: the direct 233-variable construction

**Decision: PASS, within the explicitly inherited ordinary-calibration
boundary.** The new semantic composition and every new exact algebraic map
have been reviewed. The numerical profiles below were independently
recomputed from the supplied coefficient arrays. This is an AI-assisted
review by a separate reviewer, not outside human peer review or a new
end-to-end formal-kernel certificate.

The reviewed final text is COMBINED_PROOF.md, identical at review time to
deliverable/PROOF.md. PEER_REVIEW_DIRECT233.json binds the exact reviewed
proof and equation bytes. The upstream snapshot is ProveIt
fb1bed5eb7196cf35abfaa746c18c6ee7eae6cfb.

## 1. Scope and disposition

The new proof establishes the existence equivalence between the edited
arithmetic source and a finite refutation, using the named retained
Pell/power, local-row, Horn and C222/ZF/ZFC calibrations. It does not purport
to reprove or replay all those deeper dependencies. Its last section
explicitly identifies that boundary and the absence of some historical
dependency files from the inspected tree. This qualification is material
and must remain in the delivered article.

No mathematical gap was found in the new composition. One typographic
error in the selector proof was reported and corrected before final
acceptance: with a=v_p(Lambda_t), the disappearing levels are those above a,
because p^(a+1)>t. The earlier wording incorrectly attached >t to p^a.
The corrected proof and bound are valid, including a=0 for primes p>t.

## 2. Literal source interface

I inspected the actual power239 residuals and names, rather than inferring
semantics from historical coordinate names.

- Row0 is x4-x3^2, so F=x3 and R=x4.
- Row155 is x0-16-2x212^2, so the actual horizon is x0.
- Rows1--3 identify the beta code x=x1 and spacing y=x2-1: their
  endpoint bracket is 1+(t+1)y, and the first endpoint is
  x=F+1+(y+1)u0.
- Rows170 and174 give y=F(2x238+1)^2.
- Row4 is 1+R-B*mu+x17, as required for the index bootstrap.
- Row154 gives BH=B(1+sum(x9,...,x17)). Under the retained
  first-representative shift, actual a=x9-1 and the other eight actual
  representatives are unshifted. Thus H=2+sum(actual representatives).
- Row173 gives stored_q=x101=(2x236+1)^2+1. The correct affine replacement
  is stored_q=4x236+2. Replacing it by 4x236+1 would be wrong.

The proof therefore uses the actual power branch offset and both required
source shifts. It does not import the shared-factorial branch's different
H offset.

I also replayed the upstream 245-to239 transformations on both the original
sphere-adjusted source and the source with the two semantic edits already
made. All 76 shears, 47 row additions and 6 monic projections pass their
integer inverse/coefficient identities in both cases. The edited result
equals the supplied edited_source239 residual system exactly. Thus the
semantic changes genuinely commute with the retained finite chart; this
was not assumed from the survival of two variable names.

## 3. Lcm bound and both selector directions

The lcm induction is sound. For k=ceil(n/2), a maximal prime power p^a<=n
not contained in Lambda_k has p^(a-1)<=k<p^a. Legendre's formula for
binom(n,k) contributes one at that highest level, supplying the only extra
factor p needed beyond Lambda_k. Hence
Lambda_n divides Lambda_k*binom(n,k).
The even and odd middle-coefficient estimates then give Lambda_n<=4^n.

Because t>=16, F=t^t>=16^t>=Lambda_t^2. No divisibility t!|F is used.

For each i, R+i>Lambda_t^2 ensures some prime valuation v>2a with
a=v_p(Lambda_t). All other R+j have valuation v_p(j-i), yielding

    v_p(B)=v-d,
    d=v_p(t!)-v_p((i-1)!)-v_p((t-i)!)
     =v_p(t*binom(t-1,i-1)).

Each floor summand defining d is zero or one because the two denominator
arguments sum to t-1. The levels above a vanish, so d<=a. Thus
e=v-d>a and p^e>t, while p^e divides R+i.

The converse was checked separately: Legendre's expression for v_p(B)
has zero-one summands, with no nonzero level above
max_i v_p(R+i). Consequently every exact prime power dividing B has
a compatible row. This is the necessary all-primes completeness condition,
not merely the per-row soundness selector.

## 4. Soundness order

The signed bootstrap is acyclic:

1. The authenticated positive t power gives F=t^t and hence y>=F>0.
2. q=4z+1 excludes q=0,-1 without assuming q positive.
3. If q=1, the q+1 power requests force nonnegative representatives,
   H>=2 and C0>=0. The index row gives B!=0. Then the nonunit
   self-radix request forces x=0, contradicting the last beta endpoint.
4. For all remaining q, |q|>=3 and |q+1|>=2, so the same requests
   recover the representatives. The self-radix and two endpoints give
   x>=2+(t+1)F, with no negative-base or negative-index gap.
5. M and every denominator power are now nonzero. Dividing by a
   normalization ratio is licensed because it is a nonzero integer and
   divides the normalized remainder.

The spherical budget gives |r_i|<=|L_i|/sqrt(2)<3|L_i|/4.
Together with a canonical tail below |L_i|/32, this gives a strictly
sub-modulus difference and exact tail recovery. No positive-denominator
assumption was silently introduced.

For the binomial numerator the bound
C_j<=V=(F^2+1)^t and x>=2+(t+1)F gives
V/Q<=2^(-F-t-2). Thus its low tail is small for either sign of q.
The recovered congruence B=binom(F+t,t) modulo q becomes an equality
using |B|<=Q/4 and the true coefficient below Q/32. Only then are B
and q proved positive. The following local precision margins remain
strict under F>=2^64, so the retained local-row handoff is justified.

## 5. Exact label multiplicities at the smaller evaluation point

The proof correctly avoids the false inequality (t+1)^t<F.

After removing unit factors, unequal factor counts are impossible:
the larger product exceeds the smaller by the comparison
F+1>t^d for d<=t. Both polynomial products therefore have degree d<=t.

At each degree k their coefficients are positive integers between 1 and

    binom(d,k)t^k <= t^d <= F.

For the middle inequality, use
binom(d,k)=binom(d,d-k)<=d^(d-k)<=t^(d-k).
Because both coefficient lists are positive at every degree, the difference
of corresponding coefficients has magnitude at most F-1, even if an
individual coefficient equals F. Reducing at the lowest nonzero coefficient
modulo F proves equality of the two polynomials. This establishes exact
multiplicities; the inherited Horn closure then applies.

The y=F boundary is excluded before using the intended nonzero accumulator:
zero initial value would propagate through positive-weight updates to the
required final value one.

## 6. Completeness

The cofinal even horizons remain unbounded. For F=t^t at an even horizon,

    v2(F)=t*v2(t)>=t>v2(t!).

Thus y can be an arbitrarily large even multiple of t! of the required
form F times an odd square. The beta CRT moduli are odd and pairwise
coprime, and an arbitrarily large even code x can be chosen.

For 1<=i<=t, v2(F+i)=v2(i), so B=binom(F+t,t) is odd.
The all-primes CRT construction from Section2 therefore retains independent
representative parity choices modulo the odd N^2. Taking the actual first
representative odd and the others even gives odd H while preserving the
old opposite-parity and even-anchor conditions. Since x is even,
q=(BH)^x is an odd square and hence is 1 modulo4, providing the required
new affine-radix coordinate.

The canonical remainders satisfy 0<=R_i<M/32. With eleven remainders,
2*sum(R_i^2)<22M^2/1024<M^2, so the residual nonnegative integer has the
required ternary representation. The retained Pell/frame completion
can then be used. This is an existence construction; the proof does not
misdescribe the semantic edit as a pointwise bijection.

## 7. Exact maps and independently recomputed endpoints

In addition to the upstream commutation check described above, I verified:

- Every residual of edited239 after substituting x4=x3 and
  x101=4x236+2, including the exact vanishing of the two deleted rows.
- All three common-Hessian-radical projections, with unit pivot slopes,
  integral restoration polynomials and their complete coefficient identities.
- The affine projection of coordinate95 in the 234-coordinate system;
  its deleted row has coefficient +1 and supplies the exact affine inverse.
- Every elementary integer row operation in each final basis, with its
  inverse subtraction.
- Every expanded coefficient of each final sum of squares, total degree,
  variable liveness and coefficient height.

The independently recomputed results are:

| Endpoint | Variables | Rows | Degree | Terms | Height | Row additions |
|---|---:|---:|---:|---:|---:|---:|
| P233_balanced | 233 | 169 | 4 | 18482 | 5632 | 365 |
| P233_sparse | 233 | 169 | 4 | 10182 | 8880 | 49 |
| P234_sparse | 234 | 170 | 4 | 5018 | 8880 | 47 |

The coefficient review used exact integer arithmetic and the separately
supplied independent projection auditor, after reading its implementation.
No search for roots was performed or used. This confirms the new finite
artifacts; it does not establish consistency or replace the inherited
unbounded arithmetic and refutation theorems.

## Final disposition

The stated ordinary theorem follows by composing the reviewed semantic
existence reduction, the verified integer-zero-set bijections and the
explicitly retained source calibration. The declared scope is appropriate.
The construction supplies an actual new 233-coordinate quartic at this
snapshot, with two useful term/height tradeoffs. No worldwide novelty or
global simplest-equation conclusion follows from this review.

