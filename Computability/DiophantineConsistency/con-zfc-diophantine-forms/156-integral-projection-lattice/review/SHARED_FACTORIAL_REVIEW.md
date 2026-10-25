# Scoped independent review of the Shared Factorial Error source

## Reviewed version and conclusion

The reviewed source is the final signed affine-radix construction in `conzfc_shared_factorial_error_20261025/report/report.tex`, Sections 2--8, together with `verification/INDEPENDENT_MATHEMATICAL_REVIEW.md` and the final Section 6 of `verification/SIGNED_POWER_AND_BETA_REVIEW.md`. I independently checked the new arithmetic reasoning rather than treating the earlier review's verdict as a proof.

**Conclusion:** I found no unresolved gap in the normalized factorial-error bound, exclusion of the two unit radices, recovery at a negative provisional radix, nearest-factorial fixed point, or canonical completeness, under the explicitly retained signed Pell and CRT/calculus interfaces. The final recovery order avoids assuming a sign or factorial meaning before it is proved.

The file `equations/PROOF.md` describes an earlier 250-variable odd-square stage. It is historical support, not the complete proof of the final affine-radix source. The final integrated report is the appropriate authoritative proof for the present composition.

## 1. Sign-free normalized error

The common norm and integer nonnegativity of G(a,b,c)=a^2+b^2+c(c+1) give

    M != 0,       2|S| < |M|.

From Bv=M and MF=vV+S, both B and v are nonzero and

    S=v(BF-V),        |BF-V| < |B|/2.

This cancellation is valid with every sign of B,v,M,F. It is not division by a possibly zero variable, and it introduces no nonintegral error: BF-V is already an integer.

The signed power interface at the known index t>=16 gives V=(F^2+1)^t. At F=0 its base is one, so the unit-base case must be used. It yields V=1.

Write b=|B|. If F=0 then 1<b/2 and b>=3. If F!=0, the error bound forces B and F to have the same sign. With f=|F|>=1, b<=f would imply

    V < b(f+1/2) <= f^2+f/2,

contrary to V>=(f^2+1)^2. Therefore b>=f+1>=2 and V<b(f+1/2)<b^2. These deductions are independent of every binomial interpretation and every beta spacing estimate.

## 2. Signed power semantics and the q=+/-1 cases

The retained canonical signed-index Pell pair gives a power congruence modulo T=2An-n^2-1. For |n|>=2, the frame makes |T| greater than both absolute error bounds required for nonnegative and negative requested indices. For a negative index -j, the congruence gives m*n^j=1 as an exact integer equality, impossible for |n|>=2. Thus the exponent is nonnegative and m=n^k, even when n is negative.

For n=epsilon in {1,-1}, the requested output is epsilon^k at every signed index k. One cannot deduce nonnegativity of k at a unit base, nor silently omit negative indices. The proof correctly uses the two-sided recurrence f_(k+1)=2A f_k-f_(k-1) and 2A=2epsilon modulo T to establish this separate case.

The final radix equation is q=2z+1, so q is odd and nonzero. If q=+1 or q=-1, its M-output request gives |M|=1. That contradicts Bv=M with b>=2. Hence |q|>=3 and |q+1|>=2.

Requests at q+1 now force the actual CRT representatives to be nonnegative, even if q+1 is negative. Therefore H=1+sum representatives>=1. Requests at q give x>=0 and M=q^x. The retained q^(t+1) normalization ratio forces x>=t+1 by absolute values. Only now use the BH request to conclude

    q=(BH)^x,        Q:=|q| >= b^(t+1).

No positivity of q or B, no y>0, and no F=t! has been used to reach this estimate. The full orientation pool is essential: the x pair cannot safely be oriented only from an initially positive output at a provisionally signed base.

## 3. Recovering the factorial binomial at a signed radix

For F!=0, the coefficient estimate

    binom(F^2+t,j) <= (F^2+1)^t = V < b^2,  0<=j<=t,

is valid because F^2>=1. Its elementary Pascal induction is correct. At F=0 the same bound by V=1 is false; the report explicitly uses binom(t,j)<=2^t instead.

For either sign of q, the true low polynomial

    r_true=sum_(j=0)^(t-1) binom(F^2+t,j)*q^j

is congruent to (q+1)^(F^2+t) modulo q^t. The absolute geometric bound, Q>=b^(t+1), b>=2, and t>=16 give |r_true|<Q^t/32 when F!=0. At F=0 the separate b>=3 bound gives the same margin.

The normalized remainder equations reconstruct an integer r with |r|<Q^t/2. Its difference from r_true is divisible by q^t and has absolute value less than |q^t|. Hence r=r_true, without calling either remainder nonnegative. The exact digit equation then gives B congruent to binom(F^2+t,t) modulo q. The difference has absolute value less than Q, so the congruence is equality.

Thus B is positive. The case F=0 would force B=1, contrary to b>=3. The earlier same-sign conclusion gives F>0. Only then does q=(BH)^x force q>0. The order is acyclic and specifically closes the negative-q possibility.

## 4. Independent nearest-factorial argument

Let T=t!, t>=16, F>=1, and

    R=(F^2+1)^t/binom(F^2+t,t)
      =T*product_(i=2)^t [1-(i-1)/(F^2+i)].

Each factor increases with F. Therefore

    R >= 2^t/(t+1) > t^2+1/2.

The last inequality holds at t=16 and persists inductively. If |F-R|<1/2, it follows that F>t^2. The elementary product lower bound gives

    R > T[1-t(t-1)/(2F^2)] > 3T/4.

As T>=16!, this yields F>R-1/2>T/2. Reusing the same product estimate now gives

    0 < T-R < 2t(t-1)/T < 1/32.

The last upper bound holds at 16 and decreases thereafter, with consecutive ratio 1/(t-1). Hence |F-T|<1/2+1/32<1. Integrality forces F=T. Conversely F=T gives directly

    0 < T-R < t(t-1)/(2T) < 1/32,

which proves the required nearest-integer condition. This checks both directions and supplies the stronger completeness margin. It does not merely reuse a ceiling lemma whose hypotheses would be insufficient for a signed error.

After F=t!, BF-V is positive and less than B/32. The deleted factorial remainder and complementary slack can therefore be restored as BF-V and B-(BF-V)-1; both are nonnegative integers. Also q>B restores the deleted radix gap.

## 5. Remaining arithmetic and constructive completeness

The beta formula y=V(V-1) is unchanged. Once F=t! and V is positive, all of its original divisibility and size properties apply. The endpoint equations give x>=F+1 and x>=2+(t+1)y, providing the inherited amplification and range bounds. The remaining ten binomial digits are then decoded with the parent's positive-radix argument. This later use is legitimate because the preceding steps have restored its sign and factorial premises.

For completeness start from a finite refutation and use the parent's canonical padded horizon and CRT data. At F=t!, B and N^2 are odd. Changes by N^2 preserve all precision congruences while permitting the required parities: the dominant semantic anchor remains even, and H can be chosen odd. Consequently q=(BH)^x is odd, so z=(q-1)/2 exists without restricting x to be even.

B divides q and M, so v=M/B is integral. Taking S=v(BF-V) gives |S|/M<1/32. The eleven canonical normalized remainders satisfy the same margin. Thus

    4[S^2+sum R_i^2] < (48/1024)M^2 < M^2.

The remaining integer M^2-1-4[S^2+sum R_i^2] is nonnegative and admits the inherited G representation. The new norm and affine-radix rows therefore have canonical witnesses. No new cofinal beta construction is required.

## 6. Targeted literal source inspection

I inspected `equations/candidate244/source.json` in the exact source archive. The actual raw graph retains 560 coordinates and 383 quadratic residuals before the recorded projections. Relevant zero-based rows are:

- row 361: the cofinal horizon square; the actual horizon is 16 plus its nonnegative offset;
- row 359: the signed square frame, including the actual B, q, q+1, M, and BH quantities;
- row 373: the full paired orientation pool, including all fourteen abscissa squares and the x pair's `(1-X_x)^2` and `(Y_x-x)^2` terms;
- row 308: the literal M power-congruence row;
- rows 374--376: all three normalization ratios, including the crucial q^(t+1) divisor;
- row 378: all eleven normalized digit-error squares and the new normalized factorial-error square in the same norm;
- row 380: the affine odd-radix equation;
- rows 381--382: Bv=M and MF-vV-S=0.

This is a targeted interface inspection, not a second complete source-to-final projection audit. The latter remains covered by the source package's exact certificates and the new projection/Gram checkers.

## 7. Precisely retained dependencies

The reviewed new steps rely on the parent's signed Pell classification, deterministic comparison-center and cap theorem, full orientation/frame theorem, canonical power congruence interface, uniform CRT/range decoding, local C222/Horn-flow certificate theorem, and the two named logical calibrations:

    KEndpoint.c222_iff_zf_refutation
    ConstructibleChoice.zf_refutation_iff_zfc_refutation.

I inspected the unconditional statements of these logical interfaces in the retained Lean source. I did not rebuild their transitive kernel environment or independently reprove the entire inherited logical chain. The present conclusion is an ordinary unbounded mathematical review of the new signed bootstrap and nearest-factorial replacement, composed with those identified dependencies. No consistency assumption, numerical root search, or new end-to-end formalization is asserted.
