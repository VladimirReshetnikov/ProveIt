# Independent review of the signed residue-pool reduction

Reviewer: a separate mathematical review agent in this AI-assisted session.
Date: 25 October 2026. This is not external human refereeing.

## Conclusion

The new ordinary proof in `analysis/certificates/new_signed_pool/PROOF.md`
is sound, subject to its explicitly retained C222/refutation and shared
Pell-source interfaces. I found no remaining gap in the new arithmetic
transformation. The merged endpoint has 260 unrestricted integer variables,
186 quadratic residuals, 5,325 collected quartic terms, and height 128,446.
The separate-denominator companion has 261 variables, 185 residuals,
5,332 terms, and the same height.

This assessment does not certify the entire inherited proof-calculus
calibration from first principles or claim a newly compiled Lean/Rocq proof.
It certifies the new reduction's proof order, the exact changed source
constraints, and its finite projection/translation/expansion artifacts.

## Mathematical points checked

1. The certificate n=a^2+b^2+c(c+1) is nonnegative for every integer triple
   and represents every nonnegative integer. Applying the three-square
   theorem to 4n+1 and reducing modulo four gives its converse.

2. The shared cap L^2-2 sum(r_i^2)-1=n implies |r_i|<L/sqrt(2)<3L/4.
   With a known canonical residue 0<=c_i<L/8, a multiple r_i-c_i of L
   has absolute value below 7L/8 and is zero. This is valid for negative
   provisional remainders as well as positive ones. Conversely at most
   seven such canonical residues leave a nonnegative integer slack.

3. Removing the eleven delayed intervals preserves the three *initial*
   scalar nonnegativity graphs for the factorial remainder, its slack,
   and the exact-binomial output slack. It also preserves every frame,
   cap, coordinate-orientation, genuine-power, endpoint, and raw radix
   row. The parent `ORIENTATION_FIRST_PROOF.md` and `STRICT_BUDGET_PROOF.md`
   explicitly establish all power meanings before the delayed intervals.

4. The early bootstrap is noncircular. From B=r+s+1, q=B+o+1 and
   FB=(F^2+1)^t+s it obtains F>=1, B>=2 and V=(F^2+1)^t<B^2. The
   endpoint equations and t>=16 give x>=2+(t+1)y>=6, independently of
   F=t!. After the actual representatives become nonnegative,
   q=(B H0)^x>=B^6>=16B^2>16V, using only H0>=1.

5. The factorial low-digit margin must be proved before using F=t!.
   Here is an explicit proof independent of the inherited coefficient
   lemma. Put m=F^2. If m>=t, the binomial coefficients through position
   t are increasing, and binom(m+t,t)=product_i(1+m/i)<=(m+1)^t.
   If 4<=m<t, every coefficient is at most 2^(m+t)<4^t<=(m+1)^t.
   If m=1, every coefficient of (1+z)^(t+1) is at most 2^t, since the
   sum of coefficients of either fixed parity is 2^t. These are all
   cases because m is a positive square. Consequently each relevant
   coefficient is <=V<q/16. The shared cap recovers the factorial
   remainder without first interpreting any of the other ten remainders.

6. The retained digit-output bound then identifies B=binom(F^2+t,t),
   so the inherited square-output fixed point gives F=t!. Only after
   this step is B=product_i(1+F^2/i) used. The raw congruence
   B|(C0+F^2+1), with C0>=0 and B>F^2+1, forces C0>=1 and H0>=2.

7. All eleven cases in the new proof's table match the actual numerator
   and denominator rows. For an ordinary upper representative a and
   j<k<=x, binom(a,j)<=max(1,a)^j<=H0^(x-1)<=q/64. For the derived
   label, h<=H0^ell and ell(t+1)<2F<x give the same bound through
   j=t. Zero upper representatives are included: their constant
   coefficient is one, and no invalid 0^0 estimate is needed.

8. Each canonical low residue is <L/8 by a geometric sum. The merged
   cap uses the positive exact relation q^(t+1)=q*q^t, so the two
   smaller-denominator remainders are weighted by q. Its bilinear
   term is exactly q^2*(r_choose^2+r_index^2), where q^2 is an already
   existing, retained wire and the sum of two squares is one new wire.
   Every squared contribution is nonnegative before any missing sign
   is inferred. This permits the factorial bootstrap inside a group
   whose other residues have not yet been decoded.

9. Soundness reconstructs each old slack as L-r-1 and then its old
   nonnegative product certificate. Completeness starts with an old
   zero, whose now-canonical residues satisfy the same stronger margin,
   and supplies three universal ternary witnesses per new cap. This
   proves existential equivalence; no false one-to-one claim about
   private witnesses is needed.

## Exact artifact checks

`check_signed_pool.py` is an independent checker written for this review.
It imports neither the producer nor the inherited polynomial/compiler
implementation. `SIGNED_POOL_INDEPENDENT_CHECK.json` is its actual receipt.

The checker independently identifies all eleven old intervals from their
literal coordinate names and polynomials. It confirms exactly 22 deleted
rows, all other parent rows byte-for-byte unchanged, and every new cap and
sum-square definition. The inherited Horn factorization certificate is
identical to the parent's, apart from renaming its freshly allocated root.

It then replays every monic integral elimination from the factored source:
205 steps for the 261-variable endpoint and 204 for the 260-variable endpoint.
It checks each pivot is exactly +1 or -1, each restoration has no self-
reference, every intermediate residual remains quadratic, all discarded
coordinates are genuinely unconstrained, and every output residual matches.
It separately applies the final integral translations, re-expands every
residual square, compares the full collected coefficient dictionary with
the distributed polynomial, and checks all variables occur.

Verified equation hashes:

- 260 variables: ee37d6583ec7789ffd8ea6b6f3b99c285c16349d54e1a0e209b9615c8e05bc69
- 261 variables: c813e22e92f9daa1784e25f0379f47a317ea3663d0e9f80026b718f9f0ffa165

The finite checks do not search for a ZFC refutation, prove consistency,
or replace the unbounded ordinary proofs. They bind the advertised finite
polynomials to the reviewed transformation.
