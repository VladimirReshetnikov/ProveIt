# Review of the modular numerator composition

Reviewer scope: separate mathematical review within the AI-assisted
workflow, 25 October 2026. This is not outside human refereeing.

Reviewed: `proofs/MODULAR_PROOF.md` and the literal edits
in `stages/modular/mutation.json`, against the fixed-base
source and the retained orientation-first, strict-budget and
PROOF_315 semantic-cap proofs.

## Conclusion

The semantic composition is sound subject to the explicitly inherited
Pell, binomial CRT, C222 and logical interfaces identified in the note.
No additional consistency assumption is used. The following potentially
delicate steps have been checked separately.

1. **Bootstrap with signed representatives.** The odd-B row gives B!=0.
   The unchanged exact q^(y+1) certificate, |q|>=3, and y=RBodd^2
   imply y>0 and B>0 before any modular binomial interpretation.
   H is positive by its square definition. The first endpoint then
   excludes x=1 after the self-radix excludes x=0. This avoids using
   nonnegative numerator indices, which the modular replacement no
   longer guarantees.

2. **A common modulus suffices.** N=B^x divides q=(BH)^x. Therefore
   every modulus N*q^k for k<=x, and the exceptional exact-digit
   modulus q^(t+1), divides Omega=N*q^x. Higher binomial terms
   vanish modulo the required N*q^k because N divides q. The common
   square root condition legitimately evaluates the signed Pell unit
   at q+1; q+1 is a unit modulo Omega even for negative indices.

3. **Signed binomial coefficients.** The bound
   |binom(-a,j)|=binom(a+j-1,j)<=a^j follows from the surjection of
   ordered tuples onto multisets. The negative-index truncation is
   a finite polynomial identity in the quotient where q is nilpotent.
   No analytic convergence is involved. The signed extension of the
   range lemma in Section 9 follows by applying its nonnegative form
   to a+k-1 and then taking the residue of -a.

4. **Centered remainder uniqueness.** The common norm bounds each
   normalized remainder by M/2. Its exact ratio divides both sides
   of the numerator equation, so the unnormalized remainder is an
   integer. The canonical signed low sum has absolute value below
   D/32. Congruence modulo D therefore forces equality. This is
   sufficient without a sign condition on any global representative.

5. **Growth bounds.** With H>=2+2(R+t)+sum(a_i^2), every ordinary
   representative satisfies max(1,|a_i|)^2<=H. The two special
   indices use x>=2t and x>=2*ell*(t+1), available from y>=R and
   R=16^t. The reported independent DAG certificate for |J| is
   necessary: a positive-input monotonicity bound alone would not
   justify signed inputs. The value stated in the certificate is
   below ell=2^22, as required.

6. **Arbitrary sufficiently large positive centers.** The newer
   squared-cap construction uses the former exact frame center only
   through its magnitude and canonical Pell identities. Its
   completeness construction first fixes the even semantic anchor
   h, then uses canonical X_h(A),Y_h(A), with a large positive A.
   The gap estimate remains valid when A is enlarged. The auxiliary
   index h*Y_h(A) and odd-quotient argument work for every integer
   positive A: h even gives an even ordinate and odd abscissa, and
   the cited divisibility identity then gives the odd auxiliary
   quotient. The comparison-center CRT or its deterministic
   polynomial substitute retains the necessary congruences.
   Consequently freeing A above L^2 is compatible with these caps.

7. **New squared-H congruences in completeness.** Fix a odd and the
   other schema variables b,c,d even, making the semantic anchor
   even. Keep all five other representatives even. If 3 does not
   divide B, two representatives outside a,b,c,d may be adjusted
   modulo six by multiples of the odd, 3-coprime modulus N^2.
   Their squares modulo three independently attain 0 or 1; their
   sum attains every residue. This arranges H=0 modulo three while
   H remains odd. The changes do not alter J or the CRT conditions.
   Enlarging a by a multiple of 6N^2 preserves these congruences and
   supplies the needed dominant positive anchor. If 3 divides B,
   only oddness is needed. Thus q=6z+3 is constructively complete.

## Attribution and limitations

The modular-numerator/common-root/free-center method already occurs in
the retained INHERITED_MODULAR_FACTORIAL_PROOF, attributed there to the
Pell-residue predecessor. The present contribution is its composition
with the fixed-base radius, binomial Horn weights, signed semantic cap,
and shared centered norm, with the changed signed-input proofs supplied.

This review does not independently recompile the original logical
formalization, prove Con(ZFC), or authenticate every final coefficient.
It reviews the ordinary unbounded argument; exact literal audits are
separate. A proposed two-square center constructor is justified in the
separate TWO_SQUARE_CENTER note, and requires its own completeness
choice of the Pell frame index. The argument that every large A is
available must not be retained verbatim after that refinement.
