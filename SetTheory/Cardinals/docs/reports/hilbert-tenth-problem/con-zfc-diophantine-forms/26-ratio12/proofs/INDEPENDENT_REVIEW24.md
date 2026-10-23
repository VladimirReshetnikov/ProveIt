# Independent review of the twenty-four-integer synthesis

Reviewed `/research/root24/PROOF24.md` against package 21's norm proof and
the full text of package 23's `ODD_SCALE_27_PROOF.md` at the pinned snapshot.
This is an ordinary mathematical review, not a proof-assistant check.

## Findings

1. The signed extension of the unchanged norm weight is valid. If
   U=|H|Bnd>2, then |L|>=U-1. The two estimates sqrt(G)>2 and
   |H|sqrt(A)-sqrt(G)>2 imply both required automorphism dominance bounds,
   regardless of the sign of L or H. When w=0, A=1 already makes the
   first root rational, so its dominance argument is unnecessary.
2. The conjugate bound remains valid for signed v and imaginary y:
   use |v|sqrt(D)+b. Because b>1, the interval from -1 to QM^2-1 yields
   the stated absolute-value bound. No total-realness hypothesis is hidden.
3. The auxiliary offset obeys 1<b<Q before any roots are reconstructed.
   The proof only uses Delta>R>0, D>Delta+|c|, and i!=0. In particular
   Q-b=(Delta-R)D-Delta-c>0 is valid when c is negative.
4. The T=0 case is handled in the right order. Saturation applies directly
   to rational y with integral V=b, before f has been recovered. Moreover
   (b^2-1)/(Q-1)<b+1<2b+1 for 1<b<Q, so y^2 lies strictly between
   consecutive squares b^2 and (b+1)^2. Hence T=0 is impossible.
5. The w=0 case does not require f to have been recovered. Once u and
   gamma are integral, u=ac+Hgamma and Delta=a^2+H make the main norm
   divisible by H, contradicting |H|>1. The order of the two degeneracy
   exclusions is therefore sound.
6. Package 23 explicitly permits signed h,T,gamma and roots, odd i of
   either sign, odd s, and square w. Its Sections 2-4 use precisely the
   four reconstructed normalized norms and equal outer unit signs. They
   do not impose the stronger H*i scale of package 23's separate
   twelve-variable root merger. The proposed application is valid.
7. The odd-s completeness claim is a genuine inherited theorem, not an
   arbitrary witness restriction. Package 23 proves popcount(R)=3t+2
   and v2(Y)=3t when q=2^t, so s=Y/q^3 is odd. It composes with the
   existing odd-i and square-w canonical choices.
8. Six Pos maps, two odd affine maps, and one square map use 24 integer
   coordinates and 47 binary gates. The source twelve-variable norm
   has 116 gates, yielding 163. The highest-degree certificate agrees:
   its selected product monomial has coefficient 2^353 beta^853 and
   total degree2432. The norm monomial coefficient is
   2^352 beta^848 at degree2416.

## Dependency boundary

The review validates the new domain composition relative to the explicit
inherited signed-Pell, mask, finite-window, and K215 calibration theorems.
It does not independently formalize those theorem chains or check the
astronomical fixed coefficient payload. One entire authentic tuple must
be used, including the shifted-MF convention and the padding/parity
properties needed by package23's completeness proof.

No remaining mathematical defect was found in the reviewed new reduction.
