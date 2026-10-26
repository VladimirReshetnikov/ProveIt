# Independent review of the eleven-positive-variable dilation companion

Reviewed object: `research_compact/PROOF_constant_dilation.md`, together with the matched source-172 and source-140 ordinary proof interfaces. The candidate is `constant_dilation11.json`, advertised as eleven strictly positive variables, 104 live binary operations and exact total degree 174. This review concerns the unbounded mathematics and an independent leading-form check. Literal graph and coefficient-payload authentication belong to the candidate's separate finite checker.

## Verdict

No substantive gap was found in the new soundness or completeness argument inspected. The candidate may be included as a separate positive-domain companion, with its inherited native/compiler/refutation calibration boundary explicitly preserved. It is not an unrestricted-integer equation in eleven variables. Its metrics are a tradeoff against the retained ten-positive-variable constructions, not a universal optimum.

## Unit product and root recovery

The final equation `(P0+1)(3N+1)-1=0` correctly forces both factors to be integer units. Since the second is congruent to one modulo three, it cannot be minus one. Hence P0=N=0. There is no remaining negative-unit branch.

At P0=0 the rational-center equation is

    (Q-1) z^2 = G(QV^2-1).

Since Q is a multiple of G, neither Q-1 nor QV^2-1 has a prime factor in common with G. Prime valuations therefore make every prime exponent of G even, even though z initially is rational. The identity F0=1+Delta U^2 E gives gcd(E,F0)=1, so the two positive factors of G split as squares separately.

The adjacent-coefficient descent is valid. If `QV^2-(Q-1)y^2=1` with V integral and y rational, the squared denominator of y divides Q-1. The displayed norm-preserving transformation keeps its first coordinate integral and preserves the reduced denominator of its second coordinate. After sign normalization, for |V|>1 one has y>|V| and

    (Q-1)(y-|V|)=(V^2-1)/(y+|V|)<|V|/2,

which proves that the new integral first coordinate lies strictly between zero and |V|. Descent reaches |V|=|y|=1 and forces the original denominator to be one. This closes the rational-to-integral step without assuming it.

The recovered strong quantities satisfy `I=2Ug`, `f^2-Delta I^2=1`, `Q=(Delta I)^2`, and `c^2|I`. The signed folding and strong-rank theorems are used only under their retained hypotheses.

## The new small-index bound

The fixed dilation no longer gives A>q^2 automatically, so the p=3 branch genuinely requires a replacement argument. That argument checks out. If the main index p is at least five, `c>=psi_A(5)>4A^4>4q^4`. If p=3, the first index is m=2 because P>A and c>k force m<p, while m=1 is excluded by the strip.

Then

    k=8 lambda^2 X Y^2+4,  c=4A^2-1,
    c/k>(X+1)^2/(2X+1)>(X+1)/2.

Combining this with c/k<Y+1 yields 2Y>X-1, hence 2Y>=X because X,Y are integers. Substitution into c gives `c>lambda^2 X^4-1>2q^4`. Therefore the later use c>2R is justified after the independent mask bound R<q^4 is recovered.

## Third-order inverse and transport

I independently expanded the proposed T3 after substituting the first four recurrence coefficients, using separate exact Fraction-valued polynomial arithmetic in Q[m,x]/(x^4). All coefficients of degrees zero through three vanish after subtracting 2m. This verifies the symbolic identity for indeterminate m rather than sampling finite indices.

Because the final T3 has integer coefficients and the full recurrence polynomial has integer coefficients for each integral m, the remainder belongs to x^4 Z[x]. No inversion of 6,360 or15120 modulo a variable modulus is implicit.

The correction-sign estimate also holds. For t=k^2>=4, the relevant quadratic is

    675t^2-1458t-176
      =675(t-4)^2+3942(t-4)+4792>0.

Hence T3(k,x)<=k at k>=2,x>=1. This supplies e*<b uniformly even when the proposed rank R is negative. Together with the separately established |b|,|V|,g bounds, the carrier excludes B<0 before invoking positive-rank mask estimates. There is no sign circularity.

## The denominator and projector order

Integral z=Z/(h q^7) gives

    q^7 | h(e*-q^4Y).

Canceling h is legitimate because h=q-1. This proves q^4|e*, and the inverse identity yields q^4|(2m-R-1). Its absolute value is strictly smaller than q^4, so 2m=R+1.

The independently integral input kappa and its equation K-kappa H=0 give H|K directly. There is no need to assume gcd(q,H)=1. The retained universal projector yields

    H | (X-2^R)(2^R X+1).

The entire product is bounded, rather than canceling an unproved coprime factor. With R=2r+1, X>=32,r>=48, its stated majorant is smaller than X^(r+1)<H; the two normalized summands at the limiting point are exactly 2^(-137) and 2^(-45). Thus X=2^R.

Only then is q known to be a power of two. The inequality R>3q>=7 log_2(q) supplies q^7|X, making the full correction quotient integral. The remaining carrier congruence gives q^3|Y and h|B using gcd(q^3,h)=1 and W=1 modulo h. This order repairs the genuine obstruction in the rejected ten-variable shortcut.

## Completeness and positivity

The uniform ratio theorem is stated and proved for every positive integer dilation, so it applies at the fixed value lambda=210. Starting from canonical native outer data, it supplies positive eta,zeta at the new bases. The universal projector supplies integral positive kappa.

A finite period of the determinant-one Pell matrix modulo c^2 tau provides positive strong ordinates divisible by c^2 tau. Arbitrarily large positive multiples of that period make `g>kappa+sigma+|rho|` while leaving the already fixed outer data unchanged. This proves the final independent input n positive even if the third-order correction is negative.

For the new auxiliary construction, R=3 modulo4 and the quotient Chebyshev identities give V=-c modulo f and V=-R modulo c. The identities f=1 modulo c and gcd(f,c)=1 then make

    T=(V+c+Rf)/(cf)

a positive integer. The defined n gives the exact carrier z=gy. Therefore both P0 and N vanish with all eleven declared inputs strictly positive. No inverse map of arbitrary positive source tuples is assumed.

## Exact degree independently checked

The degree vector `(Q,M,G,V,Z)=(58,8,36,30,44)` makes `-QM^2GV^2` the unique degree-170 contribution to P0. Its leading form is

    -16 lambda^36 q0^46 w^24 Y^56 i^10 k0^32 (q0-F)^2.

The degree-four part of N is

    q0 w [3k0Y-2q0w-4lambda kappa Y].

Thus the degree-174 part of the final product is three times their product. Selecting the kappa term, the q0^2 term, and the eta^32 term gives the nonzero coefficient

    192 lambda^37 beta^49

at `J^49 w^25 Y^57 i^10 eta^32 kappa`. The exponent sum is174, and that selection is unique. This certifies attained degree at the actual fixed positive beta, not just a circuit upper bound.

## Boundary

This is an independent AI mathematical review, not external human peer review or a fresh end-to-end Lean/Rocq build. The signed folding, normalized strong-rank, ratio/half-binomial, native controller and logical refutation calibrations remain the identified inherited theorems. The finite checker separately authenticates the literal circuit, coefficient tuple, operation count and formal inverse coefficients. Neither type of check establishes Con(ZFC) or its negation.
