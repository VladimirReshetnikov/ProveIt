# Independent review of the eleven-integer linear multiplier

## Verdict and scope

The new arithmetic transformation in
`research_low/linear_multiplier11/PROOF.md` is accepted as an ordinary
mathematical proof, relative to its explicitly identified inherited native
calibration and signed-Pell source theorems. I found no gap in the new signed
bootstrap, variable-weight radical separation, square recovery, or the
rescaled completeness argument. The degree 412 / 127-operation centered
form and degree 440 / 126-operation direct form are supported by the literal
circuits and the checked degree identities.

This is an independent review within the AI-assisted preparation of this
packet, not external peer review. It is not a new complete Lean/Rocq or
object-language ZFC derivation. I read the new proof, the immediate mixed
parent, the full supported-modulus interpolation argument, the underlying
full-residue period/valuation proof, relevant generalized signed-rank
sections, and the stated source calibration boundary. I did not independently
reprove the entire transitive native/compiler/refutation chain.

## 1. Signed bootstrap

Before extracting any square roots, S=0 reduces the norm polynomial to
Ac^8. The homogeneous quintic carrier Ac is nonzero because its denominator
scale MH is nonzero and (t^2+3)(t^3-19) has no rational root. Thus s,r are
nonzero at a polynomial zero.

The auxiliary Da is positive in all three required cases: c=0 gives Da=1;
c!=0,r<0 gives two negative factors Q-1 and QV^2-1; c!=0,r>0 gives Q>1
and a nonzero V by Df>|c|+1. Likewise rDf is positive whenever c!=0.
Its only negative case is c=0,r<0.

If exactly one of rDf,P is negative, its radical is the sole imaginary
term in a vanishing conjugate factor. If both are negative, c=0,r<0 and
imaginary cancellation gives 1=9rP, impossible for integral r,P. The guard
Dg is 1 modulo 4, so P cannot be zero. Thus both rDf and P are positive.
This proves positive budget before any source interpretation is invoked.
The order avoids a circular use of c!=0 or a signed strong Pell theorem.

## 2. Variable 3-adic weights and recovery of r

The three normalized radicands are rDf, Da, P with weights 3,1,9r.
Writing a=v3(|r|), b=v3(P), Df=Da=1 modulo 3 gives the stated within-class
coefficient valuations. In a squareclass with 3-part epsilon, the strong
valuation is 1+(a-epsilon)/2 and the guard valuation is
2+a+(b-epsilon)/2; the latter exceeds the former by 1+(a+b)/2.
The auxiliary term, when present, has valuation zero. Hence a nontrivial
squareclass cannot cancel. All three positive radicands are squares.

The factor rDf is square and gcd(r,Df)=1. The factors therefore have the
same sign and square absolute values. Negative Df is impossible because
Df=1 modulo 3 whereas a negative square is 0 or 2 modulo 3. Consequently
r=u^2>0 and Df=f^2. This works for every integer input r, not just one
whose sign or valuation has been restricted in advance.

## 3. Restoration and the auxiliary descent

Monicity of the homogeneous carrier gives M|zc from M^5|Ac. Since
gcd(M,H)=1, the exact cubic scale follows. It makes Y nonzero; only then
does positive budget rule out c=0. The recovered strong coordinate is
I=c^2u and the former auxiliary coordinate is T_old=uT. The resulting
norms and two congruences are exactly the hypotheses used by the parent's
pre-projection folding and rank argument. No claim of a pointwise zero
map to the old mixed carrier is needed; the proof restores the generalized
native source and then its fresh witnesses.

The rational auxiliary ordinate descends integrally: writing y=a/b in
lowest terms gives b^2|(Q-1). The stated transformation preserves the norm,
keeps V integral and the reduced denominator b, and decreases |V| after
sign reflection until |V|=|y|=1. A minor exposition correction was requested:
the endpoint should say |y|=1, rather than y=1, unless its reflected sign
has just been fixed. This does not change the argument.

## 4. Completeness and fixed-pair quantifier order

The strong pair is fixed with 4s c^2|I before any residue is requested.
Set u=I/c^2 and r=u^2; every prime of s*u^3 divides I. The retained
supported-modulus theorem therefore applies with modulus u*m=s*u^3,
where m=s*r. Asking for T_old=u*a0 modulo u*m gives both u|T_old and
T_old/u=a0 modulo m. This is exactly the extra modulus needed after
linearizing the multiplier. Merely interpolating T_old modulo m would
not have justified the division.

I checked the retained theorem's prime-power argument: the common index
increment d=lcm(4m0*f,4I) has v_p(d)=v_p(4I) for p|I; the Pell addition
formula and explicit lifting valuations give an exact p-adic isometry
after division by 4If^2. This implies bijection on each supported prime-
power residue ring, followed by CRT. The argument keeps I,f fixed.
The stated hypotheses on the canonical outer witness are supplied by
the copied interpolation source.

The carrier quotient Ac/S=H^4*pi(T+kappa)/(sr) is then an integer, and
the explicit n closes a conjugate norm factor. There is no later change
of strong pair and no hidden positivity requirement on n.

## 5. Independent degree calculation

I independently recomputed

    B_top = 2^14 s^2 r^6 q0^20 a0^14 c^16 R0^2,
    G_top = -2^16 3^5 s^4 r^4 q0^22 X0^6 Y0^12 k0^6.

The centering identity B-(SQV)^2=-S^2[Q(V^2+1)-1] gives
deg(Z^2-B)<=90. The unique top inner term is -4BG of degree 206,
while the external correction has degree 362. Thus the centered degree
is 412 with top form 16B_top^2G_top^2. The direct chart has the uniquely
dominant radicand B, giving top form B_top^4 of degree 440.

Taking h^12 then z^4 yields the centered coefficient
2^384*3^278*beta^216 at the stated degree-412 monomial. The corresponding
direct coefficient is 2^392*3^280*beta^224. Both are positive at the
authentic tuple. These arguments establish the degrees of the whole
polynomials, not only upper bounds or behavior on solutions.

## 6. Fresh finite replays

I ran the supplied independent finite checker afresh under normal Python
and under -O, recording `LOW_VARIABLE_NORMAL.json` and
`LOW_VARIABLE_OPTIMIZED.json`. Both passed: the six complete coefficient
payloads, 83 retained source-file identities, literal circuit definitions,
35-coefficient universal norm identity, whole leading forms, operation
counts and all eleven variables. Seven altered circuit nodes were rejected
for each variant in each mode. The bounded controls remain explicitly
diagnostic; they do not prove the unbounded arithmetic lemmas.

These checks support inclusion of both circuits with the ordinary proof
and the retained calibration material. They do not establish Con(ZFC)
or the absence of polynomial zeros.
