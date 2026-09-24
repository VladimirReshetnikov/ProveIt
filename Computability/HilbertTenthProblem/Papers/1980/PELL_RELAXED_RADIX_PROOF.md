# The Pell block only needs B at most n before decoding

This note audits the relaxed bootstrap needed when the homogeneous encoding
moves the input x to weight zero and uses the arithmetic register C_code=x+g.
It does not alter the frozen Pell or 110-operation proof files. In this note
C_code is the digit polynomial's value; it is distinct from the Pell
denominator c.

The removed input shift means C_code<q no longer proves B<q. That stronger
inequality is unnecessary before the Pell implications. The geometric
equation and positivity already give

    q^2-1=lambda*(B-1), lambda>=1  ==>  B<=q^2.

With n=q^8, this implies B<=n. The bound 3L<=B still follows from the fixed
choice of H and B=H*b^2. Thus the exponent comparisons used in the existing
Pell proof remain valid in their original form.

## All packing bounds before invoking the Pell block

Use the changed code C_code=x+g, the mask factor B-4, and the same reversed
packing equations. Put Y_code=ell+e*q. Positive alpha and

    Y_code+C_code^2+alpha=q^2

give 0<ell<q^2, e<q, C_code<q, and g<q. Also b=x+beta>=2. The admissible
scale satisfies H>16 and B=H*b^2, so B<=q^2 implies q>4b>=8. In particular
b<=n and q<=n. Since B>2Z and B-Z>b,

    lambda < 2q^2/B,
    b < N_mask=(B-Z)*lambda < q^2-1.

Here lambda>q is not asserted or used.

The additional positive unknown sigma=S3 gives the needed lower bound
for the third block. The upper bound is unchanged:

    0<S3=(2e-Z*lambda)*C_code^2+B*lambda*(1+q)
        <2q^3+2q^2*(1+q)<5q^3<q^4.

Therefore

    S=g+q^2*(Y_code+q^2*S3)

lies strictly between zero and q^8=n.

For the first raw mask define

    d=floor((b-1)*ell/q^2),
    u=(b-1)*ell-d*q^2.

Then 0<=d<b, 0<=u<q^2, and the exact normalized packing of T is

    T=(q^2-1-u)+q^2*(N_mask-d)+q^4*(B-4)*ell.

The three block values belong to [0,q^2), [0,q^2), and [0,q^4),
respectively. For the third one, use B<=q^2 and ell<q^2; for the middle
one, use N_mask>b>d. It follows directly that 0<=T<n. Consequently

    r=S*(n^2-n)+(T+1)*(n^2-1)>=n^2-1>=n.

All of these statements precede canonical decoding, and none assumes
B<q or that the first raw mask is nonnegative.

## Exact hypotheses used by the Pell proof

The initial information now available is

    3<3L<=B<=n<=r,  q<=n,  b<=n,  n,r>=8.

B is even because H is a fixed even power of two, independently of b.
Compare this with the initial line of PELL_SHIFTED_BASE_PROOF.md. Its
subsequent arguments use B only through B<=n, 3L<=B, and this evenness.
Here is the complete dependency audit.

Write N=n, R=r, U=w*N^2, Y=s*N^2, M=R*Y, A=a=M*(U+1), and J=2R+1.
The bounds U,Y>=64, M>=512, A>=33280 are unchanged. The positive interval
and index congruence for k give c>J. Thus the signed Pell block gives
c=psi_A(J), d=chi_A(J), without a radix comparison.

With X=2U*M^2 and shifted parameter P=X+1, the same Pell growth and
congruence argument gives k=psi_P(R+1). Its exact-index ratio satisfies

    xi*(1-R/A-R/X)<c/k<xi,  xi=(U+1)^(2R)/U^R,
    R/A+R/X<2/[Y*(U+1)]<1/2.

The positive interval therefore implies Y>U^(R-1) and A>R*U^R.
This part of the proof uses no B or q comparison.

The base-two exponent argument still has

    2^(3J)<=8*N^(2R)<=R*U^R<A,
    (bw)^3<=U^R<A,

because b<=N. E14 therefore gives bw=2^J, b a power of two, and
U>4*2^(2R), exactly as before.

The bound 3L<=B<=N<=R gives 0<L<J<A. The positive gap c>kappa, E19,
and E20 consequently give kappa=psi_A(L), mu=chi_A(L). The second
exponent argument uses the unchanged comparisons

    B^(3L)<=B^B<=N^N<=U^R<A,
    q^3<=N^N<=U^R<A.

These follow from 3L<=B<=N and q<=N; B<q is not needed. Also a>B
already follows from a=R*Y*(U+1)>N>=B, so its positive modulus
2aB-B^2-1 has the required sign. E18 and the chi exponent lemma now
give q=B^L. In particular B<q is recovered before any digit-evaluation
or high-mask argument requires it.

B was even already, so q and N are now even. The parity rounding and
positive-witness maps of PELL_SHIFTED_BASE_PROOF.md apply verbatim.
They give N^2 dividing binom(2R,R).

## The earlier gap replacement and necessity

The positive-domain justification of E13, namely c=kappa+phi, in
PELL_GAP_PROOF.md only uses n>=2 and

    a=(w*n^2+1)*r*s*n^2>=20r.

Both remain true here. Thus relaxing the radix comparison does not
invalidate the earlier spacing argument or its positive slack map.

For genuine encoded witnesses, the unit digit delta=1 is now placed at
weight one inside g. It makes g>=B, so the intended value C_code=x+g
is greater than B anyway. Necessity therefore has all the stronger
original bounds as well. The previously proved Pell necessity
constructions and their positive witness choices remain available.

This completes the audit of the relaxed bootstrap. No extra arithmetic
operation or system equation is required for this argument.
