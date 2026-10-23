# Independent review of the signed bootstrap and quadratic batching

Reviewed the new `build_nine.py`, `source_data.json`, and Sidon weight list,
against package37's `nine/PROOF.md` at ProveIt commit
`22e75dd6b87b1b199bb08c778d7cf075ae5aae08`. This review focuses on the new
source packing and on the order of the sign arguments. It is a mathematical
cross-check, not a new proof-assistant certificate.

Outcome: the signed bootstrap and coefficient-extraction mechanism are
sound in the stated order. In particular it is intentional and harmless
that R can be negative away from zeros of the final polynomial.

## 1. A nonzero packed rank before any margin is known

Write Q0=B^(M+1) for the low code-block modulus, to distinguish it from the
later Jones register Q. The new source expressions are

    S = g+Q0*S0,
    T = Q0-1-(b-1)*ell+Q0*(B-2)*zero_mask,
    R = S*(N^2-N)+(T+1)*(N^2-1).

Since Q0 divides N, we have the unconditional congruence

    R = (b-1)*ell mod Q0.

All Sidon weights used in ell are distinct, positive and at most M. Since
B=kappa*b^2>b>=2, the base-B digits of (b-1)*ell are b-1 at those weights
and zero elsewhere. Consequently

    0<(b-1)*ell<Q0.

Thus R is never zero, even when g is arbitrarily large and R is negative.
No carry or bitwise property of an eventual solution has been assumed.

## 2. The inherited majorants really permit negative R

Let sigma=Y(U+1), r=bw+phi, s1=r+1. Then sigma>=2, r>=2,
A=R*sigma and C=2R+s1. Since R!=0, |A|>=2. Also

    P=2R^2Y^2U>=2R^2>=2,
    K=R+1+h(P-1)>=R+P>=2R^2+R>=1.

It follows that J=4A-5 is nonzero, AJ>0, D>=1, AE>=0 and F>=1.
These are sufficient for package37's unconditional majorants; they do
not require A,R,C or H to be positive.

For MD=AC+sigma*s1^2+1,

    MD-AC=sigma*s1^2+1>0,
    MD+AC=sigma*(4R^2+2R*s1+s1^2)+1>0.

The quadratic form in the latter expression is positive. Since all
quantities are integers, MD>=|AC|+1 and hence D<=MD^2. Similarly
MF=AE+1>=1 and F<=MF^2 because AE>=0.

For the I-majorant, H=(j+1)C-r and TCH=CH+r^2 satisfy TCH>=|CH|:
the plus-sign inequality is the exact identity

    TCH+CH = C^2+(C-r)^2+2jC^2 >= 0.

Writing G=FDC+F-A(F-1), the inequalities |H|<=H^2 and
|AH|<=A^2+H^2 show

    |GH|+|H|+1 <= FD*TCH+2F*H^2+(F-1)*A^2+1 = MI.

Therefore sqrt(|I|)<=MI. The absolute value is important: even a
negative candidate I is allowed at this stage. Multiplying the three
bounds gives sqrt(|DFI|)<=MD*MF*MI. With the added ones in V0,V1,

    sqrt(a0)<=V0-1, sqrt(|a1|)<=V1-1,
    V0,V1>=2.

All hypotheses of the signed-divisor finalizer are therefore available
before recovering a positive R. Candidate zero/negative radicands, C=0,
and H=0 are covered by these inequalities.

## 3. Finalizer first; source positivity second

The source signed-divisor lemma applies because u=JF!=0 and

    |v/u| = |Q/J+(H-C)/F|
           <= |Q|+|H-C|
           <= Q^2+(H-C)^2 = Mdiv-1.

The final circuit and manuscript both use plus v in Theta, consistently
with the predecessor's finalizer convention. The absolute quotient bound
and the displayed signed-divisor argument therefore apply directly. They
force the two square conditions, u|v, and margin>0 without a sign assumption
on R.

The positivity of the margin now gives

    8g<Gcap=32bB^M, hence g<4bB^M.

Only after this step is source positivity used. If C is the fixed absolute
coefficient bound recorded by the source builder, then

    |e(B)| <= (C-1) B^(length-2M-1).

Integrality gives 1+g<=4bB^M. Consequently

    |2(1+g)^2 e(B)|
       <=32(C-1)b^2 B^(length-1)
       < B^length/64,

because kappa>2048C. The background B+...+B^length is at least B^length,
so S0>0. Its matching upper bound gives S<N. The explicit mask expression
has 0<=T<N, and hence the packed rank is positive and has the ordinary
range required by the Jones packing/ratio interface.

This ordering resolves the potential circularity from the fact that e(B)
has a negative highest coefficient in the current row orientation.
Orienting residuals differently is optional; it is not needed for soundness.

## 4. Why B2 weights are sufficient for all 22 quadratic equations

Adjoin the weight a0=0 for the constant coefficient and use the 31 listed
positive weights a1,...,a31. Their 528 unordered pair sums are all distinct.
For a quadratic residual r_j and multi-index alpha with |alpha|<=2,
the source coefficient at exponent 2M-sum_i(alpha_i*a_i) is

    (2-|alpha|)! * product_i(alpha_i!) * coefficient_alpha(r_j).

Therefore the coefficient at exponent 2M of

    2*(1+sum_i x_i Z^a_i)^2 * e_j(Z)

is exactly 4r_j(x). Pair-sum uniqueness, including the zero weight,
excludes every unintended contribution. This follows by cancellation
of the quadratic multinomial coefficients, not by an empirical sample.

Each block has degree at most4M. The stride4M+1 therefore separates
the products from different residuals. All22 target coefficients can be
tested simultaneously by the repeated zero mask. The large exponent
of the quartic sum-of-squares compressor is avoided because each source
residual is quadratic before the final conjunction is encoded.

## 5. Signed digits and carry direction

After the Jones arithmetic has supplied the power-of-two base, the low
block of the disjointness test forces g to have digits x_i<b precisely at
the allowed weights and zero elsewhere. This step needs g<Q0, which
already follows from g<4bB^M and B>4b. It does not need bounds on the
quadratic coefficients yet.

For such a digit polynomial, the sum of absolute coefficients of
1+sum_i x_i Z^a_i is at most32b. Hence every coefficient z_t of the
signed correction 2(1+g)^2 e satisfies

    |z_t| <=2048C b^2 < B.

Every z_t is even. Use the background B*(1+B+...+B^(length-1)) as
the raw coefficient B in every digit position. During radix reduction,
the incoming carry is always0 or1: B+z_t+carry lies between2 and2B-1,
since B and z_t are even. Thus the outgoing digit is z_t+carry modulo B.
At a target the mask B-2 permits only the digit0 or1. Under |z_t|<B
and evenness, this occurs if and only if z_t=0. The target condition is
therefore exactly r_j(x)=0, independently of the incoming carry.

The parent shifted system cannot vanish at the all-zero x: its fifth
residual equals1. Thus a genuine parent solution always encodes a
strictly positive g, as required by the Jones interface. The source
normalization used in the completeness direction is preserved.

## Boundary of this review

This note checks the new arithmetic packing and the unconditional sign
bootstrap. The inherited Jones ratio theorem, native compiler theorem,
and literal K215/ZFC syntactic-refutation calibration remain named
unbounded dependencies. Neither this review nor the finite arithmetic
receipts establish a new end-to-end kernel certificate.
