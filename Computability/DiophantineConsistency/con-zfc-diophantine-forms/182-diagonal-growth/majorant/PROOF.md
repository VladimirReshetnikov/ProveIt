# A sharp checked polynomial label bound for the diagonal horizon

This note improves the constructor-depth exponent `2^20` to a rigorously
certified bound sufficient for the diagonal horizon with **c = 464**.
The finite checker executes the actual authenticated source's `codes_only`
path through a positive arithmetic DAG. It does not expand the huge polynomial.
The unbounded argument is the coefficient comparison below.

## 1. Exact source and the polynomial being bounded

Pinned repository commit:
`953fb4d82d4229f4efc5f9db4cc2bf38ae329bb4`.

Source path:
`Computability/DiophantineConsistency/con-zfc-diophantine-forms/112-powered-saturation-round14/intake/ConZFC_Shell_Reciprocal_660_2026-10-24/ConZFC_Shell_Reciprocal_660/code/shell_source.py`.

The preserved source has 2955 bytes and SHA-256
`59c68a354fe5cdbc04bde33720080db2436cb51ae25e3485ac5ae45ff4230199`.

The constructors are

    I(a,b)=2((a+b)^2+a),   M(a,b)=I(a,b)+1,
    A(a,b)=2((a+b)^2+3a+4b+3),   E(a,b)=A(a,b)+1.

Let J be the sum of the nine actual source axiom-code expressions, followed
by the five expressions a,b,I(a,b),A(a,b),1. Write j(s)=J(s,s,s,s).
All coefficients of J and j are nonnegative integers. The exact degrees of
these fourteen summands, in source order, are

    16, 8, 8, 8, 8, 32, 16, 8, 524288, 1, 1, 2, 2, 0.

Thus j has exact degree D=524288. Positivity prevents cancellation of a
leading term. These assertions are obtained from the actual source DAG,
not from a separately transcribed list of formula schemata. The logical
claim that every selected local rule label belongs below this J remains
the same source-interface claim used by the parent label-separation proof.

## 2. A finite coefficient-growth lemma

If p(X)=sum_(i=0)^D a_i X^i has nonnegative coefficients, t>=c>0, and d>=D,
then

    p(t) <= p(c)(t/c)^D.

Indeed, each t^i=c^i(t/c)^i is at most c^i(t/c)^D. In particular,

    p(c) < c^d  implies  p(t) < t^d  for all t>=c.

The last step follows from c^d(t/c)^D <= t^d. This is an identity and an
inequality of ordinary rational numbers; denominators may equally be
cleared to give an integer proof. No assumption on solutions of a
Diophantine equation is involved.

The finite certificate proves

    j(464) < 2^5692913 < 2^5721263 <= 464^645888,
    645888 = 3*464^2 >= 524288.

Therefore j(t)<t^645888 for every integer t>=464. Since each independent
source parameter is an integer in [0,t-1], monotonicity gives

    J(a,b,c,d) <= j(t-1) < j(t) < t^645888.

In the displayed formula c is a source parameter; the fixed horizon
constant is always written explicitly as 464 to avoid overloading it.
The strict middle inequality follows because j has positive nonconstant
coefficients (it includes both source parameter summands).

## 3. Diagonal horizon

Set, for an unrestricted integer z,

    t = 464 + z^2,   K = 464t^2,   F = K^K.

Here the last equality is a semantic power request, to be represented by
the retained Pell-power equations in the final ordinary polynomial.
This note does not introduce an exponentiation symbol into that polynomial.

We show F>=t^(645888t). For integers t>=c>=3 one has c^t>=t^c.
For completeness, this fact has an elementary induction proof: at t=c
there is equality, and

    (1+1/t)^c <= (1+1/c)^c
                 <= sum_(j=0)^c 1/j! < 3 <= c.

The strict upper bound 3 follows, for example, from j!>=2^(j-1) for j>=2
and the finite geometric sum. Consequently c*t^c>(t+1)^c, which supplies
the induction step. Thus, with c=464,

    F=(ct^2)^(ct^2)
      =(c^t)^(ct) t^(2ct^2)
      >=t^(c^2t+2ct^2)
      >=t^(3c^2t)=t^(645888t).

The coefficient lemma therefore gives F>=L(t)^t for L(t)=t^645888. This
is exactly the large-label separation condition of the parent argument.
The horizon t is at least 464 and cofinal as z varies; it may be odd or
even. The requested index K is always positive and even. Indeed, since
464=16*29, the exact valuations are

    v_2(K)=4+2v_2(t),   v_2(F)=K*v_2(K)>=4K>2t.

This covers the entire power of two in t!, since v_2(t!)<t. Also
v_2(F)>floor(log_2(t)), so v_2(F+i)=v_2(i) for each 1<=i<=t. It follows
that the binomial B=binom(F+t,t) is odd. These arguments impose no parity
condition on t itself.

For the radius condition let Lambda_t=lcm(1,...,t). The elementary bounds

    Lambda_t <= t! <= t^t,
    F >= t^(645888t) >= t^(2t)

give Lambda_t^2<=F. Thus the parent binomial-CRT radius and parity
requirements continue to hold for the selected horizon t=464+z^2.

## 4. What the numerical certificate establishes

The checker uses only integer arithmetic. A pair (m,e) denotes the exact
dyadic value m*2^e. It computes lower and upper bounds at each source-DAG
node by rounding respectively down or up, retaining about 64 mantissa bits.
Addition aligns the dyadic exponents; multiplication multiplies mantissas
and adds exponents. Each rounding goes outwards, so induction on the DAG
proves that the resulting interval contains the exact integer.

Repeated squaring supplies the same kind of lower and upper bounds for
c^(3c^2). Both endpoints locate each integer in the same binary interval,
thereby certifying its exact bit length. The gaps of many thousands of
bits make the final comparisons particularly robust. The optional --exact
mode checks the two decisive cases by evaluating the full huge integers.

| c | 3c^2 | Bit length of j(c) | Bit length of c^(3c^2) | Outcome |
|---:|---:|---:|---:|---|
| 462 | 640332 | 5689646 | 5668059 | Insufficient |
| 463 | 643107 | 5691281 | 5694628 | Sufficient, odd |
| 464 | 645888 | 5692913 | 5721264 | Sufficient, even |

The failure for 462 is only a failure of this particular sufficient
majorant strategy. No lower bound on possible Diophantine constructions,
and no global optimality claim, follows from it.

Run:

    python3 check_label_majorant.py
    python3 -O check_label_majorant.py
    python3 check_label_majorant.py --exact

The certificate contains no enormous polynomial expansion or giant integer
payload. It records source identity, actual degrees, dyadic endpoint pairs,
and the decisive integer comparisons. All validation checks remain active
under Python's -O option.
