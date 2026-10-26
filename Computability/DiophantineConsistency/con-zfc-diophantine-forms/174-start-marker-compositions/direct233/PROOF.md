# A 233-variable integer quartic by composing a linear selector with a self-power horizon

## Exact scope

The new equation is the sum of squares of 169 explicitly supplied quadratic residuals in 233 independently unrestricted integer coordinates. Two invertible integer row bases give the following exact profiles:

| Variant | Variables | Residuals | Degree | Collected monomials | Coefficient height |
|---|---:|---:|---:|---:|---:|
| P233_balanced | 233 | 169 | 4 | 18,482 | 5,632 |
| P233_sparse | 233 | 169 | 4 | 10,182 | 8,880 |
| P234_sparse companion | 234 | 170 | 4 | 5,018 | 8,880 |

The arithmetic source is package165's literal `signed/power239/equation.json`, at ProveIt commit `fb1bed5eb7196cf35abfaa746c18c6ee7eae6cfb`. The semantic change combines the linear binomial radius and mod-four radix argument of package164 with package165's self-power horizon and wider spherical remainder budget. The new composition is proved below; it is not a claim that those ingredients are new. The final four projections and residual-basis operations are exact polynomial maps preserving integer zero sets. The source calibration to finite C222, ZF and ZFC refutations is an explicitly inherited ordinary theorem. No complete new proof-assistant verification or proof of consistency is claimed.

## 1. Literal changed interface

Use semantic names t,F,R,B,x,y,q,H,N,M. The source already has the cofinal horizon and authenticated power

    t = 16 + 2h^2,       F = t^t,

the beta equations

    y = F(2w+1)^2,
    x = F+1+(y+1)u0,
    x = 1+[1+(t+1)y]ut,

the binomial index row

    B mu = C0+R+1,

and requests for B's binomial numerator, q=(BH)^x, N=B^x, M=q^x and the normalized digit powers. Retain every power request, frame atom, both-coordinate Pell orientation condition, semantic-anchor cap and local Horn polynomial.

Change only

    R=F^2  to  R=F,
    q=(2z+1)^2  to  q=4z+1.

The eleven normalized low remainders retain the already present sphere

    M^2 = 2 sum_i Ri^2 + G(a,b,c),
    G(a,b,c)=a^2+b^2+c(c+1).

Here G is nonnegative at every integer triple and represents every nonnegative integer (apply the three-square theorem to 4n+1). The sphere need not by itself exclude M=0; nonzeroness is established from the radix and power requests before division.

In the literal 239-coordinate equation, F=x3, R=x4, the stored radix is x101=q+1, and z=x236. The changed rows are R0 and R173. Their new affine restorations are x4=x3 and x101=4x236+2. The `+2` is essential. The actual horizon is x0, despite its historical name `t0`; row155 reads x0=16+2x212^2. The actual beta parameter is x2-1. The first actual CRT representative is x9-1 and the other eight are x10,...,x17. Consequently the source's row154, which defines BH=B(1+sum(x9,...,x17)), means

    H=2+sum of the nine actual representatives.

Thus H>=2 after nonnegativity recovery. This is the power branch's offset, not the different offset in the shared-factorial branch.

## 2. The lcm estimate and the new selector radius

Let Lambda_n=lcm(1,...,n). We give the elementary bound Lambda_n<=4^n. Set k=ceil(n/2). Every prime power p^a<=n either already divides Lambda_k or satisfies p^(a-1)<=k<p^a. In the latter case the p^a-level summand in Legendre's formula for v_p binom(n,k) is one. Thus

    Lambda_n divides Lambda_k binom(n,k).

If n=2m, the middle coefficient is at most 2^(2m)=4^m. If n=2m+1, the two equal middle coefficients together are at most 2^(2m+1), so each is at most 4^m. Induction from Lambda_1=1 proves Lambda_n<=4^n. Therefore t>=16 gives

    R=F=t^t >= 16^t >= Lambda_t^2.

Here the weak inequalities suffice. No assertion that t! divides F is made.

For completeness, the selector theorem needed by the retained generalized binomial-CRT argument has two parts. If R>=Lambda_t^2 and B=binom(R+t,t), then for each i in [1,t] there is a prime power p^e exactly dividing B, with p^e>t and p^e dividing R+i. Conversely every prime power exactly dividing B divides at least one R+i.

For the first part, R+i>Lambda_t^2, so some prime p has v=v_p(R+i)>2a, where a=v_p(Lambda_t). Otherwise R+i would divide Lambda_t^2. For j!=i, v_p(R+j)=v_p(j-i). Hence

    v_p(B)=v-d,
    d=v_p(t binom(t-1,i-1))<=a.

The last bound follows from Legendre's formula: each summand is zero or one, and all levels above a vanish because p^(a+1)>t. Thus e=v-d>a, so p^e>t and p^e divides R+i. For the converse, let v=max_i v_p(R+i). Legendre's expression for v_p(B) has only zero-one summands and has no nonzero level above v, so e<=v. A maximizing i works. This explicitly checks both directions required by the source's prime-power CRT construction.

## 3. Signed radix recovery has no circular positivity assumption

The retained signed Pell/power interface, whose squared frame is independent of front signs, authenticates any request at nonzero integer base n. For |n|>=2 it forces the requested exponent nonnegative and gives exactly n^k. At n=+/-1 it gives the corresponding unit power for every signed integer k. We use no request at base zero.

The positive t request first gives F=t^t>=16^16=2^64, and the beta square then gives y>=F>0. The affine radix makes q different from 0 and -1. Suppose q=1. The requests at q+1=2 force all actual representatives nonnegative, so H>=2 and C0>=0. The index row B mu=C0+F+1 forces B!=0. Therefore |BH|>=2, and q=(BH)^x gives x=0. The last beta endpoint cannot hold at x=0: its positive bracket exceeds one and cannot divide -1. This contradiction excludes q=1.

In every remaining case |q|>=3 and |q+1|>=2, so the same representative/index argument gives H>=2 and B!=0. The self-radix power forces x>=0; x=0 is excluded. If u0<=-1, the first endpoint gives x<=F-y<=0, also impossible. Therefore

    x>=F+1,
    x>=2+(t+1)y>=2+(t+1)F,
    Q:=|q|=|BH|^x>=2^x,
    Q>=4B^2 and |B|<=Q/4.

All nonzero q and q+1 requests now have their genuine meanings, including M=q^x!=0 and all denominator powers L_i. From L_i vi=M and vi Ui=M Qi+Ri, the integer vi divides Ri; division gives Ui=L_i Qi+ri. The sphere yields

    |ri|<=|L_i|/sqrt(2)<3|L_i|/4.

This proof does not assume signs of vi,L_i or M.

## 4. Digit recovery and the smaller binomial

Put n=F+t and Cj=binom(n,j). For j<=t,

    Cj <= (F+1)^t <= (F^2+1)^t =: V.

V is proof notation, not a new register. Since F>=7, F^2+1<=2^(F-1). The endpoint bound on x gives V/Q<=2^(-F-t-2), and in particular V/(Q-1)<1/32. For either sign of q the genuine low tail rho=sum_{j<t} Cj q^j therefore has |rho|<|q^t|/32. The recovered remainder is congruent to rho modulo q^t and has magnitude below 3|q^t|/4; their difference has magnitude below 25|q^t|/32. It follows that they coincide. The digit equation then gives B=Ct modulo q. Because 0<Ct<Q/32 and |B|<=Q/4, this congruence is an equality:

    B=binom(F+t,t)>0.

Consequently q=(BH)^x>0. The negative-radix branch has been excluded arithmetically. Also B>=F+t>F+1, so the index row excludes C0=0. The remaining source coefficient/label estimates are unchanged: x>2^32, F>2^22, and 2^22(t+1)<x. The local majorant (2x)^(2^23)<2^x still holds; all remaining canonical low tails are less than L_i/32. Their normalized sphere bounds thus recover every digit exactly by the same divisible-difference argument. The selector theorem in Section2 gives the retained all-primes local-row extraction and reverse CRT construction at the new radius.

## 5. Authentication of label multiplicities at F=t^t

This step uses the self-power proof, not the older inequality (t+1)^t<F, which is false here. The local beta updates give the source's positive weight identity with factors 1+jF, 0<=j<=t. The boundary y=F is impossible: it would give initial accumulator zero and final accumulator one, while every update propagates zero. Remove the unit j=0 factors. One side has at most t factors. If factor counts differed, the larger side would be at least (F+1)^(d+1), where d<=t is the smaller count, and the smaller would be at most (1+tF)^d<=t^d(F+1)^d. This contradicts F+1=t^t+1>t^d. Thus both sides have the same degree d<=t as products of linear factors in an indeterminate Z.

Every coefficient of degrees 0,...,d in either product is a positive integer at most binom(d,k)t^k<=t^d<=F. Therefore corresponding coefficient differences have absolute value at most F-1, even when an individual coefficient equals F. If the two polynomials differed, their lowest nonzero coefficient, after dividing their equality at F by the corresponding power of F, would be a nonzero multiple of F of magnitude below F. Contradiction. Thus the two polynomials agree. Their distinct roots -1/j give exact label multiplicities. The retained single-conclusion Horn-closure argument then yields a finite C222 derivation. Its inherited ZF/ZFC calibration gives a finite syntactic ZFC refutation.

## 6. Constructive completeness

Begin with a finite calibrated refutation and pad to a sufficiently large allowed even horizon t=16+2h^2. Set F=t^t and R=F. Since t is even, v2(F)=t v2(t)>=t>v2(t!). An arbitrarily large odd multiple w of the odd part of t! makes y=Fw^2 an even multiple of t!, larger than every pending-multiset accumulator and F+1. The beta moduli 1+(i+1)y are pairwise coprime and odd. Their CRT code x can be chosen arbitrarily large and even.

For i<=t, v2(F)>floor(log2 t) gives v2(F+i)=v2(i). Hence B=binom(F+t,t) is odd, as are N=B^x and N^2. The retained all-primes binomial CRT construction applies by Section2. Its representative parities can be adjusted by adding N^2: choose the dominant first actual representative odd and the other eight even. The old opposite-parity and dominant-anchor conditions remain satisfiable, and H=2+sum actual representatives is odd. The new front index F+t lies below B^2<N^2, as required by the existing dominance bounds. Choose all required representative lifts before the self-sized radix.

Now q=(BH)^x is an odd square, so q=1 modulo4 and z=(q-1)/4 is integral. The canonical normalized remainders satisfy 0<=Ri<M/32. Therefore 2 sum Ri^2<22M^2/1024<M^2; the remaining integer gap has a G representation. The unchanged Pell/frame completion supplies all remaining witnesses. This constructs a zero of the edited source. It is a zero-existence argument, not a bijection between every original and edited assignment.

## 7. Exact finite projection

Delete the two new monic affine rows, restoring R=F and stored_q=4z+2. This gives a literal 237-variable,173-row source. Three projections along common Hessian-kernel directions remove three coordinates and rows without increasing residual degree. An affine label-definition projection removes one further coordinate and row, giving 233 variables and169 rows. Every projection is verified from its complete coefficient arrays, with explicit integral polynomial inverse maps. Subsequent elementary row operations are inverted in reverse order. Squaring and adding the final rows yields a literal quartic; its expanded coefficients are included and checked exactly.

The four new algebraic projections are integer-zero-set bijections. The preceding semantic source edit preserves existence via Sections2--6. Composing with the inherited source calibration establishes, in ordinary mathematics formalizable in ZFC,

    exists z in Z^233: P233(z)=0  iff  a finite ZFC refutation exists.

Negating gives the requested equivalence with Con(ZFC). The artifact verifier checks all new finite algebra and the exact 245-to239 source interface, not all historical arithmetic or formal-logical dependencies. In particular some historical dependency files advertised by package165 are absent from the inspected Git tree; the release does not claim to have replayed an unavailable inherited checker.

## Provenance and novelty boundary

Source165 supplied the self-power even horizon, wider sphere, and literal239-coordinate source. Source164 supplied the linear-radius/mod-four idea and signed bootstrap. Source159 supplied the common-radical and affine projection/reversible-row tools and independent checker. This package's contribution is their compatible composition, its proof obligations and explicit new233-coordinate output. The elementary lcm inequality is classical. No worldwide novelty, global simplicity minimum or end-to-end formal-kernel certification is asserted.
