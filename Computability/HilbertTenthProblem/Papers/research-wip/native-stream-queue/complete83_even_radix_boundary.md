# Even-radix boundary for shared-projection83

Every positive zero of the shared-projection83 candidate on a valid inherited compiler slice has **even q**. Its cubed-scale condition has an exact four-term binomial congruence, without first proving q is dyadic. An explicit non-dyadic **scalar diagnostic**, with q=76, also has a full positive parametric completion and nonzero common offset. It is not a valid compiler instance or a rejected-input counterexample. These results narrow the unresolved candidate; they do not improve the established universal bound of84 operations.

No circuit row, witness, positivity requirement or fixed numeral port changes. The predecessor remains83=46M+37A with18 positive witnesses and exact degree187; the source/degree audit is inherited, not repeated here. This note reads the frozen source and proofs as inert data. Its fresh helper guards their hashes and source interface and checks only newly written bounded arithmetic.

## 1. Parity and exact half-binomial extraction

Use the accepted shared-projection offset theorem, including its pretyping proof. Write

```
q=(B−1)J+1, X=wq, Y=sq^3,
R=(q^2−Z−qF)(q^2−1)+(MC+qMF)J,
u=2dx+b, C=q−F−Z−alpha−2dx, W=C−Z,
r=(R−1)/2, a=Y(X+1), A=a+2, Delta=A^2−1,
H=4a+3, E=XY, P=2XY^2+1,
U=shared_projection, E_j=chi_A(j)−a*psi_A(j).
```

The source port MF is the shifted native mask MF0+B−1. The accepted theorem establishes, before dyadic radix or native mask decoding,

```
B is a power of two >=16, q>=B,
R=3 mod4, R>3q+1, R+2<q^4,
0<u<2q, |W|<q,
X−W=2^R−2^u,
c=psi_A(R), k=2psi_P(r+1), Y<c/k<Y+1,
Y>X^r/3, a>X^(r+1)/3, r>=24.
```

**Parity.** If q were odd, then J would be even since B−1 is odd. Both summands in the displayed expression for R would then be even: q²−1 is even and J is even. This contradicts R=3mod4. No mask-numeral parity or native mask decoding is needed. Thus q, and consequently X, are even.

**Size.** Since u<=2q−1,

```
2^u+q <=2^(2q−1)+q <2^(2q)<2^(R−1).
```

The middle inequality holds for q>=16, and the last follows from R>3q+1. Therefore the exact offset identity implies X>2^(R−1)=2^(2r), even when q is not dyadic.

Define the ordinary integer polynomial and rational tail

```
C_j=binom(2r,r+j), M_r(X)=sum_(j=0)^r C_j X^j,
xi=(X+1)^(2r)/X^r=M_r(X)+theta,
theta=sum_(j=1)^r binom(2r,r−j)/X^j.
```

The binomial symmetry gives `0<theta<2^(2r−1)/X<1/2`. The central coefficient is even (r>=1), and every other term contains the even X. Hence M_r(X) is even.

The elementary first/main Pell estimates in half-binomial42 §5, applied exactly as in the accepted offset proof, give

```
xi/2 < c/k < (xi/2)(1+8r/a),
xi<2Y+2, 0<c/k−xi/2<16r/(X+1)<1/2.
```

Their size hypothesis follows in the proper order from the already established lower estimate Y>X^r/3, giving a>8r. They require the individual Pell equations and size bounds, not the parent theorem's exponent equality X=2^R. Combining these estimates yields

```
M_r(X)/2 < c/k < M_r(X)/2+1/4+1/2 < M_r(X)/2+1.
```

Comparison with Y<c/k<Y+1 proves the exact identity

```
Y=M_r(X)/2.                                           (1)
```

## 2. Four terms suffice at an arbitrary even radix

Because X=qw and q is even, for every j>=4 the integer X^j is divisible by2q³: already q⁴/(2q³)=q/2 is an integer. Equation(1) therefore gives

```
q^3 | Y  iff
C_0+C_1 X+C_2 X^2+C_3 X^3 =0 mod2q^3.                 (2)
```

This is an exact arithmetic reformulation of the existing cubed-scale constraint. It is neither a new gate nor a claim that the four terms suffice for a full candidate zero. No population count or native AND decoder has been deduced at general even q. In particular parity does not supply dyadicness.

## 3. A non-dyadic scalar diagnostic

Take the diagnostic fixed ports, in source order,

```
(Bm1,Kconstant,twice_cell_bits,inner_bits,MC,MF)
=(15,28,8,1,14,19).
```

These are not asserted to arise from the valid machine compiler. Set

```
J=5, x=1, F=6, Z=29, alpha=32.
```

The literal outer definitions give

```
q=76, C=1, W=−28, u=9,
R=30562815, r=15281407, R=3 mod4,
3q+1<R, R+2<q^4.
```

Put `X=2^R−540`. The identity X−W=2^R−2^u holds exactly. Fresh modular exponentiation gives

```
X=4028 mod5700, 5700=q(q−1),
q|X, w=X/q=53 mod75.
```

Therefore `transport_quotient=(w+97)/75` is a positive integer, and the source transport factor is exactly

```
(28+w)C+q−F−75*transport_quotient=1.
```

Define M=M_r(X), Y=M/2. Since q³=2⁶·19³, equation(2) uses modulus2⁷·19³. The factorial valuation formula gives the following exact values; no enormous binomial coefficient needs to be materialized.

| j | 0 | 1 | 2 | 3 |
|---|---|---|---|---|
| v2(C_j) |16|8|9|8|
| v19(C_j) |3|3|3|3|

All four coefficients themselves are divisible by2q³. All remaining terms are too, by X being a multiple of the even q. Thus Y is a positive multiple of q³, and `s=Y/q³` is a positive integer.

This scalar tuple deliberately does not satisfy the native binary-mask conditions: `(Z−1) AND (MC*J+1)=4` and `F AND ((MF−15)*J−1)=2`. At this non-dyadic q the ordinary binary mask interpretation has not been justified. These failed checks are retained, not presented as a decoding defect for a valid program.

## 4. All18 positive witnesses, parametrically

For clarity, define Pell polynomials by `chi_T(0)=1,chi_T(1)=T`, `psi_T(0)=0,psi_T(1)=1`, both with recurrence `z_(j+2)=2T z_(j+1)−z_j`. At the X,Y above set

```
a=Y(X+1), A=a+2, Delta=A^2−1, H=4a+3, E=XY,
P=2XY^2+1, n=(R+1)/2,
c=psi_A(R), D=chi_A(R),
k=2psi_P(n), tau_root=chi_P(n),
eta=c−kY, zeta=k(Y+1)−c, h=(k−R−1)/E.
```

The strict sandwich is available for this constructed pair as well. Since X>2^(R−1), xi=M+theta with0<theta<1/2. We have xi<3Y and a>8r, so the elementary Pell estimates give

```
Y<c/k<(xi/2)(1+8r/a)
       <Y+1/4+12r/(X+1)<Y+1.
```

Thus eta,zeta are positive integers with k=eta+zeta and c=kY+eta. Modulo E, P=1, so `k=2n=R+1 modE`; Pell growth gives k>R+1 and hence h>0. The first norm and normalized main norm are both+1.

The input and shared witnesses are

```
kappa=psi_A(9), mu=chi_A(9),
delta=(kappa−9)/Delta,
U=E_9+28,
sigma=(E_R−E_9−X−28)/H
     =((E_R−2^R)−(E_9−512))/H.
```

The odd-index residue `psi_A(9)=9 modDelta` and strict growth make delta a positive integer. The recurrence gives `E_j=2^j modH`. The increasing excess E_j−2^j for j>=2 proves sigma is positive and integral. U is visibly positive. The literal roots are

```
a*kappa+W+U=mu,
a*c+X+U+sigma*H=D.
```

Here `U=540 modH` with0<540<H. Hence H does not divide U and the same-coordinate inverse to complete84 is unavailable. The common offset is e=−540.

Finally use the same general Pell completion as the accepted shared83 scalar construction:

```
m=2cR, f=chi_A(m), i=psi_A(m)/c^2,
S=Delta*psi_A(m), y_aux=psi_S(R), V=chi_S(R)/S,
auxiliary_quotient=T=(V+c+R*f^2)/(c*f).
```

The multiple-index expansion proves c² divides psi_A(2cR), so i is a positive integer and S=Delta*i*c². Since R is odd, V is integral. As r is odd, the polynomial `chi_S(2r+1)/S=C_r(S²)` has `C_r(0)=−R` and `C_r(−Delta)=−psi_A(R)=−c`. Using `S²=Delta*(f²−1)` gives

```
V=−R modc, V=−c modf, f²=1 modc, gcd(c,f)=1.
```

Consequently cf divides V+c+Rf², and T is a positive integer. These equations establish the strong and auxiliary normalized norms+1 and the exact auxiliary quotient producer. Together with the first, main, input, index and transport factors, all seven normalized factors equal+1. The actual source output is Delta times their product minus Delta, so it vanishes.

The18 supplied witnesses are exactly J,F,alpha,transport_quotient,f,h,i,T,s,w,tau_root,eta,zeta,y_aux,Z,delta,U,sigma. The construction proves their positive integral existence; the fresh code does not materialize Y, a Pell root or this enormous tuple. No extra witness or uncharged producer is proposed for the circuit.

## 5. Evidence and remaining scope

The companion helper authenticates four frozen files as inert bytes, checks the83-row source ordering/count and nine literal interface producers, and independently verifies the factorial-valuation formula against small direct binomials. It checks full half-binomial sums against their four-term truncations for small even q,r,w and recomputes the diagnostic outer data and residues. Its JSON gives exact counts and hashes. No predecessor program or source DAG is executed or imported. Fresh normal and optimized-Python receipt comparisons are performed before this packet is frozen.

Mathematical dependencies read are the whole `complete83_shared_projection_math.md` and its independent proof review, the unchanged source receipt, and the first/main quantitative estimates of `pell_kernel_half_binomial42.md` §5. The prior normalized Pell classification, fixed-minus rank theorem and compiler pretyping bounds remain explicitly inherited from the accepted offset proof, not newly certified here. The fresh valuation/truncation checks corroborate the elementary proofs; they do not test a valid machine's acceptance language.

For valid compiler slices the odd-q sector is excluded, and equation(2) is now available at every remaining zero. Whether a nonzero offset can occur for a valid rejected input, or whether another sound inverse exists, remains open. The separate dyadic-negative-offset result uses full fixed-layout mask hypotheses unavailable to this scalar diagnostic. Neither this note nor that conditional result establishes universal83.
