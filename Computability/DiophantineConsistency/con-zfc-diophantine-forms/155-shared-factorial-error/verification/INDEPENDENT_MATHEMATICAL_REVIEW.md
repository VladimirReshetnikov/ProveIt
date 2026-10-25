# Independent review: signed odd radix and a shared nearest-factorial bound

Prepared 25 October 2026 by a separate AI research agent for this packet.
This is an ordinary mathematical audit of the new lemmas and their dependency
order. It is not an external human review, a new proof-assistant theorem, or
an independent regeneration of the complete polynomial artifact.

## 1. Final construction reviewed

Retain the parent's signed Pell frame, including **all** of its paired
abscissa and ordinate orientation constraints. Retain its eleven normalized
binomial remainders and their common-denominator ratio equations. Replace
the initial factorial remainder/slack sign guards by a twelfth component in
the existing shared radius. Restrict the radix by the affine equation

```
q=2z+1,                         z in Z.
```

In particular q is initially odd and nonzero; it is not initially assumed
positive. Keep the parent's beta spacing **unchanged**:

```
y=V(V-1),                       V=(F^2+1)^t,
t=16+h0^2.
```

With M the existing output coordinate eventually identified as q^x, add
integer coordinates v_B,S and equations

```
B v_B=M,
MF=v_B V+S,
M^2=1+4(S^2+sum_{i=1}^{11} R_i^2)+G(a,b,c),
G(a,b,c)=a^2+b^2+c(c+1).
```

All these rows are quadratic in the literal coordinates. The old eleven
digit rows and their three shared ratio equations are unchanged, except for the existing affine
coordinate transformations. No inequality or variable exponent is an extra
primitive in the final polynomial.

Soundness uses G>=0 on integers. Completeness uses the inherited fact that
G represents every nonnegative integer.

## 2. Signed shared-radius cancellation

The radius implies M!=0 and 2|S|<|M|. Thus B and v_B are nonzero. The two
bilinear equations imply exactly

```
S=v_B(BF-V).
```

Therefore S/v_B is the integer BF-V. Cancellation gives

```
|BF-V|<|B|/2,                   |F-V/B|<1/2.          (1)
```

No sign of B,M,F,v_B,S was assumed. For each old ratio L_i v_i=M, the
same calculation gives |r_i|<|L_i|/2, where r_i=R_i/v_i is integral.
The absolute values on initially signed denominators are essential.

## 3. Unit-base power lemma for every signed index

The retained frame orients the canonical Pell coordinates at every signed
requested index before semantic power interpretation. Let epsilon be +1 or
-1, and put

```
f_j=X_j(A)+(epsilon-A)Y_j(A),
T=2A epsilon-2.
```

The initial values are f_0=1 and f_1=epsilon, and the two-sided recurrence is
f_(j+1)=2A f_j-f_(j-1). Modulo T one has 2A=2epsilon. Forward and backward
induction give

```
f_j=epsilon^j (mod T)             for every j in Z.
```

The oriented power residue therefore gives m=epsilon^j mod T. The retained
square-frame bounds imply |m-epsilon^j|<|T|, so

```
m=epsilon^j,                     |m|=1.              (2)
```

This proof includes negative indices. It uses both-coordinate orientation;
no principal abscissa constraint is deleted.

For completeness, the signed-base lemma at |n|>=2 is also valid. The same
modulus T=2An-n^2-1 dominates the absolute power error. A negative requested
index -j would yield m n^j=1 as an exact equality, impossible for integral m
and j>=1. Thus such a request forces a nonnegative index and its exact
power output. The size estimate must use |n|; negative bases are permitted.

## 4. Acyclic recovery before factorial meaning

The following ordering has no circular sign premise.

1. Apply the unchanged signed-anchor/cap and both-coordinate orientation
   proof. Its large frame consists of squares of signed atoms, so it does
   not presuppose positivity of q,B,F,x or the actual CRT representatives.
2. The known t>=16 request at base F^2+1>=1 gives V=(F^2+1)^t>=1. When
   F=0, the unit-base conclusion gives V=1. Equation (1) is now available.
3. Exclude q=+1 and q=-1. Equation (2) applied to the request with output M
   gives |M|=1. The radius then forces S=0. Since B v_B=M, |B|=1; since
   S=v_B(BF-V), BF=V. Hence |F|=V=(F^2+1)^t>|F|, a contradiction.
   The literal oddness now yields |q|>=3.
4. Requests at base q force x>=0 and M=q^x. The retained ratio equation
   for the denominator q^(t+1) shows q^(t+1) divides M. Taking absolute
   values gives x>=t+1. This does not require q>0.
5. Because |q+1|>=2, requests at q+1 force all actual independent CRT
   representatives to be nonnegative, even if q+1<0. Thus
   H=1+sum representatives>=1. No sign of their power outputs is needed.
6. Equation (1) implies |B|>=2, as proved below. Consequently |BH|>=2,
   and the retained request at BH gives

   ```
   q=(BH)^x,                     |q|>=|B|^(t+1).      (3)
   ```

Here is the estimate used in step 6. If F=0, (1) gives |B|>2V=2, so
|B|>=3. If F!=0, BF must be positive: otherwise |BF-V|>=|B|+V>|B|/2.
Thus V<|B|(|F|+1/2). Were |B|<=|F|, this would contradict
(F^2+1)^t>F^2+|F|/2. Therefore |B|>|F|>=1. Integrality strengthens this
to

```
V<|B|(|B|-1/2)<|B|^2.                                (4)
```

The order above does not yet use y>0, F=t!, positivity of q, or the sign of
any deleted remainder. The old spacing only gives y>=0 at this stage.

## 5. Exact factorial digits in signed radix

Put Q=|q|. The binomial theorem is valid for either sign of q:

```
(q+1)^(F^2+t)=sum_j C_j q^j,
C_j=binom(F^2+t,j)>=0.
```

Its low polynomial r_true=sum_(j=0)^(t-1) C_j q^j is a signed integer.
If C_max bounds these coefficients, then

```
|r_true| <= C_max sum_(j=0)^(t-1) Q^j
         < C_max Q^t/(Q-1).                          (5)
```

For F!=0, the inherited elementary coefficient lemma gives C_max<=V,
including the coefficient C_t. By (3)--(4), V<|B|^2 and
Q>=|B|^(t+1), so (5) is smaller than Q^t/2.

The F=0 case is separate. Here C_j=binom(t,j)<=2^t and |B|>=3. Thus
Q>=3^(t+1), and 2^t/(3^(t+1)-1)<1/2. Again |r_true|<Q^t/2. For t>=16
one could strengthen this to 1/32, but soundness needs only one half.

The normalized remainder reconstructs an integer r with |r|<Q^t/2.
It is congruent to r_true modulo the possibly negative integer q^t.
Their difference is a multiple of q^t of absolute value below Q^t, so
r=r_true. This is centered-residue uniqueness, not least-nonnegative
remainder interpretation at a negative radix.

Dividing the exact factorial digit row by q^t now yields

```
B=C_t (mod q).
```

If F!=0, (3)--(4) give |B-C_t|<=|B|+C_t<Q, hence B=C_t>0.
If F=0, C_t=1 and |B|+1<Q likewise force B=1, contradicting |B|>=3.
Thus F!=0, and the positive B together with (1) gives F>=1.

Only now recover positive radix: B>0, H>=1 and x>=t+1 imply from (3)
that q=(BH)^x>0. Every later range digit can use the parent's ordinary
positive-radix proof unchanged.

Also V>=2 and y=V(V-1)>=1. The last endpoint

```
x=1+[1+(t+1)y]u_t
```

with x>=t+1>1 forces u_t>=1, so the parent's stronger amplification bound
x>=2+(t+1)y is available before the remaining range-digit interpretations.

## 6. Nearest-factorial fixed point

Let t>=16 and F>=1, and put T=t! and

```
R_t(F)=(F^2+1)^t/binom(F^2+t,t)
      =T product_(i=1)^t (F^2+1)/(F^2+i).
```

Assume |F-R_t(F)|<1/2, as provided by (1) and the exact binomial digit.
Each factor is positive, at most one and nondecreasing in F. Therefore

```
R_t(F)>=R_t(1)=2^t/(t+1)>t+1/2,
```

and F>t. Write a_i=(i-1)/(F^2+i). The finite product inequality
product(1-a_i)>=1-sum a_i gives

```
sum a_i < t(t-1)/(2F^2) < 1/2,
R_t(F)>T/2.
```

Since F>R_t(F)-1/2>T/2-1/2 and T/2 is an integer, F>=T/2. Applying
the product inequality once more,

```
0<=T-R_t(F)<=T sum a_i
             < T t(t-1)/(2F^2)
             <= 2t(t-1)/T < 1/2.
```

Thus |F-T|<1. Both F and T are integers, so F=T=t!.
This proves the required nearest-integer fixed point; the parent's ceiling
fixed-point theorem alone would not justify the new signed error.

For the canonical F=T the same estimate is much stronger:

```
0<=T-R_t(T)<t(t-1)/(2T)<1/32.                         (6)
```

After this identification, the deleted front signs can be recovered if
needed: r=BF-V>=0, r<B/2, and the complementary slack B-r-1>=0. Also
q-B-1>=0. These are conclusions of the proof, never early assumptions.

## 7. Canonical completeness and the twelve-component budget

Keep the parent's cofinal horizon, F=t!, exact B, unchanged y=V(V-1),
endpoint CRT, amplified representatives and private Pell witnesses. Its
canonical odd-square radix is already a positive odd integer. For the
weakened affine equation choose z=(q-1)/2. No fresh beta-spacing argument
is required because y was not modified.

Canonical B divides q and therefore divides M=q^x. Choose

```
v_B=M/B,                      S=v_B(BF-V).
```

Equation (6) gives |S|/M=F-V/B<1/32. The eleven inherited genuine
normalized digit remainders satisfy |R_i|<M/32. Therefore

```
4(S^2+sum R_i^2)<(48/1024)M^2<M^2.
```

The integer M^2-1-4(S^2+sum R_i^2) is nonnegative, so it has a G
representation. Every canonical refutation witness consequently extends
to the new radius and affine-radix constraints.

## 8. Verdict and scope

No arithmetic loophole was found in the signed shared-radius cancellation,
the two-sided unit-base lemma, the signed-radix factorial digit, the acyclic
bootstrap, or the nearest-factorial fixed point under the retained
interfaces. The two exceptional cases q=+/-1 and F=0 must remain explicit;
they are not covered by a casual appeal to positive-base power semantics.

This audit assumes the literal system retains the ratio for q^(t+1), the
same q^x common denominator, and **all** principal-pair abscissa orientation
constraints. It does not establish a numerical variable or monomial count;
those require exact checks of the emitted rows, affine projections and
collected quartic. It does not replace the inherited uniform Pell theorem,
CRT/range theorem, Horn-flow decoding, or C222-to-ZFC calibration.
The new arguments are ordinary finite arithmetic formalizable in ZFC.
