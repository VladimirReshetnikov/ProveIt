# Three modulus-four refinements

Use the domains, sixteen- and fifteen-coordinate lists, parent source, and
common abbreviations in `PROOF.md`, unchanged. In particular

```
d=c^4; Q=Delta(f^2-1); m=XY^2; B0=mk;
A=1+m(m+1)k^2; S=k(2m+1).
```

The guard alone supplies d>0, Delta>1, A>0, |k|>=2, |m|>1, S!=0 and
S^2>=4A. It excludes Q=1. These conclusions do not assume any omitted
root equation. In addition W=4(3w+1) is divisible by four, hence X=qW,
m=XY^2 and B0=mk are divisible by four. Consequently

`A=1 (mod 4)`.

Every rational square root of A is therefore an **odd integer**. This
residue fact gives the final one-gate reductions.

## 1. Sixteen variables: degree 112, 119 operations

Replace the two-root definitions of the original sixteen-variable form by

```
n=4n0+2; L=n+B0;
G=n^2+B0(2n-k)-1=L^2-A;
U=dG+Q; N2=U^2-4dL^2Q.
```

Keep its other three residuals A2, A5 and
`B4=(V+nu)^2-Q*nu*(2V+nu)-1`. The polynomial is their sum of squares
together with N2^2.

Since L=2 modulo four, it is nonzero. At a zero, define rational numbers

`u=U/(2dL), tau_old=L-u`.

The norm and the exact identity

`(2dL^2-U)^2-4d^2L^2*A=N2`

give d*u^2=Q and tau_old^2=A. Thus tau_old is an odd integer. Since L
is even, u=L-tau_old is an odd integer. Define r=(u-1)/2 and
tau=tau_old-B0. These are integers restoring the deleted strong and first
norms; the auxiliary row agrees because I^2=Q. This supplies a parent zero.

Conversely, at a parent zero let u=2r+1. Choose the sign of its private
first root tau_old so that `tau_old=u (mod 4)`. Both numbers are odd,
and negation exchanges the two odd residue classes, so the choice is always
available. Only the private first root is changed; every other parent row
is independent of it. Then

`n0=(u+tau_old-B0-2)/4`

is an integer, and L=u+tau_old makes the norm zero. The full factorization
under Q=d*u^2 and L=u+tau_old is

`N2=d^2*(tau_old^2-A)*((tau_old+2u)^2-A)`.

The exact weighted leader of N2 is d^2*m^2*k^4, at degree 56. The
complete final polynomial has degree 112, with coefficient

`[c^16 J^60 w^12 v^16 h^8] P16_mod4=2^40*3^72*beta^60>0`.

The literal evaluator uses 119 live binary operations.

## 2. Fifteen variables: degree 310, 136 operations

In the three-root formula use

```
n=4n0+2; L=n+B0+4SV; delta=Q-1; D=d*delta;
Aa=A*D; Bb=Q*delta; Cc=16S^2*d*(QV^2-1);
R3=D*L^2-Aa-Bb-Cc;
T3=R3^2-4(Aa*Bb+Aa*Cc+Bb*Cc);
N3=T3^2-64*Aa*Bb*Cc*D*L^2;
Gsum=A2^2+A5^2;
P15_mod4=Gsum+N3+Gsum*N3.
```

The positive integer 1+Gsum again shows that a zero is exactly
Gsum=N3=0. Since D!=0, the norm is D^4 times the classical three-root
norm with radicands

`A, Q/d, 16S^2*(QV^2-1)/(Q-1)`.

Here L=2 modulo four for every integer assignment.

If Q<0, exactly the middle radicand is negative and no signed sum is real.
If Q=0, a vanishing factor would give L=+/-sqrt(A)+/-4S. Square
integrality makes sqrt(A) odd, so L would be odd, a contradiction.
Q=1 is impossible. If Q>1 and V=0, exactly the final radicand is negative.

For Q>1 and |V|>=1, all radicands are positive, and the final one is
at least 16S^2>=64A>A. Hence the first and third roots cannot cancel.
The multiquadratic lemma in `PROOF.md` says that a nonzero rational root
sum has either all roots rational or two nonrational roots canceling with
the third rational. In the latter case:

* Cancellation of the middle and final roots leaves an integer root of A,
  which is odd and cannot equal the even L.
* Cancellation of the first and middle roots leaves 4S*y. Rational Pell
  descent makes y integral; the sum is divisible by four and cannot equal
  L=2 modulo four.

The first/final cancellation is excluded by strict size separation. Thus
all roots are rational. Write their signed sum as

`L=tau_old+u+4S*y`.

Then tau_old is an odd integer and y is an integer by the inherited
adjacent-coefficient Pell descent. Therefore u=L-tau_old-4S*y is an odd
integer. It satisfies d*u^2=Q. Reconstruct

`r=(u-1)/2; tau=tau_old-B0; nu=y-V`.

All five parent residuals vanish.

For completeness choose the sign of the first parent root to match u
modulo four, just as in Section 1. Set

`n0=(u+tau_old-B0-2)/4+S*nu`.

This is integral and gives the desired signed sum, so the norm vanishes.

The generic norm has exactly 3,151 terms. With weights
m:10,k:7,V:7,Q:14,d:4,n:1, its degree is 222 and its unique leading
monomial is `2^22*m^8*k^8*V^6*Q^2*d^4`. The final degree is 310 and
the actual fixed-slice coefficient is

`[c^16 J^184 w^28 v^44 h^16 z^6 f^16] P15_mod4`
`=2^122*3^212*beta^184>0`.

The literal evaluator uses 136 live binary operations.

## 3. Centered fifteen variables: degree 306, 139 operations

Replace n=4n0+2 by

`n=4*(n0-h*Y*R)+2`.

This is an invertible integral coordinate shear preserving n modulo four.
The soundness proof is unchanged. Add hYR to the completeness value of n0
in Section 2.

The separate independent exact expansion in
`independent_degree/audit_mod4.py` checks all 61,557 terms of the inner
polynomial T3 on atoms X,Y,R,h,f,c,T,n0 of weights 2,4,5,1,1,1,1,1.
Its degree is 109 and its complete leading form is

`2048 X^9 Y^13 R^3 h^3 f^6 c^8 [R f^2+hY(X-2f^2)]`.

The subtracted triple tail has degree at most 212. Thus N3 has degree
218 and the final unit-product polynomial has degree 306. The nonzero
actual coefficient is

`[J^184 w^26 v^42 z^8 h^14 f^16 c^16] P15_mod4_centered`
`=2^116*3^210*beta^184>0`.

The literal evaluator uses 139 live binary operations. The original
odd-sum forms are retained unchanged as reference constructions. These
counts and degrees are explicit achievements, not optimality claims.
