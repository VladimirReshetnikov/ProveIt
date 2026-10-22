# Cross-package ordinary strong-root compression

Source snapshot: `3b201cdea32d2c816f5f3d20734051f25fd3ef14`.

The construction combines package 06's raw-K215 blank coefficient recipe and
15-coordinate scale, package 02's ordinary strong-root lemma, and package 08's
quadratic register elimination. It keeps package 06's four fixed integer ports
`Bm1,Kconstant,MC,MF`; in particular `MF` is the shifted coefficient. It does
not substitute the numerical constants of package 02 or package 08.

## Results

| Form | Positive coordinates | Equations | Exact degree / max residual degree | Binary operations |
|---|---:|---:|---:|---:|
| ordinary blank system | 15 | 6 | 28 | 61 = 34M + 27A |
| ordinary product | 15 | 1 | 99 | 69 = 39M + 30A |
| ordinary sum of squares | 15 | 1 | 56 | 78 = 40M + 38A |
| quadratic ordinary lift | 33 | 24 | 2 | not compared |
| quartic ordinary lift | 33 | 1 | 4 | not compared |

This improves the prior 16-coordinate, 7-equation, degree-28, 63-operation
system in all size counts except its unchanged degree. It also gives a better
low-degree tradeoff than the prior 15-coordinate SOS (degree 92 at 79 ops),
and removes one coordinate and one equation from package 08's 34/25 quadratic
lift. The 69-operation polynomial does not beat the prior 67-operation count;
it improves its degree from155 to99.

## Formulas

All fifteen coordinates
`J,F,alpha,z,f,h,i,T,s,w,tau,eta,zeta,y,gamma` are positive.
Write beta=B-1 and use package06's K, MC, MFsrc. Set

```
q = beta J + 1,              C = q-F-alpha,
X = wq,                     Y = sq^3,               E = XY,
k = eta+zeta,               c = kY+eta,             a = E+Y,
H = 4a+3,                   Delta = a^2+H,          D = X+ac+gamma H,
G = (q-1)(q-F)+alpha,
R = G(q^2-1)+(MC+q MFsrc)J,
L = E kY,                   V = c(Tf-1)-Rf^2,
I = i c^2,                  A0 = Delta(f^2-1).
```

The six equations are

```
N0 = tau^2-L(L+k) = 1,
N1 = D^2-Delta c^2 = 1,
Na = A0(V^2-y^2)+y^2 = 1,
Nk = k-hE-R = 1,
Nt = (K+w)C+(q-F)-z(q-1) = 1,
I^2 = A0.
```

The polynomial is

```
N0 N1 Na Nk Nt [1+I^2-A0] - 1 = 0.
```

It has the same *existence* predicate as package06's normalized-strong
polynomial. No equality of full tuples with identical i is asserted. Its
product and its six-equation presentation have the same positive zeros.

## Proof of product/system equivalence and soundness

At a product zero all six factors are integer units. Delta is0 or3 modulo4.
A0=Delta(f^2-1) is therefore0 or1 modulo4, regardless of the supplied f.
Consequently 1+I^2-A0 cannot be-1 modulo4, and is1. The same residue argument
makes Na=1. The negative Pell descent makes N0=1, and Delta modulo4 makes
N1=1. Let Nk=epsilon, Nt=nu, where epsilon,nu are signs and epsilon nu=1.
The ordinary strong equality I^2=A0 is now known.

As in package06, Nt being a unit gives C>=0, not C>0. In particular
q-F=C+alpha>0. With the authentic raw-K215 masks one has

```
q(q^2-1) < R < q^4-q^3+q^2-1 < q^4-2,
E >= q^4 > R+2,          a>R+2,          q>=16.
```

Thus the bootstrap from package02 applies using package06's weaker upper
bound. Write A=a+2, P0=2XY^2+1. From N0=1 and N1=1 there are positive
indices n,p with

```
k=2 psi_P0(n), c=psi_A(p), D=chi_A(p).
```

Since P0=1 moduloE, 2n=R+epsilon moduloE, so n>=(R-1)/2>=24.
Since P0>A and c>k, monotonicity gives p>n. Thus

```
c>A Delta^2,          c>2p,          c>2R.
```

For the last inequality use h>=1, k=R+epsilon+hE, and c>kY; this avoids any
assumption about the auxiliary variable V.

The ordinary strong equation now yields

```
f^2=1+i^2 c^4/Delta,
f>c^2/sqrt(Delta)>c^2/A>2c,
f^2>Delta+c.
```

Together with R<a<Delta this gives

```
A0-(Rf^2+c)=(Delta-R)f^2-Delta-c>0.
```

Na=1 is A0 V^2-(A0-1)y^2=1. It excludes V=0; for |V|>1 it implies
|V|>=2A0-1. But T>0 gives V>-Rf^2-c>-A0, so V cannot be negative except
possibly -1. Both +/-1 are excluded by V=-c modulof and 2<c<f/2.
Therefore V>1.

Apply the generic ordinary strong-rank lemma, *with i itself* as its ordinary
coefficient. Its hypotheses are the main Pell equation, c>A Delta^2,
and (i c^2)^2=Delta(f^2-1). It yields

```
f=chi_A(m),          p|m,          c|m,          m>=c>2p,
i c^2=Delta psi_A(m).
```

In particular

```
f^2-1=Delta psi_A(m)^2=i c^2 psi_A(m),
```

so c^2 divides f^2-1. This divisibility must not be inferred just by cancelling
Delta in the original strong equation.

Define integers

```
o=cT-Rf,          j=Tf-1-R(f^2-1)/c.
```

Then of=V+c>0 and jc=V+R>0, so o,j>0 and V=of-c=jc-R. The inherited signed
auxiliary step-down lemma now gives p=R. Its hypotheses only require
0<p,R<c/2 and the rank conclusions above.

Writing 2n=R+epsilon+vE, v>=0, the bound E>R+2 rules out v>=1 because n<p=R.
If epsilon=-1, then p=2n+1, and the standard duplication comparison gives
c>k(Y+1), contradicting c=kY+eta with 0<eta<k. Hence epsilon=nu=1.
Now Nt=1 excludes C=0, so C>0. All six displayed equations hold.

The remaining power recovery and native blank-tableau decoding are exactly
package06's arguments: the strict Pell ratio gives X=2^R; q|X gives q a
power of2; q=beta J+1 gives q=B^N; rescaling X/q^3 restores the symmetric
kernel. The first shifted mask produces Start with no End, and the raw-K215
window compiler supplies the blank halting computation. This uses the same
ordinary mathematical compiler lemmas as the prior packages; it is not a
new Lean/Rocq formalization.

Conversely, given a normalized-strong package06 zero, replace

```
i_ordinary = Delta i_normalized.
```

Then (i_ordinary c^2)^2=Delta(f^2-1); the auxiliary coefficient is unchanged
on the zero, all other coordinates are retained, and the six equations hold.
Together with the prior completeness theorem this proves equivalence of
existence predicates, and hence the desired ZFC equivalence.

## Literal ledger and exact degrees

In package06 system61 replace the four gates

```
aux_coefficient_root=i*(Delta*c^2),
R16=aux_coefficient_root^2,
scaled_f_square=Delta*f^2,
norm_strong=scaled_f_square-R16
```

by four gates

```
f2_minus_one=f^2-1,
R16=Delta*f2_minus_one,
ordinary_ic2=i*c^2,
ordinary_ic2_square=ordinary_ic2^2.
```

Compare ordinary_ic2_square=R16. The replacement has the identical cost,
3M+1A, and keeps every port and gate live. It gives61=34M+27A gates.
Adding ordinary_unit=1+ordinary_ic2_square-R16 and the six-factor product
minus1 adds2A+5M+1A, for69=39M+30A. The six-residual SOS adds6M+11A,
for78=40M+38A.

Let Q=beta J, k0=eta+zeta, C1=Q-F-alpha. Exact factor degrees are
22,18,28,7,2,22. The product's leading homogeneous form is

```
8 Q^55 h gamma i^2 k0^9 w^7 s^16 T^2 f^4 (w C1-zQ).
```

The monomial J^56 h gamma i^2 eta^9 w^7 s^16 T^2 f^4 z has coefficient
-8 beta^56, nonzero for every valid compiler. Thus the degree is exactly99.
The auxiliary residual alone has degree28, so the SOS has exact degree56.

## Quadratic33 lift

Start from package08's 34-variable, 25-equation register list. Delete the
register K and merge its two main-norm equations into

```
D^2 = Delta C2 +1.
```

Replace I=iK by I=iC2. Keep all other register definitions and equations,
including Baux=I^2=Delta(F2-1). This is exactly the ordinary strong equation.
There are33 positive unknowns and24 equations, all quadratic; their complete
expanded residuals are in blank_ordinary_quartic33.json.

The positive inverse lift is the same as package08 except I=ic^2 and there
is no K. All registers remain positive. Specifically V0=Tf-1>0,
V>1, Baux=I^2>1, and g=y^2-V^2>0 follow from the proof above.
The sum of residual squares has exact degree4 (tau^4 occurs with coefficient1).
Replacing each positive unknown v by n_v+1 gives33 natural-number unknowns.
This lift may use package06's raw-K215 constants because its elimination is
algebraic; one must not silently use package08's different constants.
