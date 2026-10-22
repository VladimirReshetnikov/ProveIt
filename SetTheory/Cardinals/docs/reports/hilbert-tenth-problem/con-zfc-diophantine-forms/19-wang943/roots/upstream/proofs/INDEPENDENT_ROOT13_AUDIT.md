# Independent audit of the weighted13-variable construction

This note first derives its formulas for the inherited four-port arithmetic interface of `06-blank67`; references below to that package's exact coefficients describe this initial derivation. The accompanying report proves transfer to the new four-site recipe, with the final default binding in `../COEFFICIENT_BINDINGS.json` selecting the package-root recipe `compiler/tshape_constants.json` and its shifted MF mask.

Audit scope: the elimination algebra, coefficient nonvanishing, unit
guards, root integrality, signed auxiliary issue, and transfer to the
inputless compiler. The arithmetic ledgers are checked independently
by the arithmetic agent; this note does not duplicate those builds.

## 1. Notation and exact algebra

Use the common inputless expressions q,X,Y,E,k,c,a,Delta,C_word,R.
The remaining positive variables are

```
J,F,alpha,z,h,i,T,s,w,eta,zeta,gamma,t.
```

Write the new abbreviations with a different letter for each root:

```
A = 1+Lfirst(Lfirst+k), Lfirst=E(kY),
D = 1+Delta i^2 c^4,
Q = Delta(D-1)=(Delta i c^2)^2,
v = cT, z0=c+RD, d=Q-1,
e = Q(Dv^2+z0^2)-1,
b = 2Qvz0,
M = D+v^2,
C = d(t^2+M^2 A)-e,
U = C^2+b^2D-4d^2t^2M^2A,
Res = U^2-4C^2b^2D.
```

The weighted expression C is distinct from the packed word C_word.

Suppose temporarily that f^2=D, tau^2=A and
`d y^2=e-bf`. Set t=M tau+y. Expanding gives

```
C+bf=2dtM tau,
U+2Cbf=0,
Res=0.
```

Conversely, if C,b,d,t,M are nonzero and Res=0, put

```
f=-U/(2Cb),       tau=(C+bf)/(2dtM),       y=t-M tau.
```

Then f^2=D and tau^2=A by the defining identities. A rational whose
square is an integer is an integer: reduce the fraction to lowest
terms and its denominator squared divides its numerator squared.
Thus f and tau are integers, and y is an integer. Rearranging the
unsquared identity gives

```
d y^2=e-bf=Q(vf-z0)^2-1.
```

This is the exact auxiliary norm with V=vf-z0. There is no appeal
to an approximate square root or a rational-to-integer assumption.

## 2. The dangerous coefficient-zero cases are excluded

For the four-equation system, the main, index and transport factors
are individually1. For the product construction they are units,
as analyzed in §3. In either case let Nk=epsilon and Nt=nu, with
epsilon,nu in {-1,1}.

The inputless weak transport bound forces C_word>=0. The exact
shifted-mask bounds of package06 then give

```
q>=16, 0<R<E-2, E>=q^4, k=R+epsilon+hE>R.
```

This argument does not use the first Pell norm: that root has not yet
been recovered. Since eta,zeta>0,
`c<k(Y+1)` and Y>=1. With X>=16,

```
A > k^2 X^2 Y^4 > 8 k^2((Y+1)^2+1) > 8(c^2+R^2).
```

For example `(Y+1)^2+1<=5Y^2`, while X^2Y^4>=256Y^2, so the
middle inequality is strict even under the much weaker Y>=1.

Now D>1, Q>1 and d>0. Since v=cT>0 and z0=c+RD>0, b>0.
The chosen weight satisfies

```
M^2 >= 4Dv^2,       M^2 >= D^2,
z0^2 <= 2D^2(c^2+R^2).
```

Therefore

```
2(Dv^2+z0^2)
 <= M^2(1/2+4(c^2+R^2))
 < M^2 A.
```

As Q>=2, d=Q-1>=Q/2. Hence

```
d M^2 A > Q(Dv^2+z0^2)=e+1,
C=d(t^2+M^2A)-e > d t^2+1 > 0.
```

Every reconstruction denominator in §1 is consequently nonzero.
This closes the usual exceptional branch in an iterated quadratic
resultant; no unproved generic nonvanishing assumption remains.

## 3. Product guard

For the single polynomial

```
Nmain Nk Nt (1+Res)-1=0,
```

every factor is a unit. Since Delta=0 or3 modulo4, the main norm
cannot be -1. Since Res=U^2 modulo4, `1+Res` is1 or2 modulo4,
so it cannot be -1 either. Thus Nmain=1, Res=0 and Nk Nt=1;
the index/transport units have a common sign.

The bounds in §2 hold for both signs and include the C_word=0
boundary. It is not legitimate to assert C_word>0 before recovering
the index sign. After root reconstruction the signed index argument
in §4 gives Nk=Nt=1 and then excludes C_word=0.

## 4. Signed recovered f: required correction to a naive parent invocation

The recovered f need not be positive solely from the quadratic
elimination formula. Neither the fact f^2=D nor the resultant itself
permits calling the positive15-variable parent theorem unchanged.
The following signed proof is enough and avoids that error.

The reconstructed first norm gives tau^2=A>1; use |tau|. The
auxiliary norm with Q>1 excludes y=0 and V=0; use |y|.
Since D>1, f is nonzero. If f<0, replace f by -f and T by -T.
The source depends on these two coordinates only through f^2 and Tf,
so this leaves all computed quantities unchanged. We now have f>0
and an arbitrary signed T.

The first/main norms and weak index equation give

```
k=2 psi_P(n), c=psi_A0(p), Dmain=chi_A0(p),
P=2XY^2+1, A0=a+2,
p>n>=(R-1)/2>=24, c>2p, c>2R.
```

The normalized strong equation is
`f^2-Delta(ic^2)^2=1`. It gives
`f=chi_A0(m), psi_A0(m)=ic^2`.
Strong divisibility gives p|m; expanding the Pell unit at indexp
modulo c^2 gives c|(m/p). Thus c|m and m>2p.

Put S=Delta i c^2, so Q=S^2. The auxiliary norm classifies the
absolute root `|SV|=chi_S(ell)` at an odd ell. Write ell=2u+1 and
V=sign(V) Q_u(S^2). The source congruences remain

```
V=-c modulo f,       V=-R modulo c.
```

Using Q_u(-Delta)=(-1)^u psi_A0(ell), square the first congruence.
The signed chi step-down gives ell=plus or minus p modulo m,
hence modulo c. The second congruence gives R=plus or minus p
modulo c. Since 0<p,R<c/2, p=R.

Now 2n=R+epsilon+uE with u>=0. The bound E>R+2 excludes u>=1.
If epsilon=-1, then p=2n+1, and Pell duplication gives
`c>Ak>k(Y+1)`, contradicting the literal ratio interval.
Thus epsilon=nu=1, 2n=R+1 and C_word>0.

The power and exact half-binomial extraction arguments depend only
on the now odd R, main-root projection, and strict ratio. They do
not inspect T or V. Sections2-4 of the signed-quotient scout spell
out these estimates; substitute the inputless C_word for its Z and
omit its input bridge. They recover X=2^R, q=B^N, the population
threshold, and the native masks. The remaining transport/window
argument is exactly the raw blank compiler of package06 and gives
a blank halting K215 run.

This direct exterior decoding is sufficient. One may additionally
adapt the scout's two-congruence parity argument to prove T>0, but
that stronger statement is unnecessary here. In particular, the
ordinary-input complete84 theorem is not being applied wholesale
to different inputless constants.

## 5. Completeness and conclusion

Given any positive normalized15-variable solution of package06,
choose t=M tau+y. All remaining13 coordinates are positive and
the identities in §1 give Res=0. The main, index and transport
equations are unchanged. This proves completeness directly.

Together with §§1-4, both the four-equation and product constructions
have a positive solution exactly when K215 halts blank. Their ZFC
consistency equivalence uses the same machine calibration and
formalizability argument as the source packages. The audit finds no
remaining algebraic or sign gap in this construction, conditional
on the retained native compiler and Pell lemmas.

This is an independent mathematical review, not a new formal
certificate, a proof of consistency, or a global minimality claim.

