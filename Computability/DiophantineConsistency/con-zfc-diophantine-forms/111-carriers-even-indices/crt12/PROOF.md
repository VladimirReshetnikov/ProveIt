# A mixed-modulus carrier for twelve integer unknowns

## Result and source boundary

All twelve coordinates `j,C,z,h,r,v,w,T,c,n,t,s` are unrestricted integers.
The complete supplied arithmetic DAGs define integer polynomials:

| File | Degree | Live binary operations |
|---|---:|---:|
| rational.json | 768 | 161 |
| integral.json | 784 | 154 |

The words rational and integral describe an auxiliary norm presentation;
**both final equations are ordinary division-free integer polynomials**.
The complete six fixed coefficient payloads are the unchanged source34
tuple, copied from the scalar-carrier12 candidate at ProveIt commit
`84e16e43092614bae262ca59651cb9d77e31a255`. In particular
`beta=2^1064921-1`, `cone_A=2^1113`, `cone_B=2^666104`, and MF is the
already shifted coefficient. The other three integers are supplied in
full, not replaced by a universal index or an unspecified constant.

This proof establishes equivalence to the same signed native source and
finite-refutation endpoint as that pinned parent. The inherited ordinary
source theorem, its Pell/CRT lemmas and its controller calibration are
explicit dependencies, retained under `source/`. No new Lean or Rocq
derivation, no assertion of consistency, and no global optimality theorem
is claimed. Composing the new reduction with that ordinary source theorem
gives the ZFC-provable equivalence between no integer zero and Con(ZFC).

## 1. Complete polynomial definitions

Use the following abbreviations; none is an additional quantified variable.

```
J=6j+1, q=beta J+1, W=12w+4, X=qW, Y=qv,
a=(X+1)Y, H=4a+3, Delta=a^2+H=(a+2)^2-1,
F=(K0+W)C-z(q-1),
R=(q(q-F)-C)(q^2-1)+(MC+q MF)J,
k=R+1+hXY, eta=c-Yk, zeta=k-eta,
G=(cone_A F)(cone_B C)-(q-cone_A F-cone_B C)^2,
Peta=eta zeta,
Pair=G Peta-(t^2-G-Peta+1)^2,
Dg=(3Pair-4)s^2+1,
I=sr c^2, Df=1+Delta I^2, Q=Delta^2 I^2, delta=Q-1,
V=Df(c-R+4IT)-c, Cy=QV^2-1,
ell=XY^2, Dt=1+ell(ell+1)k^2,
Kstar=X(2X-3c)-2,
M=2q^2, D=MH,
Ccarrier=M Kstar+H(v-q^2),
zc=D T+Ccarrier,
Ac=(zc^2+3D^2)(zc^3-19D^3),
S=sr M^5 H.
```

Let

```
N4(x;a,b,e,d)=product over eps in {+1,-1}^4
                 (x-eps1 sqrt(a)-eps2 sqrt(b)-eps3 sqrt(e)-eps4 sqrt(d)).
```

Changing the sign of one formal square root permutes the factors. Thus
this product is an integer polynomial in its five displayed arguments.
It has degree16 in x and degree8 in each radicand. Define

```
P768=delta^8 N4(S(n+V)-Ac;
                   9S^2 Df,81S^2 Dt,729S^2 Dg,S^2 Cy/delta),
P784=N4(S(n+delta V)-Ac;
                   9S^2 Df,81S^2 Dt,729S^2 Dg,S^2 delta Cy).
```

The apparent denominator in P768 cancels on expansion because the degree
in the fourth radicand is eight. Both literal files use only integer
leaves, the twelve variable leaves, the six fixed coefficient leaves,
addition, subtraction and multiplication. Section8 supplies a small
division-free evaluator and independently verified exact degrees.

## 2. The carrier and the inherited arithmetic interfaces

Put `pi(u)=(u^2+3)(u^3-19)` and
`Phi_D(z)=D^5 pi(z/D)=z^5+3D^2z^3-19D^3z^2-57D^5`.
The retained `PRIME_TWELVE.md` proves that pi has a root modulo every
positive integer. It has no rational root: its quadratic factor is
strictly positive on the reals and 19 is not a rational cube. These are
different properties, both used below. The exceptional primes2,3,19
are covered in that retained proof; no assertion about only almost all
primes is being substituted for intersectivity.

The same source supplies the prime-order radical-separation lemma,
adjacent-coefficient Pell descent, signed main-root folding, the source
ratio and rank bounds, and full residue-class interpolation of T **after
one strong pair I,f has been fixed**. Precisely the interpolation form
used here says that from canonical outer data and a selected nonzero
guard witness s one can choose a strong pair with `4sc^2|I`, and then,
for every residue class modulo I, choose T in that class satisfying
the auxiliary Pell equation with `V=Df(c-R+4IT)-c`. Its proof uses
a squared-modulus period and generalized CRT, and is retained as
`INTERPOLATION12.md`. These interfaces are unchanged by the new carrier.

## 3. Uniform facts before any equation is imposed

The actual beta is odd and is1 modulo3. Thus q is even, q=2 modulo3,
and q is nonzero. Also W=4 modulo12, so `|X|>=4(beta-1)>2^36` and
X=-1 modulo3. Since Y=qv, either v=0 and a=0, or
`|a|=|qv(X+1)|>1000`. Consequently Delta>=3, H is nonzero and odd,
and Q is either zero or at least9. In particular delta never vanishes.

Because a is a multiple of q, H=3 modulo q. Since q=2 modulo3,
`gcd(H,M)=gcd(H,2q^2)=1`. Modulo3,

```
a=H=Delta=0, Df=Dt=1, Q=0, delta=Cy=-1.
```

For Dt, the integer ell=XY^2 is either0 or-1 modulo3. Uniformly
`Df>=1` and `Dt>=1`; the latter follows from ell(ell+1)>=0 for every
integer ell, without assuming that ell is positive.

## 4. Exclude zero scale; recover the guard; exclude c=0

If S=0, then sr=0 because M,H are nonzero. Hence I=0,
delta=Cy=-1, and every scaled radicand vanishes. Either polynomial
reduces to `Ac^16`. It is nonzero: D is nonzero and
`Ac=D^5 pi(T+Ccarrier/D)` is nonzero at a rational argument. Thus
every zero has s and r nonzero.

Divide a vanishing norm factor by S. Its four root terms, before their
rationality is known, are

```
sqrt(Cy/delta), 3sqrt(Df), 9sqrt(Dt), 27sqrt(Dg)
```

for P768; replace the first by sqrt(delta Cy) for P784. Their squared
3-adic orders are respectively0,2,4,6+v3(Dg). A zero guard term is
omitted. Every subset containing two or more nonzero terms has a unique
least order, and that order is even. In each rational squareclass a
signed sum therefore cannot cancel. Grouping a rational radical sum by
squareclass proves all its terms rational, even if the guard radicand
was initially negative. In particular Dg is a nonnegative integer
square. Since s is nonzero, Pair<=0 would give Dg<=-3. Thus Pair>0.

The retained elementary Pair lemma now gives G>0 and eta*zeta>0.
If c=0, then eta=-Yk and zeta=(Y+1)k, so
`eta*zeta=-Y(Y+1)k^2<=0`, a contradiction. Hence c is nonzero and
I=src^2 is nonzero. Only now is Q>1 used. Adjacent-coefficient descent
applied to `QV^2-(Q-1)y^2=1` makes its rational y integral. In the
integral presentation set y=sqrt(delta Cy)/delta first. Thus all four
normalized signed terms are integers; the first is y or delta*y.

The nonzero-scale, guard, c=0 and descent steps are in this order to
avoid assuming Q>1 on a branch where it has not yet been proved.

## 5. Recover two congruences from one carrier

The integral radical sum and the center yield `S|Ac` in either variant.
Therefore `M^5|Phi_D(zc)` and `H|Phi_D(zc)`.

For a prime p with e=v_p(M)>0, suppose b=v_p(zc)<e. Since D=MH,
the leading term zc^5 has order5b, whereas the other three terms have
orders at least `2e+3b`, `3e+2b`, and `5e`, all strictly larger.
Their sum has order5b<5e, contradicting M^5|Ac. Thus M|zc.
Since zc=D*T+M*Kstar+H(v-q^2) and gcd(H,M)=1, this gives

```
M | v-q^2, hence v=q^2(2u+1) for an integer u.
```

Consequently the existing large source scale is recovered exactly:
`Y=q^3(2u+1)`. This happens before invoking the old signed size,
ratio, rank or native-decoding arguments. In particular v=0 is now
excluded, rather than tacitly excluded at the initial definition of Y.

Reducing the carrier modulo H gives `H|(M*Kstar)^5`. Coprimality
cancels M and gives `H|Kstar^5`. Put
`Kquad=X(X+2ac)-1`. The universal identity

```
Kstar=2Kquad-HXc
```

and oddness of H imply `H|Kquad^5`. We have deliberately obtained a
fifth-power congruence, not assumed the stronger H|Kquad.

## 6. The stronger height estimate resolves the weaker congruence

After Section5, the complete signed source front, strong and auxiliary
Pell equations and strict guards are restored. The retained main-folding
argument recovers `|c|=psi_|a+2|(p)`. The c^2|I rank argument and the
two auxiliary residues recover p=R before any main projection. In the
notation of the retained proof,

```
R=2r0+1, r0>=24, x=|X|>=2^36,
m=|Y|>(x-3)^r0/2-1,
2^R Kquad == (sigma X-2^R)(2^R sigma X+1) (mod H),
sigma=sign(c).
```

Let B=(sigma X-2^R)(2^R sigma X+1). Odd H and H|Kquad^5 give
H|B^5. There is no cancellation through either variable factor B.
Each factor has magnitude at most2^(R+1)x, so
`|B|^5 <= 2^(20r0+20) x^10`.

Set L=(x-3)^r0. Since L>=4, m>L/4. Then

```
|H| >= 4(x-1)m-3 > (x-1)L-3 >= (x/2)L
     >= (x/2)^(r0+1).
```

Moreover `x^(r0-9)>=2^(36r0-324)>2^(21r0+21)` because r0>=24.
Multiplying proves `|H|>|B|^5`. Since H divides B^5, B=0. The second
factor is odd and cannot vanish for even nonzero X, so
`sigma X=2^R`. The old projection lemma now restores the actual main
root and its integral congruence witness, then the native decoder gives
a finite syntactic ZFC refutation.

This height estimate uses the actual fixed coefficient beta. It is not
claimed uniformly under the earlier much weaker lower bound x>=64.
The general useful principle is that H|B^d and |B|^d<|H| suffice to
force B=0; demanding H|B was unnecessarily strong in this application.

## 7. Completeness with a fixed strong pair

Start with a finite refutation and the canonical outer data of the
pinned source. Write its cubic-scale parameter as u and set
`v=q^2(2u+1)`. Thus Y, a, H and all other outer quantities coincide.
The canonical projection gives H|Kquad and therefore H|Kstar.
Also M|v-q^2. Hence

```
kappa=Ccarrier/D=Kstar/H+(v-q^2)/M
```

is an integer. Choose the strict joint guard witness t and its nonzero
Pell witness s. Next choose the strong pair I,f with4sc^2|I by the
retained all-residue interpolation theorem, and put r=I/(sc^2).
This pair is now fixed. Intersectivity supplies a root u0 of pi modulo I.
Request an auxiliary T in the class u0-kappa modulo I. The interpolation
theorem supplies it without changing I. Then

```
Ac=D^5 pi(T+kappa),
Ac/S=c^2 H^4 pi(T+kappa)/I in Z.
```

Choose `n=Ac/S+3f+9tau+27g+y-V` for P768, or
`n=Ac/S+3f+9tau+27g+delta*y-delta*V` for P784. All entries are integers
and a norm factor vanishes. No positivity of n is requested. The
quantifier order is outer data, t,s, I,f, an intersective residue, T,
then n; no already fixed modulus depends on a later residue.

This proves both existence directions. Every new step is elementary
integer arithmetic, finite-field/group arithmetic, CRT, Pell recurrence
or an explicit polynomial identity. Together with the named inherited
source theorem it is formalizable in ZFC without assuming Con(ZFC).

## 8. Centered evaluators and exact degrees

For P768 put `U=Sn-Ac`, `P=SV`, `L=delta*P`, `N=S^2-P^2`.
The two factors belonging to the auxiliary radical combine into

```
delta*W^2+2L*W+N,
W=U-3S*f-9S*tau-27S*g.
```

Their norm over the remaining three roots is the original cleared
four-root norm. For P784 use `L=S*delta*V`,
`N=S^2*delta-L*(SV)`, and combine the auxiliary factors as
`W^2+2L*W+N`. These identities remove high terms algebraically before
degree propagation; they are not divisions by an equation.

The important degrees are
`H:4, M:2, D:6, I:4, delta:24, V:21, S:16, Ac:35`.
For P768 the unique maximal first paired term is2LU of degree96;
the other two terms have degrees94 and74. Its eight conjugates give
degree768. For P784 the constant term N has degree98, above2LU's
degree96, giving degree784. The independent checker proves exact
graded-lex leading induction through every actual live DAG node.
In particular, with all coefficient ports fixed as supplied,

```
[j^352 w^96 v^96 s^48 r^48 c^80 T^48] P768
   = 2^744 3^448 beta^352 > 0,
[j^320 w^80 v^80 s^80 r^80 c^128 T^16] P784
   = 2^624 3^400 beta^320 > 0.
```

Thus these are attained degrees, not merely syntactic upper bounds.
The checker authenticates all six complete coefficient values, proves
each defining register by a free-ring identity, checks the complete
495-term free four-root norm and the centered cuts, checks liveness and
operation counts, and rejects changed projector/carrier/norm coefficients.
It imports no builder. Normal and optimized-Python runs perform the
same checks; these finite certificates do not replace the unbounded
arithmetic proof or claim a new formalization of the inherited calibration.

## Further questions

1. Can the stronger height margin be spent on still smaller carriers?
2. Can the M^5 divisibility demand be weakened using additional source
   information while retaining the exact cubic-scale recovery?
3. Can an intersective polynomial tailored to the strong modulus replace
   the general quintic? A congruence that fails at a prime factor of c or s
   would invalidate completeness, so modulus control must be proved first.
4. Can the 147-operation degree800, 154-operation degree784 and161-operation
   degree768 evaluators be further shortened without mixing fixed tuples?
5. Can these reductions be formalized against the exact native source
   theorem, rather than only their local polynomial identities?
