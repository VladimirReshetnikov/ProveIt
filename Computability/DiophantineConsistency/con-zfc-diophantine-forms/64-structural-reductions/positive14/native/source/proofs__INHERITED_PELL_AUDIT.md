# Pell dependency audit for the 67-operation blank-input polynomial

Audited against ProveIt commit `cdd582bec13f908df3711fa9e05d1ddac368a5db`.
Paths below are relative to `Computability/HilbertTenthProblem/Papers/`.
This is a mathematical dependency audit, not a claim of a newly compiled
Lean theorem. The executable identities and finite examples in the
upstream notes supplement their proofs; they do not replace those proofs.

## Result of the audit

The changed blank-input outer bounds suffice for the retained Pell
argument. In particular:

* `R<a` suffices for the auxiliary-quotient positivity estimate.
* `E>R+2` suffices for removing the first-index wrap **after** proving
  that the main index is exactly `p=R`.
* Neither `E>R+q^3` nor the older `E>2R` is needed in this order of proof.
* The original symmetric half-binomial theorem cannot be applied directly
  while only `X=wq` is known. First recover `X=2^R` by its lower-ratio
  argument. Then `q^3|X` is proved, all symmetric hypotheses hold, and the
  theorem applies at the same actual `R`.
* The positive converse must be applied after the dummy subset has been
  chosen and the **actual final** packed index computed. The masks and
  outer estimates verify its hypotheses at that final index.

There is a useful proof simplification: the actual normalized strong norm
directly gives `p*c | m`. Thus the generic relaxed-rank lemma, although
applicable, is unnecessary. The argument below uses this shorter route
and separately records the exact hypotheses of the older route.

No remaining Pell gap was found. This conclusion is conditional on the
separate native-compiler/mask and blank-tableau lemmas, including their
canonical carry bound and dummy preservation statements. Those are not
consequences of Pell theory.

## 1. Exact interface and pre-Pell estimates

Use the fifteen positive coordinates and four authentic fixed ports of
`fixed_blank_67.json`. Write `MF0` here for the native mask, so the supplied
port is `MFsrc=MF0+B-1`. The relevant fixed hypotheses are

```
B=2^d, d>=4, Kconstant>0,
0<MC,MF0<B-1,
MC=2 (mod 4), MF0=4 (mod 8), pc(MC)+pc(MF0)=d.
```

Define

```
q=(B-1)J+1, C=q-F-alpha,
X=wq, Y=sq^3, E=XY,
k=eta+zeta, c=kY+eta,
a=E+Y=Y(X+1), A=a+2, Delta=A^2-1, H=4a+3,
D=X+ac+gamma*H,
G=q(q-F)-C,
R=G(q^2-1)+(MC+q*MFsrc)J,
V=c(Tf-1)-Rf^2,
rho=Delta*i*c^2, Kaux=rho^2.
```

At a zero of P67, division of the **mathematical equality** by the
unconditionally positive `Delta` gives a product of six integer units:

```
N0 = tau^2-XY^2(XY^2+1)k^2,
N1 = D^2-Delta*c^2,
Na = rho^2(V^2-y^2)+y^2,
Nk = k-hE-R,
Nt = (Kconstant+w)C+(q-F)-z(q-1),
Ns = f^2-Delta*i^2*c^4,
N0*N1*Na*Nk*Nt*Ns=1.
```

This division is only a proof step: the emitted polynomial remains
division-free.

The first norm cannot be `-1` by the consecutive-product lemma below.
`Delta` is 0 or 3 modulo 4, so `N1` and `Ns` cannot be `-1`. Since
`rho^2` is a square, `Na` is congruent to `y^2` or `V^2` modulo 4 and
cannot be `-1`. Therefore

```
N0=N1=Na=Ns=1,
Nk=epsilon, Nt=nu, epsilon,nu in {1,-1}, epsilon*nu=1.
```

Before determining either remaining sign, transport implies only
`C>=0`. Indeed, `(q-F)-z(q-1)=1-F-(z-1)(q-1)<=0`, and `C<=-1`
would make `Nt<=-(Kconstant+w)<=-2`. The exceptional boundary `C=0`
must not be dropped yet. The positive slack yields `q-F=C+alpha>0`.
Consequently

```
q <= G=q*alpha+(q-1)C <= q^2-q,
0<(MC+q*MFsrc)J<(q-1)(1+2q),
q(q^2-1)<R<q^4-q^3+q^2-1<q^4-2,
R-2>3q+1, q>=B>=16,
X>=q, Y>=q^3, E>=q^4>R+2,
a>R+2, P0=2XY^2+1>A, 6XY^2>a.
```

These inequalities use no decoded mask, dyadic conclusion about `q`,
or input bridge. They are the precise replacement for the former bound
`R<q^4-q^3`.

## 2. Elementary Pell facts and upstream locations

For an integer `A>=2`, let `chi_A(n),psi_A(n)` be defined by

```
chi_A(0)=1, chi_A(1)=A,
psi_A(0)=0, psi_A(1)=1,
z(n+2)=2A*z(n+1)-z(n).
```

Then `chi_A(n)+psi_A(n)*sqrt(A^2-1)` is the nth power of the
fundamental positive integer-coefficient unit `A+sqrt(A^2-1)`.
In particular every positive integer solution of
`D^2-(A^2-1)c^2=1` has `D=chi_A(p),c=psi_A(p)` for some `p>=1`.
This classification does not need a statement about the full ring of
algebraic integers: the least positive coefficient is 1, with root A,
and division by powers of that least integer-coefficient unit preserves
integer coefficients.

The needed standard properties are addition/composition, monotonicity
in a positive index and in the parameter, the Pell norm, and strong
divisibility

```
gcd(psi_A(u),psi_A(v))=psi_A(gcd(u,v)).
```

The latter follows from the addition formula,
`gcd(chi_A(n),psi_A(n))=1`, and the Euclidean algorithm on indices.
Useful growth estimates, for `n>=1`, are

```
(2A-1)^(n-1) <= psi_A(n) <= (2A)^(n-1),
chi_A(2n)=1+2(A^2-1)psi_A(n)^2.
```

The appropriate upstream sources and their exact roles are:

| Source and section | Retained statement |
|---|---|
| `1980/PELL_RELAXED_AUXILIARY_PROOF.md`, “Two elementary Pell facts used below” | Integer-coefficient unit classification and strong divisibility. |
| `research-wip/native-stream-queue/complete75_coupled_index_linear88.md`, §2 | No negative norm for `v(v+1)`, `v>1`. |
| `research-wip/native-stream-queue/pell_kernel_half_binomial42.md`, §3 | First norm has the exact doubled coefficient `k=2psi_(2XY^2+1)(n)`. |
| `research-wip/native-stream-queue/pell_fixed_affine_exponent52.md`, §2 | Direct normalized rank: `psi_A(m)=i*c^2` implies `p*c|m`. |
| `research-wip/native-stream-queue/complete85_auxiliary_bezout_projection.md`, §§3–4 | Positivity of the quotient auxiliary root and exact main-index/sign recovery with `R<a`, `E>R+2`. |
| `1980/HALF_PARAMETER_PELL_92_PROOF.md`, §§3–4 | Odd quotient polynomials and congruence step-down. |
| `research-wip/native-stream-queue/complete75_reversed_auxiliary89.md`, §4 | Signed target recovery using `0<p,Jtarget<c/2`, avoiding a parity assumption. |
| `1980/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md`, §§2–4 | Strong plus-congruence step-down and the necessary `p=3 mod 4` for the minus branch. |
| `research-wip/native-stream-queue/complete75_asymmetric_scale_tradeoffs.md`, §§3–4 | Lower-ratio power recovery before restoring the symmetric `q^3` scale. |
| `research-wip/native-stream-queue/pell_kernel_half_binomial42.md`, §§1,5–6 | Exact half-binomial projection and its positive converse. |
| `research-wip/native-stream-queue/complete75_normalized_strong87.md`, §3 | Fresh normalized auxiliary witnesses, including `c^2|psi_A(2cR)`. |

### 2.1 Consecutive-product negative norm

For any integer `v>1`, `x^2-v(v+1)z^2=-1` has no integer solution.
For a positive solution with least positive z, its equation gives
`vz<x<(v+1/2)z`. Multiplication by the inverse unit
`2v+1-2sqrt(v(v+1))` produces another integer solution with coefficient
`z'=(2v+1)z-2x` strictly between 0 and z. Taking the absolute value of
the new root contradicts minimality. Zero coordinates cannot solve it.
Here `v=XY^2>1`, so this is exactly the needed sign exclusion.

### 2.2 First-norm classification

For positive X,Y, put `v=XY^2`, `P0=2v+1`. The first unit equation is
`tau^2-v(v+1)k^2=1`. Coefficient 1 is impossible because
`v^2+v+1` lies strictly between `v^2` and `(v+1)^2`; coefficient 2
has root `2v+1`. Thus every positive solution has

```
tau=chi_P0(n), k=2psi_P0(n), n>=1.
```

In particular no unproved evenness of q, X, Y, or k is used. Since
`P0=1 mod E`, the recurrence gives `psi_P0(n)=n mod E`. Hence

```
2n=R+epsilon+vE, v>=0, n>=(R-1)/2>=24.
```

The nonnegative v follows from `0<R+epsilon<E`; it must not yet be
replaced by zero. The main norm classifies `D=chi_A(p),c=psi_A(p)`.
`P0>A` and `c>k` imply `p>n`. Consequently `c>2p`. Also
`k=R+epsilon+hE>2R` and `c>kY` imply `c>2R`.

## 3. Auxiliary positivity and normalized rank

The strong equation gives

```
f^2=1+Delta*i^2*c^4,
rho^2=Delta*(f^2-1),
f>c^2>2c.
```

Here c is already greater than 2 directly from its positive definition.
The sole packed-index upper bound needed for the following estimate is
`R<a<Delta`:

```
rho^2-(Rf^2+c)
  =(Delta-R)f^2-Delta-c
  >=f^2-Delta-c
  =1+Delta*(i^2*c^4-1)-c > 0.
```

The auxiliary unit equation is
`rho^2 V^2-(rho^2-1)y^2=1`. It excludes V=0. If `v=|V|>1`, then

```
v^2-1=(rho^2-1)(y^2-v^2)
```

forces `y>=v+1`, and therefore `v>=2rho^2-1`. But T>0 gives
`V>-Rf^2-c>-rho^2`, excluding every negative V of absolute value
greater than 1. The cases `V=+1,-1` contradict `V=-c mod f`, since
`c>2` and `f>2c`. Thus V>0 before any auxiliary index is classified.

Restore the ordinary integer expressions

```
o=cT-Rf,
j=Tf-R*Delta*i^2*c^3-1.
```

They satisfy `of=V+c>0`, `jc=V+R>0`, hence o,j>0, and

```
V=of-c=jc-R.
```

This restoration uses no first-index sign and no input equation.

### 3.1 Preferred direct rank argument

The **actual normalized** strong equation is
`f^2-Delta*(ic^2)^2=1`. Ordinary Pell classification directly yields

```
f=chi_A(m), psi_A(m)=ic^2, m>=1.
```

Strong divisibility with `c=psi_A(p)` gives p|m. Write `m=p*b`.
Expanding `(D+c sqrt(Delta))^b` and dividing the square-root coefficient
by c gives

```
psi_A(pb)/c = b*D^(b-1) (mod c).
```

The left side is divisible by c and `gcd(D,c)=1`, so c|b. Therefore

```
p*c | m, c|m, m>=pc>2p,
rho=Delta*psi_A(m)>1.
```

This is exactly the normalized-rank argument in
`pell_fixed_affine_exponent52.md` §2. It requires no inequality
`c>A*Delta^2`.

### 3.2 The older relaxed-rank route is also valid

If the manuscript retains the original route, the precise lemma from
`1980/PELL_RELAXED_AUXILIARY_PROOF.md` is:

> If A>1, `Delta=A^2-1`, `c=psi_A(p)`, `c>A*Delta^2`, and positive
> `i_old,f` satisfy `(i_old*c^2)^2=Delta*(f^2-1)`, then for some m>0,
> `f=chi_A(m)`, `p|m`, `c|m`, and `i_old*c^2=Delta*psi_A(m)`.

Use `i_old=Delta*i`. The preliminary bound `p>n>=24` implies
`c>A*Delta^2` by the above growth estimate, independently of either
remaining unit sign. Thus this route is sound, but longer. It must not
claim `c^2|psi_A(m)` from the relaxed norm alone; that stronger conclusion
is available here because the actual source is normalized.

## 4. Exact auxiliary target, no wrap, and all positive unit signs

Set rho as above. With V,y>0, the auxiliary norm classifies

```
rho*V=chi_rho(ell), y=psi_rho(ell), ell>=1.
```

The index ell is odd: for even ell, `chi_rho(ell)=+1 or -1 mod rho`,
contradicting rho>1 dividing the first coordinate. Write `ell=2u+1`.
The integer polynomials Q_u defined by

```
chi_Z(2u+1)=Z*Q_u(Z^2),
Q_0(t)=1, Q_1(t)=4t-3,
Q_(u+2)(t)=(4t-2)Q_(u+1)(t)-Q_u(t)
```

satisfy

```
Q_u(1-A^2)=(-1)^u psi_A(ell),
Q_u(0)=(-1)^u ell.
```

Since `rho^2=1-A^2 mod f` and `c|rho`, the two restored congruences
give

```
(-1)^u psi_A(ell)=-c mod f,
(-1)^u ell=-R mod c.
```

Squaring the first and using the doubling formula yields
`chi_A(2ell)=chi_A(2p) mod chi_A(m)`. The plus step-down lemma states:

> For A>=2, m>=1, `0<k<=m`, n>=0,
> `chi_A(n)=chi_A(k) mod chi_A(m)` implies `n=+k or -k mod 4m`.

Its direct proof is in `EXPLORATION_FIXED_MINUS_INDEX_PARITY.md` §2:
reduce by `chi_A(n+2m)=-chi_A(n) mod chi_A(m)` and evenness in n,
then use strict monotonicity and
`2chi_A(m-1)<chi_A(m)` to distinguish the small representatives.
It applies with k=2p because m>2p. In particular
`ell=+p or -p mod m`, hence modulo c. The other congruence gives
`R=+p or -p mod c`. Since `0<R<c/2` and `0<p<c/2`, it follows that

```
p=R.
```

This proof does not assume R is odd, does not use mask decoding, and
does not use the full parent universal theorem.

Return now to `2n=R+epsilon+vE`. If v>=1, then

```
2n>=R-1+E>2R,
```

using only `E>R+2`, whereas n<p=R. Thus v=0. If epsilon=-1, then
`p=2n+1`. Put `Q=chi_A(2)=2A^2-1`; the definitions give Q>P0 and
A>Y+1. Duplication and parameter monotonicity imply

```
psi_A(2n)=2A*psi_Q(n)>=2A*psi_P0(n)=A*k,
c=psi_A(2n+1)>A*k>k(Y+1),
```

contradicting `kY<c<k(Y+1)`. Therefore

```
epsilon=nu=1,
2n=R+1, R is odd,
k=2psi_P0((R+1)/2),
Nt=1.
```

Only now does transport imply C>0: C=0 would make Nt<=0.

The necessary fixed-minus parity theorem in
`EXPLORATION_FIXED_MINUS_INDEX_PARITY.md` §4 now applies with

```
p=R>=3 odd, c=psi_A(p)>2p,
f=chi_A(m)>2c, c|m, m>=2p,
rho>1, c|rho, rho^2=Delta*(f^2-1),
V=-p mod c, V=-c mod f, V,y>0.
```

It gives `p=3 mod 4`. Its proof retains both step-down signs and both
parities of m; it does not assume a canonical choice m=2cR.

## 5. Recover X=2^R before applying any masks

At this point write `r0=(R-1)/2>=1`, `k0=k/2=psi_P0(r0+1)`, and

```
xi=(X+1)^(2r0)/X^r0.
```

The elementary growth bounds give

```
c/k0 >= xi*(1+3/(2a))^(2r0)*(1+1/(2XY^2))^(-r0) > xi.
```

The strict comparison requires only `6XY^2>a`: indeed
`(1+3/(2a))^2>1+3/a>1+1/(2XY^2)`. This is why neither an upper
ratio-error estimate nor X>=q^3 is needed yet. Together with
`c/k<Y+1`, it gives

```
Y>xi/2-1>X^r0/2-1>X^r0/3,
a>X^(r0+1)/3,
2^R=2*4^r0<X^(r0+1)/3<a, X<a.
```

The final comparison holds already for X>=16 and r0>=1. The sequence
`chi_A(j)-a*psi_A(j)` has initial values 1,2 and the Pell recurrence.
Modulo H=4a+3, this is the recurrence of `2^j`, because
`4A-5=H`. The main root definition therefore gives `X=2^R mod H`.
Both positive integers are below a<H, so

```
X=2^R.
```

This is the precise lower-ratio proof in
`complete75_asymmetric_scale_tradeoffs.md` §3. No population threshold
or genuine-word assertion has been used.

Since q|X and q>0, q=2^t for an integer t>=4. The pre-Pell lower bound
gives `R>3q>3t`, hence q^3|X. Therefore

```
w_old=X/q^3=w/q^2
```

is a positive integer. With this proof-only substitution all original
symmetric kernel hypotheses hold at the **unchanged** q,R,X,Y:

```
q>=16, 3q+1<=R<q^4,
X=w_old*q^3, Y=s*q^3,
k=R+1+hXY,
rho=(Delta*i)c^2,
V=jc-R=of-c.
```

The original first norm is also identical, since
`(E^2+X)(kY)^2=XY^2(XY^2+1)k^2`. Thus
`pell_kernel_half_binomial42.md` §§1,5–6 applies without changing any
actual packed index or main parameter. In particular

```
Y=floor((X+1)^(R-1)/X^((R-1)/2))/2,
v2(Y)=pc((R-1)/2)-1,
pc(R)>=3t+2.
```

The relation `(B-1)|q-1`, with B=2^d and q=2^t, then gives d|t by
the usual exponent remainder argument. Write `t=dN`; this is the point
at which repeated-cell masks may be decoded with q=B^N.

## 6. Exact half-binomial converse at the tuned actual R

The kernel converse has the following precise numerical interface:

```
q=2^t, t>=4,
3q+1<=R<q^4,
R=3 mod 4,
pc((R-1)/2)>=3t+1
```

(equivalently, since R is odd, `pc(R)>=3t+2`). No hypothesis refers
to an earlier untuned index. It supplies fresh positive Pell witnesses
at that q,R.

### 6.1 Verify the hypotheses after tuning

In the blank-tableau construction, first choose the canonical helical
word, width h and height Htime, with `q=B^N`, `N=h*Htime`, and all
dummy bits initially zero. Then choose the Boolean dummy subset and
compute the resulting **actual** C,F and

```
R=[q(q-F)-C](q^2-1)+(MC+q*MFsrc)J.
```

The separate compiler proof must establish the following facts for that
final word, not only for the baseline word:

```
C,F>0, C+F<q,
(C-1) AND (MC*J+1)=0,
F AND (MF0*J-1)=0,
R=d*h mod dN.
```

The canonical mass bound `2C+F<q/3` is more than enough for the first
line and survives every allowed dummy subset. The mask conditions give
the exact population, not just a lower bound. Put

```
S=(C-1)+qF,
TC=MC*J+1, TF=MF0*J-1, Tmask=TC+q*TF.
```

Then `1<=S<q^2`, `0<Tmask<q^2-1`, `pc(Tmask)=dN+2`, and the exact
shifted packing identity is

```
R=(q^2-S)(q^2-1)+Tmask.
```

The inverse-population identity in
`complete75_half_binomial_compiler.md` §2 therefore gives
`pc(R)=3dN+2`. Also the canonical Start at the origin gives C=1 mod4;
q=0 mod4, J=1 mod4, MC=2 mod4 imply `S=0 mod4`, `Tmask=3 mod4`,
hence `R=3 mod4`. The dummy exponent is positive, so dummy tuning
does not alter these low bits. Finally the same outer estimate as in
§1 gives `3q+1<R<q^4`. Thus every converse hypothesis holds with
`t=dN` at the final actual R.

This is the required noncircular order: choose the genuine rotation,
tune the actual packed rank, verify mask/range/parity facts, then invoke
the Pell converse. Replacing R by an abstract congruent representative
would not justify it.

### 6.2 Fresh main and first Pell witnesses

Set `r0=(R-1)/2`, `X=2^R`, and

```
M=binom(2r0,r0)+sum_(j=1)^r0 binom(2r0,r0+j)*X^j,
Y=M/2.
```

Here M is even and
`xi=(X+1)^(2r0)/X^r0=M+theta`, with `0<theta<1/4`.
The valuation identity
`v2(binom(2r0,r0))=pc(r0)` is below R; every other term in M is
divisible by X=2^R. Thus `v2(Y)=pc(r0)-1>=3t`, so Y/q^3 is a
positive integer. R>3t makes both X/q and X/q^3 positive integers.
Use `s=Y/q^3`, `w=X/q` for P67.

With fresh `a=Y(X+1)`, A,Delta,E,P0, define

```
c=psi_A(R), D=chi_A(R),
k=2psi_P0((R+1)/2), tau=chi_P0((R+1)/2),
eta=c-kY, zeta=k-eta,
h_kernel=(k-R-1)/E,
gamma=(D-X-ac)/(4a+3).
```

The ratio inequalities hold at this newly selected Y. For clarity, their
converse use is not circular: `Y=M/2>=X^r0/2` gives the required
large-a bound directly; the general upper estimate

```
c/(k/2)<xi*(1+2/a)^(2r0)<xi*(1+8r0/a)
```

then gives `0<c/k-xi/2<16r0/(X+1)<1/2`. Together with
`0<theta<1/4`, this proves `Y<c/k<Y+1`, so eta,zeta are positive
integers. The first recurrence modulo E proves h_kernel integral;
strict Pell growth proves h_kernel>0. The projection recurrence proves
gamma integral, and
`D-ac=2c-psi_A(R-1)>c>X` proves gamma>0.

The subscript on h_kernel distinguishes this supplied Pell quotient
from the external helical width h. They are different numbers and
must not be conflated merely because earlier notes use the same letter.

### 6.3 Fresh normalized auxiliary witnesses and quotient T

Set

```
m=2cR,
f=chi_A(m),
i=psi_A(m)/c^2,
rho=Delta*psi_A(m),
y=psi_rho(R), V=chi_rho(R)/rho.
```

All divisions are exact. For i, expand
`(D+c sqrt(Delta))^(2c)`: the term with one square-root factor is
`2c^2 D^(2c-1)`, and every other odd term contains at least c^3.
Therefore `c^2|psi_A(2cR)`. This is the additional divisibility proved
in `complete75_normalized_strong87.md` §3.

Because R is odd, the odd quotient polynomial makes V integral.
Because `R=3 mod4`, its two congruences give

```
V=-c mod f, V=-R mod c.
```

Consequently `o=(V+c)/f` and `j=(V+R)/c` are positive integers.
They are positive already from V>0 and positive c,R; the stronger
canonical estimate V>c>R from the upstream proof also holds. Define

```
T=(o+Rf)/c.
```

The identity `of+R=c(j+1)` and `f^2=1 mod c` imply
`o+Rf=0 mod c`, so T is a positive integer. Its definition gives
`c(Tf-1)-Rf^2=of-c=V` exactly. These fresh witnesses satisfy the
normalized strong and auxiliary factors. No divisibility of an
arbitrary old relaxed witness by Delta is being assumed.

### 6.4 Transport at the same actual rank

The tuning congruence `R=d*h mod dN` makes
`X=2^R=B^h mod q-1`. Since q=1 mod(q-1), `w=X/q` has the same
residue. For the canonical native field, let

```
(Kconstant+B^h)C=F+z0(q-1).
```

The canonical construction and the outer lower bound give `w>B^h`.
Then

```
z=1+z0+[(w-B^h)/(q-1)]C
```

is a positive integer and makes Nt=1. Set `alpha=q-F-C>0`.
All six factors are now exactly their required positive units, so
P67=0 at the final actual packed index.

## 7. Limits and points that should remain explicit in the article

1. The new polynomial is not an unrestricted substitution into the old
   complete84 universal theorem. The deleted input bridge and changed
   no-End semantics require the separate blank-tableau/compiler proof.
   The Pell reasoning is local and has been checked without using that
   theorem circularly.
2. The four compiler ports are the four specific integers from the
   closed recipe. Arbitrary integers satisfying just the displayed mask
   congruences need not encode the blank machine.
3. C=0 is a real preliminary boundary of the unit transport equation.
   It disappears only after Nk=Nt=1 is proved.
4. The symmetric kernel must be used only after q^3|X is established,
   or via a separately proved asymmetric formulation. Its original
   hypotheses are not silently weakened.
5. The kernel's positive converse is parametric at the final R. Finite
   Pell examples and source-evaluator tests do not materialize an actual
   K215 halting tuple and are not evidence that ZFC is inconsistent.
6. The argument is an ordinary mathematical proof intended to be
   formalizable in ZFC. These upstream notes and the current audit are
   not a replacement for a kernel-checked formalization of the new
   Diophantine reduction.

