# Independent audit of the twelve-variable radical amalgamation

This note audits the proposed new construction against the source snapshot
`f0ae4e0991ca44a7bb4e5671d42e33d775e48035`. It is an ordinary mathematical
proof, not an end-to-end Lean or Rocq certificate. The signed arithmetic
interface is the theorem in package `12-gap-norm14`,
`proofs/ORDINARY_BLANK_PROOF.md`, especially Sections 2, 4--7. The valid
compiler coefficient tuple is an input hypothesis to that theorem.

## 1. Definitions under audit

Retain the positive integer coordinates

```
J,F,alpha,z,h,i,T,s,w,eta,zeta,r.
```

Use the existing normalized blank compiler abbreviations

```
q = beta*J+1                 Cw = q-F-alpha
X = w*q                     Y = s*q^3
E = X*Y                     k = eta+zeta
c = k*Y+eta                 a = E+Y
H = 4*a+3                   Delta = a^2+H
Lfirst = E*(k*Y)            A = 1+Lfirst*(Lfirst+k)
b0 = X+a*c                  G = 1+Delta*c^2
R = ((q-1)*(q-F)+alpha)*(q^2-1)+(MC+q*MFsrc)*J
Nk = k-h*E-R
Nt = (K+w)*Cw+q-F-z*(q-1).
```

Here `MFsrc` is the shifted high-mask port, not the native high mask. Define

```
Q = (Delta*i*c^2)^2         D = 1+Delta*i^2*c^4
v = c*T                    b = c+R*D
d = Q-1                    e = Q*(D*v^2+b^2)-1
B = 2*Q*v*b
Rbig = v^2+D+2*b
L = 1+H*Rbig
S = b0+H*r.
```

The symbol `B` in this proof denotes a root cross coefficient and must be
renamed in a publication if the compiler radix is also named `B`.

For formal indeterminates `u,tau`, put

```
F(u,tau) = [d*(S-L*u-H*L*tau)^2-H^2*e]^2-H^4*B^2*D.
```

The proposed residual is the product over the four formal sign choices

```
N12 = product F(epsilon*sqrt(G),delta*sqrt(A)),
      epsilon,delta in {+1,-1}.
```

The product belongs to the integer polynomial ring in the twelve retained
coordinates. Equivalently it is obtained by taking the two quadratic norms,
or the iterated monic resultants with `u^2-G` and `tau^2-A`. Neither radical
is a numerical operation in the final circuit. This note audits the system

```
Nk=1, Nt=1, N12=0.
```

## 2. The rational auxiliary-Pell integrality lemma

**Lemma.** Let `s0>=2` and `V` be integers. If a rational number `y`
satisfies

```
s0^2*V^2-(s0^2-1)*y^2=1,
```

then `y` is an integer.

**Proof.** Write `y=a0/b0` in lowest terms, with `b0>0`. The equation
implies `b0^2 | s0^2-1`, because `a0` and `b0` are coprime. Put
`D0=(s0^2-1)/b0^2`. This is a positive nonsquare integer: otherwise
`s0^2-1` would be a square. The pairs `(s0,b0)` and
`(|s0*V|,|a0|)` are positive integer solutions of

```
x^2-D0*y0^2=1.
```

Neither second coordinate vanishes. Let `epsilon=x1+y1*sqrt(D0)>1` be
the least positive norm-one Pell unit, and write
`epsilon^n=x_n+y_n*sqrt(D0)`. Pell classification gives positive indices
`r0,t0` with `(s0,b0)=(x_r0,y_r0)` and
`(|s0*V|,|a0|)=(x_t0,y_t0)`.

The first coordinates have the exact divisibility property

```
x_r0 | x_t0  iff  t0 = r0 (mod 2*r0).
```

To see this, use
`x_(n+2r0)=-x_n (mod x_r0)` and
`x_(2r0-j)=-x_j (mod x_r0)`. The first identity follows from
`x_2r0=2*x_r0^2-1` and `y_2r0=2*x_r0*y_r0`; the second follows from
the Pell subtraction formula. After reducing and reflecting the index,
every residue other than the one at `r0` is a signed `x_j` with
`0<=j<r0`, and `0<x_j<x_r0`. Thus no such residue is zero.

Since `s0` divides `|s0*V|`, the index `t0` is an odd multiple of `r0`.
The Pell composition identity then gives `y_r0 | y_t0`, i.e.
`b0 | a0`. Coprimality forces `b0=1`. This proves the lemma.

The lemma is essential. Merely observing that `d*y^2` is an integer, or
that `H*y` is an integer, would not prove integrality of `y` in general.
No extra restriction on the normalized multiplier `i` is needed.

## 3. Bounds needed at a solution

Assume the proposed system has a positive integer solution. The transport
equation first gives `Cw>0`: its alternate form is

```
(K+w)*Cw=F+(z-1)*(q-1),
```

whose right side is positive since `F,z>=1`. The authentic coefficient
conditions then give `R>0`; all other quantities `a,H,Delta,A,G,Q,D,v,b`
are positive, with `A,G,Q,D>1`. In particular `d>0` and `B>0`.

If `f'` is either square root of `D` and `y'` is either square root of
`(e-B*f')/d`, then, even if `y'` is complex,

```
|y'|^2 <= (e+B*sqrt(D))/d
        = [Q*(v*sqrt(D)+b)^2-1]/(Q-1)
        < 2*(v*sqrt(D)+b)^2
        < [2*(v*sqrt(D)+b)]^2 <= Rbig^2.
```

Here `Q/(Q-1)<2`, since `Q>2`, and
`v^2+D>=2*v*sqrt(D)` by the square `(v-sqrt(D))^2>=0`.
Hence `|y'|<Rbig`. This sharper bound
replaces the initially proposed, much larger `e+B*D+1` without changing
any subsequent argument. The choice of weights supplies the strict bounds

```
L*sqrt(G) > H*Rbig,
H*L*sqrt(A) > L*sqrt(G)+H*Rbig.
```

The first follows from `L>H*Rbig` and `G>1`. For the second, write
`ell=Lfirst=k*E*Y`. Since `sqrt(A)>ell`,
`sqrt(G)<(a+2)*c`, and `c<k*(Y+1)<=2*k*Y`, one has

```
H*sqrt(A)-sqrt(G)
  > H*ell-(a+2)*c
  > k*Y*[H*E-2*(a+2)]
 >= k*Y*[H-2*a-4]
  = k*Y*(2*a-1)>1.
```

Multiplication by `L`, followed by `L>H*Rbig`, proves the second bound.
Thus the extra factor `M` in the first draft is unnecessary: the same
weight `L` works for both the main root and the first root, with the latter
scaled by `H`. These inequalities are uniform. They do not depend on an
unproved choice of signs for any root.

## 4. Existence of a coherent radical branch

Over the complex numbers, the evaluated residual `N12` is exactly the
product of the four values of `F` at `u=+/-sqrt(G)` and
`tau=+/-sqrt(A)`. A zero of this product therefore supplies one pair
`u,tau` with `u^2=G`, `tau^2=A`, and `F(u,tau)=0`.

Put `y=(S-L*u-H*L*tau)/H`. The selected `u,tau` are real because
`A,G>0`, so `y` is real. The equation `F=0` gives a coherent choice
`f=+/-sqrt(D)` satisfying

```
d*y^2=e-B*f,
S=L*u+H*L*tau+H*y.
```

This step does not assume that every formal combination of radical signs
extends to an automorphism. It only chooses one zero factor of an exact
finite product. Subsequent automorphisms are taken in the actual normal
closure of the field generated by this selected branch.

## 5. Galois descent forces all selected roots to be rational

Take a finite normal closure over Q containing the selected algebraic
numbers. If `tau` were irrational, an automorphism would send `tau` to
`-tau`. It sends `u` to one of its two conjugates, and every image of `y`
has magnitude less than `Rbig` by Section 3. Applying it to the rational
quantity `S` and subtracting would give

```
2*H*L*sqrt(A) <= 2*L*sqrt(G)+2*H*Rbig,
```

contrary to the strict dominance bound. Hence `tau` is rational.

If `u` were irrational, an automorphism would send `u` to `-u`; it fixes
the now rational `tau`. Subtraction would give

```
2*L*sqrt(G) <= 2*H*Rbig,
```

again impossible. Thus `u` is rational. The displayed expression for `S`
now makes `y` rational. Finally `f=(e-d*y^2)/B` is rational, because
`B!=0`.

This argument permits complex images of `y`; their moduli are bounded.
It does not need the entire normal closure to be a totally real field.

## 6. Integral restoration and signed arithmetic soundness

Since rational square roots of integers are integral, `tau,u,f` are
integers. Define `V=v*f-b`, which is integral. Using `f^2=D`, the first
relation in Section 4 becomes

```
(Q-1)*y^2=Q*V^2-1.
```

The coefficient `Q=(Delta*i*c^2)^2` is an integer square at least four.
The lemma in Section 2 therefore proves that `y` is integral.

Because `L=1+H*Rbig` and `S=b0+H*r`, the second relation in Section 4
implies

```
u-b0=H*(r-Rbig*u-L*tau-y).
```

Thus `gamma=(u-b0)/H` is an integer, and the main Pell root identity
`u=X+a*c+gamma*H` holds. The restored first, main, strong and auxiliary
norms are respectively

```
tau^2-Lfirst*(Lfirst+k)=1,
u^2-Delta*c^2=1,
f^2-Delta*i^2*c^4=1,
Q*V^2-(Q-1)*y^2=1.
```

The other two equations are the retained `Nk=Nt=1`. Replace the normalized
multiplier by `i_ordinary=Delta*i`. Then
`(i_ordinary*c^2)^2=Delta*(f^2-1)=Q`, so these are precisely the ordinary
signed system of package 12. Its domain theorem explicitly permits signed
`f,tau,y,gamma,T,h`; its proof classifies `|u|` and later forces the main
root and `gamma` positive. Consequently no positivity assumption on the
reconstructed roots is missing. Its compiler soundness theorem proves
blank K215 halting.

## 7. Completeness

Start with a canonical positive normalized blank K215 witness. Compute
the displayed abbreviations, retaining its positive main root `u` and
positive roots `tau,y,f`. Choose

```
r=gamma+Rbig*u+L*tau+y.
```

This is a positive integer, and `S=L*u+H*L*tau+H*y`. The defining
norm equations give `F(u,tau)=0`, so its sign-product `N12` vanishes.
Both retained equations hold. Deleting `f,tau,y,gamma` and adding `r`
therefore maps fifteen positive supplied coordinates to twelve positive
supplied coordinates without imposing any new restriction on a canonical
halting witness.

## Audit conclusion and remaining implementation checks

The proposed three-equation twelve-positive-variable construction is
mathematically sound and complete relative to the same authentic compiler
and K215 calibration as its source packages. The argument resolves the
main denominator and sign risks. Its proof uses only finite algebra,
elementary Pell theory and finite Galois theory, all available in ZFC.

The emitted polynomial circuit must also be checked against the exact
quadratic-norm definition. Its size and leading-form checks are separate
from this semantic proof. This note claims no global minimum.

## 8. A single product polynomial

The same equivalence holds for

```
P12 = Nk*Nt*(1+N12)-1=0.
```

To justify its unit guard, first reduce `F` in the ring
`Z[u,tau]/(u^2-G,tau^2-A)`. Its coefficients of `u`, `tau`, and `u*tau`
are all divisible by four. Indeed, the corresponding three coefficients
of `(S-L*u-H*L*tau)^2` are even; squaring the resulting expression makes
all three nonconstant coefficients divisible by four. The subtracted
constant term changes none of them. Taking the norm in `tau` gives an
expression `E0+E1*u` with `E1` divisible by eight. The last norm is

```
N12=E0^2-G*E1^2=E0^2 (mod 64).
```

In particular `1+N12` is either one or two modulo four and cannot be -1.
At a zero of `P12`, each of `Nk,Nt,1+N12` is an integer unit. Thus
`N12=0` and `Nk=Nt=epsilon` for one sign `epsilon`.

Weak transport still gives `Cw>=0`. Its exact expression is

```
Nt=(K+w)*Cw+1-F-(z-1)*(q-1).
```

If `Cw<=-1`, the right side is at most `-(K+w)<=-2`, impossible for a
unit. It follows that `q-F=Cw+alpha>0`, and all existing positive bounds
on `R`, `b`, and the weights apply. Do not discard the `Cw=0` boundary
at this stage: with `epsilon=-1` it is a genuine algebraic possibility.

The radical restoration now gives first, main, strong and auxiliary
norms equal to one, together with `Nk*Nt=1`. After the same multiplier
change these satisfy exactly the signed ordinary product `P69=0` in
package 12. Its proof explicitly handles the equal negative signs and
the `Cw=0` boundary, then forces both signs positive after recovering the
Pell index. Hence it proves blank halting without a circular sign claim.

## 9. Exact leading forms of the emitted circuit

Write `q0=beta*J` and `k0=eta+zeta`. The degree-1344 leading homogeneous
form of `N12` is

```
2^80*i^48*k0^112*w^112*s^224*q0^832*(q0-F)^16.
```

The circuit's last two quadratic-norm coefficients have degrees 672
and 605. Therefore the final squared first coefficient has degree 1344,
whereas the subtracted term has degree `22+2*605=1232`; no cancellation
can occur at the displayed leading degree. The earlier unique leading
term is `(d*a0)^8`, with `a0=H^2*L^2*A`. Since the leading parts of
`d,L` are `Q,2*H*b`, this becomes `2^16*Q^8*H^32*b^16*A^8`, yielding
the stated expression.

The degree-1353 leading homogeneous form of the product is

```
-2^80*h*i^48*k0^112*w^113*s^225*q0^836*(q0-F)^16
        *[w*(q0-F-alpha)-z*q0].
```

The coefficient of
`J^853*h*z*i^48*eta^112*w^113*s^225` is `2^80*beta^853`, nonzero
for every authentic fixed tuple (`beta>0`). This certifies the exact
degree for the actual astronomical coefficients, not just a synthetic
numeric specialization. The sum of squared three residuals has degree
2688 because `N12^2` is its unique term of that degree.

## 10. Extension to twenty-six unrestricted integer unknowns

The same system and product are sound on the expanded domain

```
J,F,alpha,z,s,eta,zeta > 0;
i != 0;  w >= 0;
h,T,r arbitrary integers.
```

This requires two boundary arguments; the preceding positive-domain
proof must not simply be reused without them.

### 10.1 Bounds and descent with signed T

Weak transport works because the authentic fixed `K>=2`, including when
`w=0`. Thus `Cw>=0`, `q-F>0`, and `0<R<q^4` still hold. Since
`Y>=q^3`, `a=(X+1)*Y>=q^3`, one also has `Delta>q^6>R` before proving
`w>0`. The quantities `Q,D,d,b` remain positive, with `Q,D>1` and
`b>1`, because only `i^2` occurs in these quantities.

For signed `v=c*T`, the conjugate estimate becomes

```
|y'|^2 <= [Q*(abs(v)*sqrt(D)+b)^2-1]/(Q-1)
        < 2*(abs(v)*sqrt(D)+b)^2 < Rbig^2,
```

using `v^2+D>=2*abs(v)*sqrt(D)`. Thus no absolute value must be added to
the polynomial weight. If `w>0`, the preceding dominance proof applies.
If `w=0`, then `E=ell=0` and `A=1`, so the first root `tau=+/-1` is
already rational; its dominance step is unnecessary. In either case
the main-root automorphism argument proves that `u` is rational, and
therefore so is `y`.

If `T!=0`, then `B!=0`, and the preceding restoration proves that `f`
and `y` are integers. If `T=0`, the chosen zero factor instead directly
gives

```
(Q-1)*y^2=Q*b^2-1.
```

Apply the rational auxiliary-Pell lemma with `V=b`; it again makes `y`
an integer, without having recovered `f`. Consequently `u,tau,y` and
the restored `gamma=(u-b0)/H` are integral in both cases.

### 10.2 Excluding w=0

If `w=0`, then `X=0`, `a=Y`, and `u=a*c+gamma*H`. The restored main norm
would give

```
1=u^2-Delta*c^2=H*(2*a*c*gamma+gamma^2*H-c^2),
```

impossible since `H>1`. Thus every zero has `w>0`.

### 10.3 Excluding T=0

Use `Delta>R` and `D=1+Delta*i^2*c^4` to obtain

```
Q-b=(Delta-R)*D-Delta-c
   >=D-Delta-c
   =1+Delta*(i^2*c^4-1)-c > 0.
```

Here `abs(i)>=1` and `c>=2`. Thus `1<b<Q`. If `T=0`, the integral
`y` of Section 10.1 would satisfy

```
y^2=b^2+(b^2-1)/(Q-1).
```

Since `Q-1>=b`, the last summand is strictly between zero and `b`, and
hence between zero and `2*b+1`. This puts the integer square `y^2`
strictly between `b^2` and `(b+1)^2`, a contradiction. Thus `T!=0`.
Now `f` can be restored as before and is integral. Use the positive
ordinary multiplier `i_ordinary=Delta*abs(i)` in the proof-only
translation. The source signed ordinary theorem permits the remaining
signs and proves soundness.

### 10.4 Completeness of a polynomial integer parametrization

Package `14-integer29`, Section 7, supplies canonical normalized witnesses
with odd positive `i` and square positive `w`. Its proof uses that the
compiler exponent `d_compiler` and padded period `N` are odd powers of
five and that the actual index `R` is odd. All the current power-of-five
coefficient recipes have this property. The odd strong multiplier is
obtained by the auxiliary index `m=c*R`; the full auxiliary block, not
only its strong norm, is proved to have a witness in that source.

For each of the seven guarded coordinates independently substitute

```
Pos(x,y,z)=1+x^2+y^2+z*(z+1),
```

which is positive and represents every positive integer by the classical
three-square theorem. Put `i=2*j+1`, `w=u0^2`, and leave `h,T,r`
unrestricted. There are `7*3+2+3=26` integer unknowns. The substitutions
are sound by the expanded domain theorem and complete by the canonical
odd/square choices; hence both existence predicates are equivalent.

They cost 52 binary operations: seven positivity substitutions at seven
gates each, two gates for `2*j+1`, and one square for `u0^2`. The three
forms therefore have 164, 168 and 171 gates, respectively, using the
emitted positive-domain counts 112, 116 and 119. The smaller final
norm circuit uses the identity
`(C^2+K-Z)^2-4*C^2*K=(C^2-K-Z)^2-4*K*Z` with scalar `Z`, saving six
gates without changing the polynomial.

For degree accounting give weight two to
`J,F,alpha,z,s,w,eta,zeta`, and weight one to `i,h,T,r`. The same leading
forms remain the unique highest-weight terms. Their weights are 2640
for `N12` and 2657 for the product; the SOS has weight 5280. Substituting
disjoint quadratic positivity forms preserves nonvanishing. For example,
the integer product coefficient of

```
J1^1706*z1^2*h*j^48*eta1^224*u0^226*s1^450
```

is `2^128*beta^853`. Thus the integer degrees are exactly 2640 for the
system's largest residual, 2657 for the product, and 5280 for the SOS.

## 11. Completed implementation audit

The independent program `audit_norm12.py` imports no candidate generator.
It reads the frozen six JSON packets, checks every register, operation and
dependency, and verifies that all computed gates and supplied ports are
live. Its recorded operation counts are 112/116/119 for the positive
system/product/SOS and 164/168/171 for their 26-integer substitutions.
Their degree upper bounds agree with the uniform exact-degree proofs above.

It separately checks the optimized norm tail against the direct product
of four exact integer conjugates in 96 signed fixtures where both tested
radicands are squares. In 128 further full-circuit fixtures modulo 1009,
it locates both radical roots in the finite field and directly multiplies
the four zero-factor candidates. The full circuit agrees in every case;
both finalizers agree with their definitions. Every exact integer fixture
also satisfies the claimed mod-64 unit-guard relation. These checks
exercise independent arithmetic routes and are finite implementation
evidence, not the semantic proof.

`INDEPENDENT_CIRCUIT_AUDIT.json` records every per-packet SHA-256 hash,
gate count, degree upper bound and check count. The final positive product
hash is
`ed0232c9530cebd14abfb079285eae16c2c603c624f0777aeb81447cba3d3021`;
the final integer product hash is
`1964e6c561674106683a21f24499d1b145b427972b2525af3d0ece76991d9016`.
