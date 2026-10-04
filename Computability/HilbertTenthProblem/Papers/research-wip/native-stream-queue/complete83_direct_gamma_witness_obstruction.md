# Direct reuse of a supplied witness cannot replace the main quotient

Every direct identification of the main quotient with one of the other seventeen supplied witnesses in the current [universal84 source](complete84_scaled_strong_output.md) gives an **empty positive zero set on every inherited valid compiler slice**. The [fresh compiler/checker](complete83_direct_gamma_witness_obstruction.py) emits all seventeen complete arrays in its [receipt](complete83_direct_gamma_witness_obstruction.json). Each costs **83=47M+36A**, has **17 positive witnesses**, and has uniform exact degree **187**. These are rejected charts, not universal representations.

The grammar is deliberately narrow: delete `gamma_sum=rho+sigma`, delete the now unused supplied port `sigma`, and replace the first operand of `gam=gamma_sum*a4m5` by exactly one of the seventeen other supplied witness ports. Every other retained row, all six fixed compiler numeral recipes, ordinary positive input, and the full finalizer remain unchanged. No conclusion about nonlinear expressions, new coordinates, changed norm producers, or other circuits follows.

## 1. Complete sources and the legitimate positive map

The seventeen choices, grouped by their obstruction, are:

| Group | Literal supplied ports |
|---|---|
| Smaller outer coordinates | `Jrep,F,alpha,transport_quotient,h,s,w,Z` |
| Larger native coordinates | `f,i,auxiliary_quotient,tau_root,y_aux` |
| Opposite parity | `eta,zeta` |
| Input Pell coefficient gap | `delta` |
| Equal input/main projection quotient | `rho` |

The `gamma_sum` gate has only the `gam` consumer, and `sigma` has only the deleted gate as a consumer. Thus the rewrite removes exactly one addition and one positive witness. Every other source definition and the seven-row finalizer are literal parent rows. All 83 gates and all 24 remaining free ports are live in each form. The complete ledger is 41M+35A for the producers and 6M+1A for the finalizer.

Let v denote the selected supplied port and Gamma the resulting main quotient. Over every commutative ring,

```
P_v = P84(sigma_old=v-rho),       Gamma=v.                 (1)
```

The private coefficient identity is `rho+(v-rho)=v`. It includes the case v=rho. The signed inverse need not be positive, so (1) alone does not invoke parent universality.

Instead each positive child zero maps positively to the [independent-gamma83 source](complete83_independent_gamma_scout.md) by giving its independent main port the value v and retaining every other coordinate. Identifying two ports does not invalidate any of that source's necessary local conclusions. Those conclusions were proved without main/input quotient dominance and without assuming its unresolved ordinary-input language is sound. In particular the scaled output can first be divided by its positive Delta; the normalized product then has the established unit signs. We do not infer seven unit equations directly from a product equaling Delta.

## 2. Native consequences and a strict quotient sandwich

Use mathematical Pell parameter A and discriminant Delta, distinct from the literal register `A`, which contains Delta:

```
X=wq, Y=sq^3, E=XY, a=Y(X+1), A=a+2,
Delta=A^2-1, H=4a+3=4A-5,
k=eta+zeta, c=kY+eta, D=X+a*c+Gamma*H.
```

The inherited native-only proof and [normalized auxiliary review](review_complete85_auxiliary_bezout_math.md) give, at every hypothetical positive zero,

```
q>=B>=16, R>=3q+1, R=3 mod4, R<a,
X=2^R<a, Y>=q^3, A even, Delta odd,
k=2*psi_P(n), P=2XY^2+1, kY<c<k(Y+1),
k-hE=R+1,
D=chi_A(R), c=psi_A(R),
f^2=1+Delta*i^2*c^4,
V=c(Tf-1)-R*f^2>0, T=auxiliary_quotient,
Kaux=Delta^2*i^2*c^4,
Kaux*V^2-(Kaux-1)*y_aux^2=1.
```

The transport and input ports retain

```
C=q-F-Z-alpha-2d*x>=0,  -q<W=C-Z<q,
(Kconstant+w)C+q-F-t(q-1)=1, t=transport_quotient,
u=2d*x+b, kappa=u+delta*Delta,
mu=W+a*kappa+rho*H>0, mu^2-Delta*kappa^2=1.
```

Since b<=d<=log2(q) and the supplied slacks are positive,

```
3<=u<q+b<=q+log2(q)<3q/2<R/2<A.                         (2)
```

In particular the input Pell root is positive without a comparison between rho and Gamma. The seven actual scaled factor values are `1,1,1,1,1,1,Delta`.

Write `c_j=psi_A(j)`. The main projection is

```
Gamma*H=chi_A(R)-(A-2)c_R-X=2c_R-c_(R-1)-X.             (3)
```

The +1 main norm and c>1 give `D<Ac`, because `D^2=A^2*c^2-(c^2-1)`. Consequently

```
0<Gamma<2c/H<c.                                       (4)
```

There is also a useful lower bound. The Pell recurrence gives

```
(2c_R-c_(R-1))-H*c_(R-1)
   =4c_(R-1)-2c_(R-2)>2c_(R-1)>X.
```

Here R>=3, so `c_(R-1)>=c_2=2A`, whereas X<a<A. Subtracting X and dividing by positive H proves

```
c_(R-1)<Gamma<c_R,      Gamma>2A>a.                   (5)
```

These strict inequalities concern a quotient forced by the actual native equations. They do not presume that it is an independently selectable real number.

## 3. Eight smaller outer ports

The bounds below exclude every port in the first group.

* `Jrep=(q-1)/(B-1)<q`, and each of F,Z,alpha is less than q by C>=0 and the other positive summands. Thus all four are below a<Gamma.
* `w=X/q<X<a` and `s=Y/q^3<Y<a`.
* From `k-hE=R+1>0` and c>kY,

  ```
  h<k/E<c/(YE)<2A*c_(R-1)/(XY^2)<c_(R-1)<Gamma.
  ```

  The last strict inequality before `c_(R-1)` uses `XY^2>2A=2Y(X+1)+4`, which follows already from X>=16 and Y>=4096.
* For the transport quotient, the actual compiler gives

  ```
  0<Kconstant=DC+B*DR<B^2<=q^2.
  ```

  The bound `0<DC,DR<B` is [78, Section 2, equation (8)](../../1980/FIXED_RAW_UNIVERSAL_78_PROOF.md). The [76 high-monomial correction](../../1980/FIXED_RAW_UNIVERSAL_76_PROOF.md) remains below the enlarged cell width, and the [half-binomial compiler](complete75_half_binomial_compiler.md) strengthens the no-carry coefficient bound; both retain this inequality. No arbitrary fixed numeral is substituted for this recipe bound. The retained transport equation, C<q and F>0 then give

  ```
  t<(Kconstant+w)*q/(q-1)+1
    <2*(Kconstant+w)+1
    <2*(q^2+w)+1<a<Gamma.
  ```

  For the last bound use `a=Y(X+1)>=q^3(X+1)`, q>=16 and w<X.

Thus none of `Jrep,F,alpha,transport_quotient,h,s,w,Z` can equal Gamma.

## 4. Five larger native ports

First `f^2=1+Delta*i^2*c^4` implies f>c^2>c>Gamma.

The supplied i also exceeds c; this is where normalized rank matters. The positive strong norm gives an index m with

```
f=chi_A(m), psi_A(m)=i*c^2.
```

The existing direct rank proof gives **R*c divides m**: strong divisibility first makes R divide m, and reduction of `psi_A(Rj)/c` modulo c, with `gcd(D,c)=1`, then makes c divide j. This argument uses the main/strong norms, not the old positive additive sigma. Since c>=3, m>=3R. Triplication yields

```
i=psi_A(m)/c^2 >= psi_A(3R)/c^2
  =4Delta*c+3/c>c>Gamma.                              (6)
```

For the positive auxiliary quotient, rearrange its retained definition:

```
T=(V+c+R*f^2)/(c*f)>R*f/c>c>Gamma.                    (7)
```

The inherited auxiliary positivity proof also excludes V=1 because `V=-c mod f` and f>2c. Its elementary gap gives `V>=2Kaux-1`. The auxiliary equation then implies y_aux>V, and therefore

```
y_aux>V>=2Kaux-1>c>Gamma.                            (8)
```

Finally put U0=XY^2. The first norm reads

```
tau_root^2=1+U0*(U0+1)*k^2.
```

Hence `tau_root>U0*k>k(Y+1)>c>Gamma`, using U0>Y+1. This excludes all five larger ports. It also explains why borrowing an auxiliary witness cannot simply replace the positive main quotient: these coordinates occupy disjoint forced size ranges.

## 5. The ratio slacks have the opposite parity

A is even and R odd, so D=chi_A(R) is even and c=psi_A(R) is odd. The first norm makes k even. Thus `eta=c-kY` and `zeta=k-eta` are odd. Meanwhile a and X are even and H is odd. The literal main root identity therefore makes Gamma even. Neither eta nor zeta can equal Gamma.

This argument is used after native recovery, not inferred from unrestricted supplied tuples.

## 6. The input modulus witness falls into a forbidden Pell gap

Suppose the chosen alias is delta=Gamma. Equations (4)-(5) show that its positive input coefficient lies strictly between two consecutive positive Pell coefficients.

For A>=3, `Delta=A^2-1>2A`, while `c_R<2A*c_(R-1)`. Therefore

```
kappa=u+Gamma*Delta>Delta*c_(R-1)>c_R.                (9)
```

Also

```
2Delta/H<A,
```

since `A(4A-5)-2(A^2-1)=(2A-1)(A-2)>0`. By (2), u<A<=D. Using (4),

```
kappa=u+Gamma*Delta<u+A*c_R<A*c_R+D=c_(R+1).          (10)
```

But the input +1 norm with positive root and coefficient requires `kappa=psi_A(v)` for an integer v>=1. Strict increase of that sequence excludes (9)-(10). This is a gap obstruction independent of input-index dominance; it does not assume v<R.

## 7. The equal-rho boundary

The last choice Gamma=rho is exactly the sigma=1 restriction of the already rejected [multiplicative-gamma83 chart](complete83_multiplicative_gamma_obstruction.md). It therefore has no positive zero. There is also a direct explanation of this particular boundary.

Let `E_A(j)=chi_A(j)-(A-2)psi_A(j)`, a strictly increasing sequence. The input and main projections give

```
E_A(v)=W+Gamma*H < X+Gamma*H=E_A(R),
```

because W<q<X. Hence v<R. The input discriminant congruences and (2), with R<A-1, exclude the even branch and force v=u. The projection congruence then makes `W=2^u mod H`; the range -q<W<q, the inequalities `2^u<X<a`, and H=4a+3 select W=2^u exactly.

The monic projection sequence from the cited obstruction has

```
G_0=G_1=0, G_2=1,
G_(j+2)(z)=z*G_(j+1)(z)-G_j(z)+2^j.
```

It is strictly increasing for j>=2 at every z=2A>=6, by induction in the recurrence. Thus `rho=G_u(2A)<G_R(2A)=Gamma`, contradicting equality. The sigma_old=0 signed pullback in (1) was never promoted to a strictly positive parent tuple.

## 8. Uniform exact degree and bounded evidence

The source-specific cancellation is retained even when the aliased port also occurs in other factors. The main norm expands as

```
D^2-Delta*c^2=(X+vH)^2+2ac(X+vH)-Hc^2.
```

Here a and H have degree 6, c degree 5, X degree 2, and every selected supplied v degree 1. The unique degree-18 term is `2acvH`; the other expanded terms have degree at most 16. Its leader is `8*a_top^2*c_top*v`, a nonzero polynomial for every valid fixed numeral slice. All other factors are literal unchanged polynomials. Their exact degrees remain

```
22,18,32,60,7,2,46.
```

Their product therefore has degree 187. Subtracting Delta of degree 12 cannot cancel that leader. The full leading homogeneous form is

```
32 Q^111 h v delta^2 i^4 (eta+zeta)^13 w^18 s^31
   * Nt_top * T^2 * f^2,
Q=Bm1*Jrep,
Nt_top=w*(Q-F-Z-alpha-twice_cell_bits*x)-transport_quotient*Q.
```

Substituting the selected port for v just increases its exponent; it cannot make this product zero. On the diagonal where all seventeen witnesses and x equal one indeterminate, the leading coefficient is

```
-2^18*(twice_cell_bits+3)*Bm1^111,
```

nonzero on every valid compiler slice. The naive gate recurrence still gives 197.

The fresh standard-library helper authenticates eleven source/proof files as inert bytes and JSON. It executes no predecessor source, old builder or archived verifier. It checks exact grammar coverage, all seventeen whole source reconstructions, private consumers, topological closure, all-row/free-port liveness, complete finalizers and full ledgers: **1,411 live gates** across the seventeen arrays. The private coefficient identity plus the literal unchanged descendants proves the all-ring pullback. Supplementary signed/rational evaluations check 272 whole assignments and 22,576 retained registers, including the outputs.

Two dense modular diagonal executions per source independently confirm the seven factor degrees, exact degree 187 and stated diagonal coefficient at diagnostic numerals. Eighteen small Pell components with A=3 through 8 and R in {3,7,11} check the quotient sandwich and input coefficient gap; six with R=3 also check a normalized strong extension at m=Rc and its size bounds. These components are not full compiler histories. No accepting native tuple or false ordinary input is materialized, and no proof of emptiness is inferred from bounded search.

The historical quotient-dominance and multiplicative-gamma reports supplied the existing native proof and the equal-rho boundary. The present conclusion is precisely the finite direct-identification grammar in Section 1. It does not resolve the independent-gamma83 language, exclude arbitrary nonlinear reuse, or change the universal84 bound.

Run the bounded CLI from any working directory with `--root ABS_WIP --expect ABS_JSON`, or use `--output FILE` to emit its deterministic receipt. All checks use explicit exceptions and recursive type-exact receipt equality under normal and optimized Python. The receipt and helper's `PINS` record all dependency hashes. This is a pinned-data research checker, not a maintained arbitrary-input API.

Fresh normal and optimized (`python3 -O`) exact receipt replays from working directory `/` both passed after final generation.
