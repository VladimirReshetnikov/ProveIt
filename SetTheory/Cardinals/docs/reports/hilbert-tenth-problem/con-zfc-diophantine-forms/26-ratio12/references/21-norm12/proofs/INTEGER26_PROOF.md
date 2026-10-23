# Twenty-six unrestricted integer unknowns

This proof uses the final definitions and semantic descent in
`NORM12_INDEPENDENT_AUDIT.md`, Sections 1--8. It is independently written
from the circuit generator. All coefficients must come from one whole
authentic blank compiler tuple, with the shifted high-mask port.
The proof is ordinary mathematics formalizable in ZFC, not a new
proof-assistant theorem.

The resulting product has 26 integer unknowns, 168 binary arithmetic
operations, and exact degree 2657. The system has three equations with
164 operations and maximum degree 2640. The SOS has 171 operations and
degree 5280.

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

