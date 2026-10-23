# Independent proof review: a free positive ratio coordinate

Reviewed proposal by root, 23 October 2026. This is an ordinary mathematical proof review, not a Lean/Rocq compilation. It examines the numerical Jones ratio adapter independently of the native source compiler. The inherited references are `con-zfc-sparse-pell-124c07c0b7.zip`, `nine/PROOF.md` Sections 3--5, and `ZFC_Diophantine_Selective_Quadratic_2026-10-23.zip`, `nine/PROOF.md` Sections 1--6, present in ProveIt snapshot `4b4349064a750ba6347293b55874a7f92abdd0db`.

## Conclusion

**The proposed coordinate replacement is valid.** Replace the old nonnegative slack `phi` in `C=2R+1+bw+phi` by a free strictly positive coordinate `C`. Use the shifted numerator with `M=W^2`, where `W=bw`. The positivity-first norm below forces `m>0` before any ratio theorem is invoked, and that inequality recovers the omitted guard `C>2R+1+W`. The old slack is then a positive integer. All unconditional radical majorants survive for free `C>=1`.

The extension of the calibrated sparse source from `b>=2` to `b>=1` is also valid. Its `b=1` branch has no zeros, and the ratio/compiler completeness direction still chooses `b>=2`. For the original `H` formula, all nine free coordinates may be taken strictly positive with no natural-to-positive shifts, including `n`, because the norm completeness proof produces `n>0`. For the CRT formula, the new `j` remains naturally nonnegative: keep its shift or supply a separate cofinality proof before replacing it by an unshifted positive coordinate.

## 1. Exact hypotheses and registers

Assume integers

`R,N>=8`, `1<=b<=min(R,N)`, `g,h,s,w,i>=1`, `Gcap>0`, and free `C>=1`.

Put

```
U=N^2*w, Y=N^2*s, M0=R*Y,
P=2*M0^2*U, K=R+1+h*(P-1),
A=M0*(U+1), B1=2*R+1, W=b*w, J=4*A-5,
Q=3*W*C-2*(W^2-1),
D=(A^2-1)*C^2+1,
k=i*J*C, E=k*D*C,
F=(A^2-1)*E^2+1,
G=A+F*(C*D+1-A).
```

Choose either:

- Original form: `j>=1`, `H=B1+j*C`, `u=J*F`, `v=Q*F+J*(H-C)`.
- CRT form: `j>=0`, `H=C+F*(B1+j*C)`, `u=J`, `v=Q`.

Finally define

```
I=(G^2-1)*H^2+1,
a0=(P^2-1)*K^2+1,
a1=64*D*F*I,
m=(K^2-4*(C-K*Y)^2)*Gcap-8*g*K^2,
V0=P*K,
T=k*(8*D^2-4*D-1), V1=T*G*H,
M=W^2,
Omega=u*m,
Theta=u*(n+M)+v-Omega*(V0+V1),
F9=(Theta^2-Omega^2*(a0+a1))^2-4*Omega^4*a0*a1.
```

Here `n>=0` suffices for soundness; completeness below gives `n>0`.

**Correction to an unnecessary proposed premise:** no inequality `R>=N` is needed. The source contract supplies `b<=R` and `b<=N`, and those suffice.

## 2. All bounds needed before m is positive

We have `U,Y>=64`, `P>1`, `K>=P+R>1`, and `A>=2`. Since `b<=N`,

`A=RY(U+1)>U=N^2*w>=b*w=W`.

The free coordinate only needs `C>=1` to give

`D>=A^2>W^2`, and `D>C^2`.

Consequently `W*C<D`: both `W` and `C` are strictly smaller than `sqrt(D)`. Also `C*D+1-A>0`, so `G>A>=2`. Both alternatives give `H>=1`; the original form has `H-C=B1+(j-1)C>0`. The identity for `F` yields `F>=A^2`. Thus `a0,a1` are positive integers on every allowed assignment, including ones with very small free `C`.

The first majorant is unconditional:

`V0^2-a0=K^2-1>0`.

For the second, write `E=kDC`. Since `(A^2-1)C^2=D-1`,

`DF=(D-1)k^2D^3+D`.

The exact identity

`T^2-64DF=(8D+1)k^2-64D=8D(k^2-8)+k^2`

is at least `8D+9>0`, because `k=iJC>=3`. Therefore

`V1^2-a1 = [(8D+1)k^2-64D]*(GH)^2 + 64DF*(H^2-1)>0`.

In particular `sqrt(a0)<V0` and `sqrt(a1)<V1`. These statements do not require `C>B1+W`, a square condition, divisibility, or `m>0`.

For later completeness, a convenient coarse lower bound is `T>=9D`. Indeed

`8D^2-4D-1-3D=(D-1)(8D+1)>=0`,

and `k>=3`. Hence `V1>=9DGH>5DH`.

## 3. Shifted numerator positivity and quotient bound

For the CRT form,

`u(n+M)+v = Jn+(J-2)W^2+3WC+2 > 0`

for every `n>=0`, since `J>=3`. For the original form, after division by the positive `F`, the numerator equals the same expression plus the positive term `J(H-C)/F`. Thus it too is strictly positive. This is the essential repair when the free coordinate makes `Q` negative.

For `W>=1`, `Q<=3WC`, so `Q/J<=WC<D`. In the CRT form,

`M+v/u=W^2+Q/J<2D<V1`.

In the original form,

`M+v/u=W^2+Q/J+(H-C)/F<2D+H<V1`.

The last inequality follows from `V1>5DH` and `D,H>=1` (here both are in fact much larger). These are upper bounds; no assumption that `Q` or `v` is already positive is needed.

## 4. Soundness of the new norm

If `m=0`, then `Omega=0` and `F9=Theta^4>0` by the shifted numerator positivity. Thus any zero has `m!=0`.

For a zero with `m!=0`, the four real linear factors provide signed real roots `r0^2=a0`, `r1^2=a1` satisfying

`n+M+v/u=m*Z`, where `Z=V0+V1+r0+r1`.

The strict majorants imply `Z>0` before any claim of root rationality. The left side is positive, so `m>0`.

Now `m>0` implies `4(C-KY)^2<K^2`, hence

`C>K(Y-1/2)>2K>=2(P+R)>2R+1+W=B1+W`.

The last strict inequality uses `P>W` and integer positivity. One direct proof is `P=2R^2Y^2U>U>=W`, hence `P>=W+1`. Thus `phi=C-B1-W` is a positive integer, and the omitted Jones guard has been recovered without circularity.

Also `C>K`, and `P<A^2` because `(U+1)^2>2U`. We have `D>C^2`, `F>=A^2`, `I>=G^2>=A^2`. Therefore

`DFI>A^4*C^2>P^2*C^2>P^2*K^2>a0`,

so in particular `a1>a0`. The rational sum `r0+r1=Theta/Omega` cannot vanish. If `x=r0+r1`, then

`2*x*r0=x^2+a0-a1`.

Thus each `r_i` is rational and therefore integral, since its square is an integer. The squarehood of `a1=64DFI` implies squarehood of `DFI` by the same rational-root argument. Then `Z` is an integer, and the selected factor equation forces `u|v`.

The original form now satisfies every hypothesis and all four conclusions required by the original Jones ratio interface, with reconstructed positive `phi`.

For the CRT form, `F=1 mod J` and `F=1 mod C` hold algebraically. Define

`j_old=1+((F-1)/C)*B1+F*j`.

It is a positive integer and gives exactly `H=B1+j_old*C`; moreover `F|(H-C)`. The condition `J|Q` therefore implies the old combined condition `JF | QF+J(H-C)`, as `gcd(J,F)=1`. Thus the same Jones interface applies.

## 5. Completeness and strict positivity of n

Start with source witnesses and the inherited Jones completeness theorem. Retain its `C=B1+W+phi` as the new free positive coordinate. Retain its other variables in the original form.

For the CRT form, let `z=(H_old-C)/F`. The old `j_old>=1` makes `z>0`. Since `F=1 mod C`, `z=B1 mod C`; since `0<B1<C`, uniquely `z=B1+jC` with `j>=0`. This gives the new CRT parameter with identical `H`.

The ratio conditions give `m>=1`, integral positive square roots of `a0,a1`, and `u|v`. Choose those roots and put

`Z=V0+V1+r0+r1`, `n=mZ-M-v/u`.

The earlier unconditional bound `M+v/u<V1<Z` proves `n>0`, and all quantities in its definition are integers. This produces a zero of the norm. Consequently one may demand strictly positive `n` without losing any represented source solution.

This is an existence reduction, not a claim that every old norm witness maps by subtracting `W^2` to a positive new witness. Completeness chooses a new `n` from the indicated positive-root factor.

## 6. The calibrated sparse source also permits b=1

For the selected parity-calibrated source retain the exact constants and coding data in the incoming selective-quadratic report. In particular `Mcoef=2^2134927`, `a=8192Mcoef`, `B=a*b^2`, `Wcode=183`, `Qcode=5190`, `Kcode=5556`,

`L=2b B^5741`, `N=c B^2966`, `c=2^(15*kappa/2-10)`, `kappa=2134940`.

Every unconditional source bound still holds at `b>=1`:

- `B>=a=8192Mcoef`, so `B-1>Mcoef`, `B>128`, and `B>4b`.
- The positive leading coefficient of `Dcode(B)` still dominates its signed lower terms.
- `Mcode=B^184-1-(b-1)ell` has nonnegative base-B digits and lies below `B^184`; at `b=1` it is simply `B^184-1`.
- Under `g<4bB^183`, integrality gives `g+1<=4bB^183` and `g<B^184`, exactly as before.
- The proof of `Jcode<Z/64<Z`, where `Z=B^5557`, only needs `B>128` and `B>2`.
- `Scode+Tcode<2B^5741<=L`, with strict final inequality retained even at `b=1` because the first comparison is strict.
- `R,N>=8` and `b<=R,N` follow from the same explicit large positive formulas; none requires `b>=2`.

If a final zero has `b=1`, the ratio theorem says `b=2^0`. The low-mask condition then gives `g & (B^184-1)=0`, while `0<g<B^184`; impossible. Thus the enlarged parameter domain introduces no represented zero at its extra boundary.

For parity calibration let `b=2^k`, now including `k=0`, and `v=kappa+2k`. The same calculation gives

`pop(Tcode)=206v-31k-22`,

`log2 L+pop(Tcode)+1=5947kappa+11864k-20=2 log2 N`.

The exponent identity is valid at `k=0`. Completeness starts with a nonzero source witness (the source has `p5(0)=1`), and chooses a power of two `b` larger than all its coordinates, so `b>=2` automatically.

Therefore the positive-coordinate version may use `b` itself, with no `b=epsilon+1` gate. Together with free positive `C` and the reconstructed `n>0`, the original-H branch has the nine directly positive coordinates `b,g,h,s,w,C,i,j,n`.

## 7. Scope

This review establishes the new numerical adapter and its compatibility with the stated inherited source contract. It does not independently certify every carry identity, native compiler theorem, or K215/ZFC endpoint; those remain the same explicitly identified dependencies. Literal circuit implementation, operation count, exact degree, and actual coefficient bindings require separate audits. No global minimum follows from this reduction.

## 8. Audited extension: remove the top bit and halve the block

A further independently reviewed source reduction is valid. Keep all existing source coding definitions `Scode=S`, `Tcode=T`, but replace

```
L_old=2b B^5741,
R_old=L_old^2+(S+T)L_old+L_old-1-S,
N_old=2^16012040 B^2966
```

by

```
L=b B^5741,
R=(S+T)L+L-1-S=(L-1)S+L(T+1)-1,
N=2^16012039 B^2966.
```

All coefficients remain fixed integers. This change does not rely on `R>N^2`; the inherited numerical ratio interface has no such hypothesis.

### Unconditional source hypotheses

The prior argument gives `S,T>=0` for all outer assignments and `L` extremely large. Therefore `R>=L-1>=8`, `R>=b`, and `N>=max(8,b)`. Positivity of `Dcode(B)`, `Jcode`, and `S` is unchanged.

### Required binary block bounds

Under the ratio-derived bound `g<4bB^183`, use `N0=B^184` and `Z=B^5557`. The existing inequalities give `g<N0` and `Jcode<Z/64`; hence

`S<N0*(Z/64+1)<N0 Z/32=B^5741/32`,

because `Z>64`. Also `Mcode<N0` and `(B-2)A_targets<B^5191`, so

`T<N0*(1+B^5191)<N0 Z/32=B^5741/32`.

For the last bound, `B^366>64` is much more than sufficient. Consequently

`S+T<B^5741/16<L=bB^5741`

for every `b>=1`. The inequality needed to separate the binary blocks is therefore strict even at the new boundary `b=1`.

### Valuation identity and threshold

When `b=2^k`, `B=2^v`, write `L=2^u`, where `u=k+5741v`. Since `S+T<L` and `S<L`, the new R has exactly the two nonoverlapping blocks

`R=(S+T)L+(L-1-S)`.

Thus

`pop(R)=pop(S+T)+u-pop(S)=u+pop(T)-carry(S,T)`.

The nonnegative carry count vanishes exactly when `S&T=0`. The mask population remains `pop(T)=206v-31k-22`, with `v=kappa+2k`. Therefore

`u+pop(T)=5947*kappa+11864*k-22`.

With `kappa=2134940`, the new fixed factor in N is

`2^(15*kappa/2-11)=2^16012039`,

and

`2 log2 N = 5947*kappa+11864*k-22`.

Legendre's valuation identity `v2(binomial(2R,R))=pop(R)` now yields precisely the same mask-disjointness test `N^2 | binomial(2R,R) iff S&T=0`. Both directions use the same source bounds, so soundness and completeness remain valid.

### Independent degree and leading-coefficient check

On the all-variable diagonal t, the source heads are

`S_top=4 a^5374`, `T_top=a^5375`, `L_top=a^5741`,

at respective degrees 10750,10750,11483. Hence the new rank has degree22233 and positive head

`rho=a^11115*(a+4)`.

The threshold has degree5932 and head `nu=c*a^2966`, with `c=2^16012039`. For the original-H free-C tail, independent degree propagation gives

| Register | Degree |
|---|---:|
| A | 45963 |
| D | 91928 |
| F | 367714 |
| G | 459643 |
| H | 22233 |
| a0 | 320246 |
| a1 | 1423394 |
| m | 184221 |
| u | 413677 |
| Omega | 597898 |
| V1 | 711697 |
| V1^2-a1 | 1147610 |

The exact defect identity in Section2 shows that its leading term is the first positive summand, so there is no unresolved leading cancellation. The corrected inner polynomial is

`E0^2 - 2E0 Omega(V0+V1) + Omega^2[(K^2-1)+(V1^2-a1)+2V0V1]`,

where `E0=u(n+W^2)+v`. The term `Omega^2*(V1^2-a1)` uniquely has largest degree2343406. Its square uniquely determines the final degree

`4686812`.

The generic diagonal head of the final polynomial is

`2^94*rho^104*nu^400*a^732`.

Substituting the two source heads gives the positive exact head

`2^94 * a^2343092 * (a+4)^104 * c^400`.

This independent algebraic calculation should be compared with the literal circuit's own exact-degree auditor. It is not a replacement for operation-count, source-binding, or emitted-DAG checks.
