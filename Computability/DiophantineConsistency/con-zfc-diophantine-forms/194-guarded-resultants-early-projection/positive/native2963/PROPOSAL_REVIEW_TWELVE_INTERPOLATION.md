# Twelve integer variables by intersective Pell interpolation

**The new ordinary arithmetic reductions pass review.** The complete release also passes in both normal and optimized Python. The three literal polynomials have these independently counted metrics:

| Domain | Variables | Operations | Exact degree | Literal equation |
|---|---:|---:|---:|---|
| Integers | 12 | 248 | 4,832 | `monotone_intersective12_degree4832.json` |
| Integers | 12 | 223 | 16,000 | `monotone_intersective12_degree16000.json` |
| Integers | 13 | 190 | 1,072 | `trace13_degree1072.json` |

The thirteen-variable point improves both the incoming root-fusion `195/1088` form and the separately reviewed reanchored `195/1072` form. The twelve-variable points give a further variable-count tradeoff. They do not dominate the existing ten-integer high-degree forms or the lower-degree families with more variables. The canonical thirteen-**positive** `90/51` page has a different domain and whole compact44 coefficient tuple; its coefficients must not be substituted into this source34 construction.

The accepted scope is the supplied ordinary unbounded arithmetic proof, composed with its pinned ordinary native/compiler and finite-refutation calibration. This review does not turn those dependencies into a new Lean theorem or an internal object-ZFC derivation. Lean remains paused.

## Provenance and full replay

The arrival is `docs/incoming/ConZFC_Twelve_Integer_Interpolation_2026-10-24.zip`, SHA256 `f44b903de17a70316787ff57562a3d8fe3bdec12791e266318cedb49e7125f72`. Its complete 138-file tree occupies 4,262,673 uncompressed bytes. All original members remain unchanged under `/tmp/proofs62ff-twelve-interpolation-review/original/con_zfc_trace_and_interpolation`. Independent full copies were used for normal and optimized replay.

Both invocations of the supplied `verify.py` passed: 137 release-manifest entries, 93 inherited entries, byte-identical reconstruction of all three graphs, all six actual coefficient values reconstructed from the 943 tiles, exact trace-carrier and degree identities, the two twelve-variable circuits, and their negative controls. The release entry point and its acceptance helpers use explicit exceptions, so the reported checks remain active under `-O`. Its finite modular comparisons are transcription diagnostics, not universal proofs.

The [focused read-only tool](tools/review_twelve_interpolation.py) authenticates every original member again, checks the whole six-port tuple against the previous saturated-integer review, recounts every live operation, proves additional local identities in a separate sparse ring, and exercises the interpolation boundary cases without constructing enormous auxiliary Pell witnesses. Its [normal receipt](data/twelve-interpolation-review.json) and [optimized receipt](data/twelve-interpolation-review-optimized.json) retain the complete release receipts.

The ports are precisely source34's `beta=2^1064921−1`, `K0`, `MC`, **already shifted** `MF`, `cone_A=2^1113`, and `cone_B=2^666104`. Their 615,883 minimal raw bytes match the previous source34 hashes. The inherited root-fusion files are unchanged. No unspecified universal index, consistency-dependent coefficient, compact44/54 port mixture, or hidden radical witness is used.

## Twelve-variable dependency order

The actual coordinates are `j,C,z,h,r,v,w,T,c,n,t,s`, all unrestricted integers. The common front has

```
J=6j+1, q=beta J+1, W=12w+4,
X=qW, Y=(2v+1)q³, a=(X+1)Y,
H=4a+3, Delta=(a+2)²−1,
I=s r c², Df=1+Delta I², Q=Delta² I²,
V=Df(c−R+4IT)−c, Da=(Q−1)(QV²−1).
```

The determinant `G` and strip product `eta*zeta` are combined as `O=G eta zeta−(t²−G−eta zeta+1)²`; the last radicand is `Dg=(3O−4)s²+1`. The intersective carrier uses

```
Pi(x)=(x²+31)(x³+x+1),
u=HT−(X+ac), Dm=1+Delta c²,
A+B d=H⁵ Pi((u+d)/H)  where d²=Dm,
S=I H⁵, Z=Sn−A.
```

The final polynomial is the complete five-root norm with radicands `B²Dm`, `S²w1²Da`, `S²w2²Df`, `S²w3²Dt`, `S²w4²Dg`. This notation expands to a division-free integer polynomial; the stored DAG contains no radical operation.

The soundness proof uses the following order.

1. **Uniform front facts.** On every signed assignment, `q` is even and `2 mod3`, `|q|≥16`, `|X|≥64`, `|Y|≥4096`, `H≠0`, `Delta>1`, and `Dm,Df,Dt>0`. No equation or guard has yet been imposed.
2. **Exclude the zero scale.** The quintic has no root in a real extension of degree at most two. Its quadratic-remainder coefficient `B` is strictly positive. If `S=0`, the whole polynomial becomes `(A²−B²Dm)^16`, which is nonzero. Thus `I,s,r,c` are nonzero at every zero. In particular `Q>1` and `Df>|c|+1`. The integer `c−R+4IT` is either zero, giving `|V|=|c|≥1`, or nonzero, giving `|V|≥Df−|c|>1`; hence `Da>0`.
3. **Recover the guard before squarehood.** All weights are nonzero before their eventual positivity is known: each is a product of odd integers. The four other radicands are positive. A negative `Dg` would contribute the only nonzero imaginary term of a vanishing norm factor, which is impossible. Therefore `Dg≥0`; since `s≠0`, this forces `O>0`, then `G>0` and `eta*zeta>0`.
4. **Obtain bound signs.** The determinant gives `F,C,alpha=q−F−C` the common sign of `q`. For positive `q`, both terms defining `R` are positive. For `q=−q1<0`, the first bracket is `q1(alpha1+C1)+C1>0`, and the mask term is positive because `J<0` and `MC−q1 MF<0`. Thus `R>0` before it is used in a majorant.
5. **Separate all signed subsets.** The auxiliary, strong and first roots have explicit positive bounds. The homogeneous estimate `B sqrt(Dm)/|S|<256(T²+c²+1)²` gives the first product weight. Successive weights exceed twice the sum of earlier magnitudes. Grouping by rational square class proves that all roots are rational, including when square classes are dependent. A zero guard root is simply omitted. Integer radicands then give integer roots; the adjacent-coefficient Pell descent makes the exposed auxiliary quotient integral.
6. **Restore the source.** Monicity of `H⁵Pi(x/H)` shows `H⁵|H⁵Pi(x/H) ⇒ H|x`, by the unique least prime-adic valuation if `v_p(x)<v_p(H)`. Applied to the norm relation this recovers the main integer congruence witness. The auxiliary witnesses are the literal integer polynomials

```
o=f(c−R+4IT),
j_aux=Delta s²r²c³(c−R)+4src Df T,
V=fo−c=c j_aux−R.
```

The larger-degree `223/16000` variant replaces the product weights by consecutive powers of one positive `W=2L+1`, where `L=1+B²Dm+Dt+Df+Da+Dg²`. Its initial nonvanishing and guard argument is unchanged; afterwards `L` bounds every needed root, so the same full-subset argument applies.

### The even strong multiplier is supported

One cannot restore the old odd multiplier by writing `(Delta*s*r−1)/2`; it need not be integral. The proposal instead supplies the needed rank argument directly. With positive Pell base `A0=|a+2|`, the main and normalized strong equations classify

```
|c|=psi_A0(p), |I|=psi_A0(m), |f|=chi_A0(m).
```

Because `c²|I`, strong divisibility first gives `p|m`. Write `m=pk`. The multiplication formula gives `psi_A0(pk)/psi_A0(p) ≡ k chi_A0(p)^(k−1) mod |c|`. The left side is divisible by `|c|`, and `chi_A0(p)` is a unit modulo `|c|`; hence `|c||k`, and consequently `|c||m`. The inherited first/main bootstrap already supplies `p≥25`, `|c|>2p,2R`, so `m>2p`.

The signed auxiliary step-down uses these rank bounds, `rho=Delta*|I|>1`, `rho²≡−Delta mod |f|`, `rho²≡0 mod |c|`, and the two restored congruences. It does not require `rho` to be odd: the auxiliary index is odd because `chi_rho(2k)≡(−1)^k mod rho`. Reading the retained signed proof with these exact hypotheses recovers the same rank, signs, power equation and post-power native decoder. Thus the even multiplier is a justified arithmetic generalization, rather than an assumed literal old-coordinate substitution.

## Interpolation and completeness

Three elementary properties of `Pi` are all used. The cubic discriminant is `−31`. For an odd prime other than31, either the cubic has a simple root, or its Frobenius is a three-cycle and its discriminant is a square, giving a simple quadratic root. At31 the cubic root3 has derivative28; at2, `−31≡1 mod8` supplies quadratic roots to every power of2. Hensel lifting and CRT therefore give roots modulo every nonzero integer. The cubic is irreducible over the rationals and the quadratic has no real root, proving the real-quadratic obstruction. Finally

```
Pi'(x)=5x⁴+95x²+(x+1)²+30>0,
B=5u⁴+10u²Dm+Dm²+32H²Dm+95H²u²+H²(u+H)²+30H⁴>0.
```

The central completeness lemma fixes `I,f` **before** choosing any requested residue of `T`. Here the canonical base `A0>1` is even, `Delta=A0²−1`, `R≡3 mod4`, and `c=psi_A0(R)≡R mod4`. For prescribed positive `N`, finite matrix order gives a positive even `m` with `4Nc²|I=psi_A0(m)` and `f=chi_A0(m)` odd. Put `lambda=4mf`.

For completeness, the valuation bound in this step admits a direct proof. At an odd prime dividing `I`, let `z_p` be the first zero index. If `p|Delta`, the recurrence modulo `p` gives `z_p=p`. Otherwise the norm-one unit over the finite quadratic algebra gives `z_p | p−1` or `p+1`, so `p` does not divide `z_p`. If `p|psi_A0(z_p)`, expansion of `(chi_A0(z_p)+psi_A0(z_p)sqrt(Delta))^k` shows that multiplication of the index by `p` adds exactly one to its ordinate valuation; a multiplier prime to `p` adds none. The leading binomial term has strictly smaller valuation than every higher odd term. Thus `v_p(I)≥v_p(m)` in both cases. At2, the doubling formula and parity of odd-index Chebyshev polynomials give exactly `v_2(I)=v_2(m)+v_2(A0)`. Since `gcd(f,I)=1`, these facts imply `gcd(lambda,4I²)|4I`.

For `alpha=A0+sqrt(Delta)`, the identity `alpha^m=f+I sqrt(Delta)` gives `alpha^(4m)=1−4f alpha^m mod f²`, and raising to the positive power `f` proves `alpha^lambda=1 mod f²`. The factor `f` is essential: for base2,index2, the proposed shorter period8 has coordinates `(1,35) mod49`, whereas period56 has `(1,0)`.

For every selected integer class `a mod I`, generalized CRT now gives a positive `ell` satisfying

```
ell≡R mod lambda,   ell≡R−4Ia mod4I².
```

It is `3 mod4`. With `rho=Delta I`, put `V0=chi_rho(ell)/rho`, an integer odd Chebyshev quotient. Its exact polynomial identities give `V0≡−c mod f²` and `V0≡−ell mod4I²`. The latter includes the required factor4. Since `c−R≡0 mod4`, the numerator `V0+c−f²(c−R)` is divisible by `f²` and congruent to `4Ia mod4I²`. It follows that

```
T=[V0+c−f²(c−R)]/(4If²)
```

is integral and is `a mod I`; the last reduction uses `f²≡1 mod I`. The corresponding auxiliary Pell equation follows from the defining Pell pair at base `rho`.

The complete witness order is therefore: canonical native outer data; a joint-positivity witness `t`; a guard Pell witness `s` (with the exceptional valid choice `s=1,g=0` when `O=1`); one strong pair `I,f` with `4sc²|I`; then an intersective residue solving `Pi(T+gamma)≡0 mod I`; then its interpolated `T`, the weights, and the final free integer `n`. No witness defining `I` depends on the residue subsequently requested. The norm center is assigned last and imposes no sign restriction on `n`.

## Trace companion and exceptional branches

For the thirteen-variable polynomial, initially `Y=qv` and `v=0` is allowed. The rational-part projection `Tr/[K:Q]` of a quadratic radical is its integer value if rational, and zero otherwise. For the auxiliary radical its rational-integrality property follows from adjacent-coefficient descent when `Q>1`, and directly from `Dy=1` when `Q=0`. Thus an integral radical sum with integer multipliers is divisible by the gcd of those multipliers, even if irrational terms cancel or the guard radical is imaginary.

Applied to the norm factor, this gives `M|Z` for `M=2q²`, without prior square extraction. Since `Z=M[H(n+V)+b0]+H(v−q²)` and `gcd(H,M)=1` (`H≡3 mod q`, `q≡2 mod3`, `H` odd), it follows that `v=q²(2s+1)`. The original large odd cubic scale is restored **before** using the unscaled guard. Guard recovery and the inherited large-scale root separation then give the original normalized integer kernel. The converse is the literal substitution `v=q²(2s+1)`, `n=gamma+f+tau+g+y−V−s`.

| Exceptional branch | Resolution |
|---|---|
| Twelve-variable `s=0`, `r=0` or `c=0` | `S=0`; nonzero real-quadratic quintic norm excludes it before the guard. |
| Negative determinant/strip guard | The sole imaginary radical first yields `Dg≥0`; nonzero `s` then forces strict guard positivity. |
| `Dg=0` | Allowed, including completeness at `O=1`; omit its zero term during separation. |
| Product bound factor initially negative | Each factor is odd and nonzero; positivity is only used after `R>0` is proved. |
| Negative `q,X,Y,c,I,H` | Uniform realness and source bounds use absolute values; signed native orientation occurs later. |
| Trace `v=0` | The field-trace congruence already excludes it, without guard assumptions. |
| Trace `c=0` | `Q=0,delta=−1,Dy=1` makes the trace valid; the later strict strip guard excludes `c=0`. |
| Cleared trace denominator `delta=0` | Impossible on every integer front assignment: `Q` is either0 or at least9. |

The focused checks additionally exercise 6,192 homogeneous-divisibility assignments, 583 valuation controls, 280 exact2-adic/CRT controls, 847 strong-index binomial controls, and modular interpolation at a 341-bit strong witness divisible by `4c²`. These reinforce transcription and branch handling; the universal proofs above, not those finite tests, justify the unbounded existence equivalences.

## Exact degree and comparison

For the product-weight polynomial the radicand degrees are `70,190,212,250,302`, with center degree35. Its unique highest contribution is the sixteenth power of the last radicand. Writing `q0=6 beta j`, `Y0=2v q0³`, `a0=24wv q0⁴`, and `I0=src²`, its leading form is

```
2^704 *3^16 *a0^544 *Y0^128 *I0^160 *c^64 *s^32 *h^64
  *(T²+c²)^64 *(s²+r²)^32 *T^64.
```

Consequently the coefficient at `j^2560 w^544 v^672 h^64 s^256 r^160 c^384 T^192` is exactly `2^5024 *3^3120 *beta^2560>0`. The selected powers choose one endpoint of each binomial, so cancellation is impossible. The exponents sum to4832.

For the shorter polynomial the radicand degrees are `70,410,570,786,1000`. Its leading part is `2^448 a0^1728 I0^1088 (4I0T−R0)^256`, where `R0=−q0³(12wC−q0z)`. Selecting the largest `T` power gives the coefficient `2^13056 *3^8640 *beta^6912` at `j^6912 w^1728 v^1728 s^1344 r^1344 c^2688 T^256`, of degree16000. These are exact ordinary leading-form arguments, separately corroborated by the supplied modular leading-slice diagnostics.

The trace polynomial's exact norm-cut calculation yields coefficient `2^976 *3^640 *beta^480` at `j^480 w^160 v^192 h^32 r^64 c^128 z^16`, of degree1072. It has the same attained coefficient as the separately reviewed reanchored guard, but removes five live gates from that `195/1072` tradeoff through scale recovery, direct main scaling, and the factored first norm. The new twelve-variable interpolation lemma is the larger conceptual change: it shares a guard witness and substitutes a homogeneous intersective congruence for a previously independent main coordinate, with a complete witness-selection order.
