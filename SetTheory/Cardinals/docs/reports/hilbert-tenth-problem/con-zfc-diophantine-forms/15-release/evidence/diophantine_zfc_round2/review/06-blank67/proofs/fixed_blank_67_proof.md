# Independent proof and source audit: the 67-operation blank-input polynomial

This note concerns the fixed-blank specialization of the pinned `complete84_scaled_strong_output` source. It is not a claim of a kernel-checked formal proof. The fixed numeral recipe is given in report.tex, Section 4, and data/k215_constants.json; it uses the blank-initialization local relation described below.

## 1. Candidate interface

All fifteen supplied variables are strictly positive integers:

`J,F,alpha,z,f,h,i,T,s,w,tau,eta,zeta,y,gamma`.

The program constants are `B-1,K,MC,MFsrc`, where `K=DC+B*DR`, `B=2^d`, `d>=4`, and `MFsrc=MF+B-1`. The native masks satisfy `0<MC,MF<B-1`, `MC=2 mod4`, `MF=4 mod8`, and `popcount(MC)+popcount(MF)=d`.

Define

```
q=(B-1)J+1, C=q-F-alpha,
X=wq, Y=sq^3, E=XY,
k=eta+zeta, c=kY+eta, a=E+Y,
A=a+2, H=4a+3, Delta=A^2-1=a^2+H,
D=X+ac+gamma H,
G=q(q-F)-C=(q-1)(q-F)+alpha,
R=G(q^2-1)+(MC+q MFsrc)J,
V=c(Tf-1)-Rf^2,
Kaux=(i Delta c^2)^2.
```

The six factors are

```
N0=tau^2-(XY^2)(XY^2+1)k^2,
N1=D^2-Delta c^2,
Naux=Kaux(V^2-y^2)+y^2,
Nk=k-hE-R,
Nt=(K+w)C+(q-F)-z(q-1),
Nstrong=Delta f^2-Kaux.
```

The polynomial is `P=N0*N1*Naux*Nk*Nt*Nstrong-Delta`. The expression uses ordinary integer polynomial operations only. In particular `q^3` denotes a fixed exponent, and no variable exponent is used.

## 2. Critical boundary and proof order

Since `a>0`, `Delta=(a+1)(a+3)>0` independently of the equation. Therefore `P=0` is equivalent to

```
N0*N1*Naux*Nk*Nt*Ns=1,
Ns=f^2-Delta i^2 c^4.
```

Every factor is consequently an integer unit. The inherited consecutive-product negative-Pell descent excludes `N0=-1`. Modulo 4, `Delta` is 0 or 3, excluding `N1=-1` and `Ns=-1`. Since `Kaux` is an integer square, its residue is 0 or 1 modulo 4; `Naux` is then congruent to `y^2` or `V^2`, so `Naux=-1` is impossible. Thus the four norm factors equal 1, while `Nk=epsilon` and `Nt=nu` with `epsilon,nu in {-1,1}` and `epsilon*nu=1`.

Weak transport gives only **C>=0**, not immediately C>0. Indeed

```
(q-F)-z(q-1)=1-F-(z-1)(q-1)<=0,
```

so `C<=-1` would imply `Nt<=-(K+w)<=-2`. The exact exceptional boundary `C=0, F=2, z=1, alpha=q-2` can make the transport factor -1. It must not be discarded before recovering the index sign.

At this stage, however, `q-F=C+alpha>0`, so `1<=F<=q-1`. Also

```
q <= G=q alpha+(q-1)C <= q^2-q,
0 < (MC+q MFsrc)J < (q-1)(1+2q)=2q^2-q-1.
```

Consequently

```
q(q^2-1) < R < q^4-q^3+q^2-1 < q^4-2,
R-2 > 3q+1,
E>=q^4>R+2,
a=E+Y>R+2.
```

These weaker estimates replace the old bound `R<q^4-q^3`. They are enough for the **auxiliary-quotient** proof whose recovered target is exactly R. One must not silently import an earlier generic coupled-target argument that used the larger margin for possible targets R-2 or R+2.

## 3. Positivity of the deleted auxiliary coordinates

From `Ns=1`,

```
f^2=1+Delta i^2 c^4,
Kaux=Delta(f^2-1),
f>c^2>2c, R<a<Delta.
```

Hence

```
Kaux-(Rf^2+c)
 = (Delta-R)f^2-Delta-c
 >= f^2-Delta-c
 = 1+Delta(i^2c^4-1)-c >0.
```

The auxiliary norm reads `Kaux V^2-(Kaux-1)y^2=1`. It excludes V=0. If `v=|V|>1`, elementary integer inequalities give `v>=2Kaux-1`: otherwise `v^2-1=(Kaux-1)(y^2-v^2)` is incompatible with `y>=v+1`. But `T>0` gives `V>-(Rf^2+c)>-Kaux`, excluding all negative V with |V|>1. Values V=+1 or -1 are excluded by `V=-c mod f` and `f>2c`, `c>2`. Thus V>0.

Restore the integer expressions

```
o=cT-Rf,
j=Tf-R Delta i^2 c^3-1.
```

They obey `of=V+c>0` and `jc=V+R>0`, hence o,j>0. In particular

```
V=of-c=jc-R.
```

This is established before invoking the rank theorem and without assuming an input bridge or C>0.

## 4. Recover the main index and the remaining unit signs

Put `P0=2XY^2+1`. The first norm classifies

```
tau=chi_P0(n), k=2 psi_P0(n), n>=1.
```

Since `P0=1 mod E` and `Nk=epsilon`,

```
2n=R+epsilon mod E,
2n=R+epsilon+vE, v>=0,
n>=(R-1)/2>=24.
```

The positive main root yields `D=chi_A(p), c=psi_A(p)`. As `P0>A` and `c>k`, one gets p>n, then `c>A Delta^2`, `c>2p`, and `c>2R` by the inherited elementary Pell growth estimates. Applying the generic strong-rank lemma to the positive ordinary multiplier `Delta*i` gives `f=chi_A(m)`, `c|m`, and `m>=c>2p`. The retained signed auxiliary step-down lemma applied to `V=of-c=jc-R` then gives **p=R**. The required bounds are `0<R<c/2` and `0<p<c/2`; no input equation enters this argument.

If v>=1 then `2n>=R-1+E>2R`, contradicting n<p=R. Thus `2n=R+epsilon`. If epsilon=-1, then `p=2n+1`. With `Q=chi_A(2)>P0` and `A>Y+1`, Pell duplication gives

```
psi_A(2n)=2A psi_Q(n)>=2A psi_P0(n)=A k,
c=psi_A(2n+1)>A k>k(Y+1),
```

contradicting `kY<c<k(Y+1)` from eta,zeta>0. Therefore epsilon=1 and nu=1. Now transport with value +1 excludes C=0, so **C>0** follows with no circularity.

## 5. Power and compiler recovery

The lower-ratio argument in `complete75_asymmetric_scale_tradeoffs`, Section 3, uses `X>=q>=16`, `Y>=q^3`, p=R odd, and the strict ratio; it does not need the old upper bound `R<q^4-q^3`. It proves `X<a` and `2^R<a`. The main-root congruence gives `X=2^R mod H`, hence `X=2^R` exactly. Since q divides X, q is a power of two. The large bound `R>3q` implies q^3 divides X, so the supplied w can be rescaled in the proof to restore the old symmetric half-binomial kernel. That kernel's hypotheses `q>=16`, `3q+1<=R<q^4` all hold.

The kernel therefore gives `v2(Y)=popcount(R)-2`, and `q^3|Y` yields the required population threshold. The order-of-two argument gives `q=B^N`. With Z=C, the shifted packing has

```
S'=C+qF-1,
T'=(MC J+1)+q(MF J-1),
R=(q^2-S')(q^2-1)+T',
0<S'<q^2.
```

The existing inverse-population theorem restores `(C-1) AND (MC J+1)=0` and `F AND (MF J-1)=0`. The first relation creates Start at the origin and forbids the distinguished End selector in every cell. There is no input marker and no input power to decode. The existing carry-free convolution, clean-band and anchor proof applies to the same native supports and forces an actual whole-cell temporal shift. Start's top/middle mismatch still excludes zero shift.

## 6. Blank-input finite-window semantics

Replace unary initialization by phases `L -> L or Q`, `Q -> R`, `R -> R`, all initially blank, with the unique initial head at Q. The actual first K215 action `0/0 -> write 1, move R, state 93` gives the distinguished Start window `[438,438,438,434,435,436,0,1,188]` with a fixed successor row; no prefix is added. From any global Start, cyclic horizontal scans find vertical boundaries on both sides: neither the L predecessor chain nor the R successor chain can traverse the Q and close without a boundary. This gives a proper finite strip, with exactly one initial head. Vertical-track propagation preserves the strip across all time rows.

The horizontal-boundary track is uniform inside that strip. Temporal translation is a permutation of the finite cyclic index set, so its initial boundary row eventually repeats; the first later boundary row is at finite distance. Every intervening row obeys the exact TM transition rule. The head cannot leave the strip and remains unique. The final interior row before the boundary permits a head only in the halt state. Hence the original blank-tape machine halts. Uniqueness of Start across the whole periodic tableau is not required.

A suitable distinguished selector 1 is the center-valid but globally impossible window E=`[0,438,0,0,437,438,0,437,0]`, in row-major order at time offsets -1,0,+1. Its prior-time center is H, its center and following-time center are V, and its right neighbor is H; the other five tiles are ordinary headless blanks. The center V rule holds. At its prior-time H, vertical propagation would require the bit 0 to equal the next cell V's bit 1. Thus excluding selector 1 removes no genuine tableau.

For completeness, a finite blank halting run has independently padded rectangular presentations, with one Start and no occurrence of that impossible selector. The fixed clause-band spacing in Section 11 ensures `2DC-DR=3 mod5` directly, without an optional coefficient correction. The ignored low dummy bit controls the actual packed index by `delta R=-Gamma B^i`, with `Gamma=r^e(q^2-1)[1+q(DC+B DR+B^h)]` a unit modulo dN; the Boolean subset lemma therefore gives `R=d h mod dN`. The detailed derivation and independent helical padding argument are in `blank_helical_proof.md`. The retained canonical margin proof gives `F+C<q`, hence positive alpha=q-F-C. The native-compiler canonical bound `2C+F<q/3` is more than sufficient. The existing kernel converse and auxiliary-quotient projection supply all remaining positive variables. Ordinary-input bridge coordinates are simply absent.

## 7. Exact arithmetic degree and ledger

The saved source `fixed_blank_67.json` has 67 live binary gates: 39 multiplications and 28 additions/subtractions. It has exactly the fifteen positive witness ports listed above and four fixed numeral ports. No comparison, divisibility relation, sign test, variable exponentiation, or extraction function is used to evaluate its polynomial. Static review of all 67 rows matches the six-factor formula in Section 1. The removed source rows are the complete input cone, its factor multiplication, the gamma split, and the redundant q-F-Z register; the only new row is C=q-F-alpha. Thus 84-18+1=67.

Here is a uniform exact-degree calculation, independent of the finite modular diagnostics. Give every witness degree one and every program constant degree zero. Put `Q=(B-1)J`, `k0=eta+zeta`, and `C1=Q-F-alpha`. Their top homogeneous forms give

```
X_top=wQ, Y_top=sQ^3, E_top=w s Q^4,
c_top=k0 s Q^3, a_top=E_top, Delta_top=a_top^2.
```

The factors have exact degrees 22,18,60,7,2,46 in their displayed order. To see the only significant cancellation, expand the main norm with `D=ac+X+gamma H` and `Delta=a^2+H`:

```
N1=2ac(X+gamma H)+(X+gamma H)^2-Hc^2.
```

Its unique top term is `8 gamma a_top^2 c_top`, of degree 18. The first factor has leader `-k0^2 w^2 s^4 Q^14`; the auxiliary factor has leader `i^2 k0^6 w^4 s^10 Q^34 T^2 f^2`; the index factor has leader `-h w s Q^4`; the transport factor has leader `w C1-zQ`; and the scaled strong factor has leader `-i^2 k0^4 w^4 s^8 Q^28`.

Their product is the nonzero degree-155 form

```
-8 Q^91 h gamma i^4 k0^13 w^13 s^26 T^2 f^2 (w C1-zQ).
```

For example, the monomial

```
J^92 h gamma i^4 eta^13 w^13 s^26 T^2 f^2 z
```

has coefficient `+8(B-1)^92`, which is nonzero on every valid compiler slice. The final subtraction of Delta has degree only 12 and cannot cancel this term. Thus the exact degree is uniformly 155. This proof does not treat identities that hold only at zeros as polynomial simplifications.

## 8. A division-free equation in 41 unrestricted integer variables

Only the first factor uses tau, through tau squared, and only the auxiliary norm uses y, through y squared. At a zero, neither can vanish: tau=0 gives `N0=-(XY^2)(XY^2+1)k^2<-1`, and y=0 gives `Naux=Kaux V^2`, which cannot be a unit because `Kaux>1`. Thus allowing tau,y to range over all integers is harmless: take their absolute values to recover a positive solution without changing the polynomial.

Every strictly positive integer is representable as

```
1+u^2+v^2+w(w+1),  u,v,w in Z.
```

Indeed, the expression is always positive. Conversely Legendre's three-square theorem applies to `4(n-1)+1`; this number is 1 modulo 4 and therefore has exactly one odd square in any three-square representation. Write the odd entry as `2w+1` and the even entries as `2u,2v` to get the formula. This argument also covers n=1.

Replace each of the thirteen other positive variables by its own disjoint copy of this quadratic expression, and retain tau,y as signed integer variables. The resulting explicitly specified ordinary integer polynomial has 13*3+2=41 variables. It has a zero over Z exactly when the original positive polynomial has a zero.

Its degree is exactly 310. The degree-155 leader in Section 7 does not contain tau or y. The thirteen positive replacements have homogeneous quadratic parts `u^2+v^2+w^2`; substitution by these disjoint forms is injective on the polynomial ring, as may be seen by setting every v,w to zero, which leaves the injective monomial map `x_i -> u_i^2`. Hence the degree-310 homogeneous part is nonzero. In particular the displayed nonzero monomial in Section 7 gives a monomial with each exponent doubled and coefficient still `+8(B-1)^92`.

## 9. The 68-operation polynomial of degree 123

The companion source replaces the auxiliary coefficient `Kaux=(i Delta c^2)^2` in the auxiliary norm alone by

```
Kred=Delta(f^2-1).
```

It retains the old Kaux in the scaled strong factor. One extra subtraction of 1 is paid, and the same number of multiplications is used: the full source has 68=39M+29A operations, the same fifteen positive witnesses, and the same four fixed numeral ports.

Let `Naux_red=Kred(V^2-y^2)+y^2`, and let P68 be the six-factor expression with that factor substituted. The exact polynomial identity is

```
P68-P67
 = (N0 N1 Nk Nt) Nstrong (Nstrong-Delta) (V^2-y^2).
```

This identity alone does not prove zero equivalence. At any integer zero of either source with Delta nonzero, cancel Delta to see that `Ns=f^2-Delta i^2c^4` is an integer unit. The modulo-4 argument in Section 2 excludes Ns=-1 independently of the other factors. Hence Ns=1, Nstrong=Delta, and Kred=Kaux. The two full outputs are then equal and both vanish. This proves equality of their complete integer zero sets on the stated positive domain; the same proof permits signed tau,y. No compiler theorem is needed for this local equivalence.

The reduced auxiliary norm has degree 28 instead of 60. Its leading term is `k0^2 w^2 s^4 Q^14 T^2 f^4`, while the other factor leaders remain those in Section 7. Consequently the uniform exact degree is 123, with full leading form

```
-8 Q^71 h gamma i^2 k0^9 w^11 s^20 T^2 f^4 (w C1-zQ).
```

The monomial `J^72 h gamma i^2 eta^9 w^11 s^20 T^2 f^4 z` has coefficient `+8(B-1)^72`. Thus the degree is attained on every valid fixed compiler slice. Applying Section 8's signed-coordinate and division-free positivity conversion gives a polynomial in 41 unrestricted integer variables of uniform exact degree 246.

## 10. Six-equation systems and lower-degree sums of squares

The same positive solution set has the six-equation presentation

```
N0=1, N1=1, Naux=1, Nk=1, Nt=1, Nstrong=Delta.
```

Use Naux_red in place of Naux for the reduced-coefficient variant. Sections 2-4 prove that every full polynomial zero satisfies these individual equations. Conversely the equations make the product of the six factors exactly Delta, so they imply the polynomial equation. Thus no sign ambiguity is hidden in the system formulation.

The 67-operation source uses five products to combine its six factors and one final subtraction. Deleting these six finalizer gates leaves a 61-operation system evaluator, with 34 multiplications and 27 additions/subtractions. Its largest residual degree is 60. The corresponding reduced-coefficient version has 62 operations, with 34 multiplications and 28 additions/subtractions; its largest residual degree is 46 (the scaled strong residual).

If a single polynomial of lower degree is preferable, sum the squares of the six residuals. For six comparisons the fully charged finalizer uses six subtractions, six squares and five additions, adding 17 operations. The first system therefore gives a 78-operation single polynomial of exact degree 120; its unique largest residual is the degree-60 auxiliary norm. The reduced system gives a 79-operation single polynomial of exact degree 92; its unique largest residual is `Nstrong-Delta`, of degree 46. Their highest terms are nonzero squares over the integers, so there is no cancellation. All four variants retain the same fifteen positive witness variables and the same program constants.

## 11. Simplified compiler geometry and fixed modulo-5 correction

For a tile alphabet of size `a_tiles=439`, or more generally `a_tiles=3 mod4`, the coefficient recipe uses the following revised native layout:

```
T2=T1+4Emax+2,
L is a power of 5 with L>T2+2Emax+1.
```

The original clean-band proof requires only `T2-T1>2Emax`, `L-(T2-T1)>Emax`, and `T2+Emax<L`. These are all satisfied, with stronger margins than before. All low copy and anchor supports remain below T1; the two clause bands remain disjoint; their mask populations, the number of dummy positions, and the unique anchor difference are unchanged. The extra allowed upper dummy bit still has expanded support within `[0,Emax]`, so its rotation/spill argument also remains unchanged.

Since the inner bit count b is a power of 5, `Rrad=2^b=2 mod5`. The new gap has residue 2 modulo 4, hence `Rrad^(T2-T1)=-1 mod5`. Each paired clause contribution cancels individually:

```
c_e (Rrad^(T1-e)+Rrad^(T2-e)) = 0 mod5.
```

The remaining four explicit DC monomials are at exponents `3*a_tiles`, `H+a_tiles`, `8M0`, `24M0`; DR is `Rrad^H`. Since `a_tiles=3 mod4`, they yield

```
DC = 2+3 Rrad^H+1+1 = 4+3 Rrad^H mod5,
2DC-DR = 8+5 Rrad^H = 3 mod5.
```

Thus the five-adic dummy-control coefficient is automatically a unit. The conditional extra high monomial is unnecessary; no enormous clause coefficient sum must be evaluated modulo 5 to decide whether to add it. The old coefficient bound with its allowance for that optional monomial remains a valid conservative bound when the monomial is absent.

## 12. Scope of this audit

The argument validates the mathematical reduction under the authentic compiler recipe and retained Pell lemmas. It does not prove minimality, does not materialize the astronomical fixed numerals, and is not a new Lean/Rocq certificate. The source emitter must separately verify its operation ledger, coordinate list, numerical program recipe, and exact degree. The pivotal correction is to retain C=0 through the pretyping stage and exclude it only after Nk=Nt=+1.

