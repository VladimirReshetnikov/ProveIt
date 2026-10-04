# Independent arithmetic audit of the rational-rotation family

Date: 4 October 2026

## Finding

**PASS within the stated arithmetic scope.** Sections 7–8 of the frozen proof correctly establish the rational decision procedure, the fixed-machine polynomial-time corollary, and the displayed existential-positive-integer certificate with exactly `1+80J` witnesses, `1+43J` residual equations, and sum-of-squares degree exactly 12. I found no arithmetic defect requiring correction.

This is a conventional mathematical audit. Its conclusions about physical validity are conditional on the exact chamber and orbit characterization proved in the earlier sections, which are outside this worker's independent audit. The time calculation in Section 7.2 was checked algebraically conditional on the primitive durations and transfer description. This audit does not certify an emitted arithmetic circuit, run Lean, or independently establish the provenance of a mathlib commit.

## Frozen inputs and method

- Audited proof: `/workspace/shared/five-signal-rotation-family59-20261004/PROOF.md`
- Final proof SHA-256: `14c3d694d9e0c21f3ad3b125c0d1f2bbf47793e1283c9314aa3855ef60c89fc5`
- The final proof contains the new Section 7.1 polynomial-time corollary and renumbers the clock discussion to Section 7.2. The earlier preliminary hash `4406adeda09919b826747063f70d7e356158d39230af11ad06f019e6234a6adb` was superseded and is not the final audited version.
- Pell dependency read as inert text: `/workspace/shared/five-signal-certificate58-release-20261004/science/sources/pell-source.lean`
- Its SHA-256: `993760c797ad0ff66fa77064a616fce779550bc745cbf6c44e04f392fd0bed0a`
- The same hash was separately verified for the packet copy `inert_sources/pell-source.lean`.
- Main dependency statements inspected: `Pell.matiyasevic`, beginning at source line 760; `Pell.eq_pow_of_pell`, beginning at line 860. Their constructive proofs and nearby definitions were read as text, including the positive-base construction and strict modulus bound.

No author program, upstream executable, physical simulator, saved collision schedule, or Lean process was executed. No author files were changed. Shell operations were limited to reading, listing, hashing, and creating this independent report. No finite-case numerical test is being substituted for an all-parameter proof.

## 1. Gaussian quotients, signs, and the denominator lemma

Write `z=a-ib`. Primitivity implies that each prime divisor `p` of `c` divides neither `a` nor `b`, and `p` is odd. In the two-dimensional algebra `(Z/pZ)[i]`,

`z² - 2az = -(a²+b²) = 0`.

Induction gives `z^n=(2a)^(n-1)z` for `n>=1`. Its two coordinates are nonzero modulo `p`, since `2`, `a`, and `b` are nonzero modulo `p`. This argument is valid even when this algebra has zero divisors; it uses no field division. Consequently **each** integer numerator coordinate of `z^n` is coprime to `c`, and the joint reduced denominator of `(z/c)^n` is exactly `c^n`. This establishes the claim for composite and prime-power denominators as well as prime denominators. At `n=0`, the pair is `(1,0)` with denominator 1; the proof correctly treats that case separately.

For a contact `p=(r/t,s/t)` and normalized input `(A/(3D),B/(3D))`, ordinary Gaussian division gives

`eta = t[(rA+sB)+i(rB-sA)] / [3D(r²+s²)]`.

This is exactly the displayed `U,V,Q`, and `Q>0` because `D>0` and the contact is nonzero. There is no unmentioned nonzero-input-numerator assumption: at the center `U=V=0`, the primitive joint quotient is `(u,v,q)=(0,0,1)`.

Let `C+iS=(a+i|b|)^n` and `epsilon=sign(b)`. Then

`(a-ib)^n = C-i epsilon S`.

Thus matching the forbidden inverse power requires `u=C` and `v=-epsilon S`. The acceptance equation correctly uses `(v+epsilon S)²`. Negative `a`, either sign of `b`, and `n=0` are covered.

## 2. Primitive reduction and extraction for composite c

The first three outer equations express `(U,V,Q)=h(u,v,q)` with `h,q>0`. The Bézout equation `e1*u+e2*v+e3*q=1` forces `gcd(u,v,q)=1`, including cases with zero or negative numerator coordinates. Hence `h` is precisely the positive gcd of `U,V,Q`, and `q` is the least common denominator of the two reduced rational components. The Bézout formulation is sufficient without requiring any pairwise coprimality of `u,v,q`.

The equations `r=ck+s` and `s+t=c`, with `k>=0` and `s,t>0`, say exactly that `r>0` and the remainder of `r` upon division by `c` lies in `{1,...,c-1}`. With `q=c^n r`, this is the unique decomposition obtained by dividing repeatedly by the *whole integer* `c`. It does not assert that `r` is coprime to `c`; that stronger assertion would be false and is unnecessary. For example, a leftover factor sharing some but not all of a composite `c` is correctly permitted and yields `r>1`.

If an actual inverse-power denominator is `c^m`, this decomposition forces `n=m,r=1`. If `q` is not an exact power of `c`, it forces `r>1`. Therefore the single final nonzero sum can use `r-1` as the complete denominator-mismatch test. No prime factorization and no additive valuation law is required.

## 3. Bounded radix extraction

The four slack equations enforce `-P<=C,S<=P`. For the true Gaussian-power coefficients, the same bounds hold because their complex modulus is `c^n=P`.

Set `beta_rad=4P+2c+1`. The map sending `i` to `beta_rad` in `Z/(beta_rad²+1)` respects `i²=-1`; it therefore sends the true Gaussian power to the ordinary power in the second POWER module. This gives the extraction congruence for all integers `a`, including negative ones.

If a second bounded pair satisfied that congruence, the difference `dC+beta_rad*dS` would be a multiple of `beta_rad²+1` with

`|dC+beta_rad*dS| <= 2P(1+beta_rad) < beta_rad²+1`.

The final inequality follows from `beta_rad>4P` and `P>=1`. The multiple must be zero. Then `|dC|<=2P<beta_rad` forces `dC=dS=0`. Thus this is an injective bounded decoding, not an ambiguous residue representation.

The second ordinary POWER base is positive before its semantic conclusion is used. Since `|a|<=c-1`, `|b|>=1`, and `P>=1`,

`a+|b| beta_rad >= 4P+c+2 > 2`.

This removes any sign-of-base issue or circular use of the POWER equivalence. The first base is `c>=5`.

## 4. Literal POWER module versus the inert Pell statements

### 4.1 Index characterization

In the source statement of `Pell.matiyasevic`, substitute:

- source `a,k,x,y` = module `alpha,k0,x_p,y_p`
- source auxiliary `u,v,s,t,b` = `u_p,v_p,s_p,t_p,beta`

The module has `alpha,beta>=2`, `k0=e+1>=1`, and `y_p>=k0`. Equations 1–3 are the three Pell identities. Equation 4 gives `beta congruent 1 mod 4y_p`; equation 5 gives `beta congruent alpha mod u_p`; equation 6 gives `y_p²` dividing the positive `v_p`; equations 7–8 give the remaining two congruences. Equation 9 gives `k0<=y_p`. These are precisely the nonzero-index branch of the source theorem. The source alternative `x=1,y=0` cannot be relevant because `y_p>=k0>=1`.

The source uses natural truncated subtraction in its Pell equations. For natural integers, `X-Y=1` with truncated subtraction is equivalent to the ordinary integer equation `X=Y+1`; therefore the module's displayed equations have exactly the needed meaning. There is no unchecked switch of subtraction conventions here.

The resulting conclusion is the intended index equality `(x_p,y_p)=(xn(alpha,k0),yn(alpha,k0))`.

### 4.2 Power characterization

In the positive-base, positive-index branch of `Pell.eq_pow_of_pell`, substitute:

- source `n,k,m` = `B0,k0,m0`
- source auxiliary `w,a,t,z` = `w,alpha,M,g`

Equations 10–11 encode `B0<=w` and `k0<=w`. Equation 12 encodes the essential strict bound `m0<M`, not merely a weak bound. Equation 13 is the auxiliary Pell identity; equation 14 is `2 alpha B0=M+(B0²+1)`; equation 15 is the required congruence modulo `M` once the Pell pair has been identified.

Because `g>=1` and `w>=B0>=2`, equation 13 forces `alpha>w>=B0`. Thus the module's ordinary expression `alpha-B0` is nonnegative and agrees with the source's natural subtraction. The source theorem gives `B0^k0=m0=B0*out`; cancellation of the positive `B0` gives `out=B0^e`. This covers `e=0` via `k0=1` without needing a disjunction in the displayed module.

### 4.3 Existence and positive domains

Conversely the constructive source theorems give the module witnesses when `out=B0^e`. The stricter positive domains do not discard those solutions:

- `w` is positive because `w>=B0>=2`
- `g` cannot be zero, as the auxiliary Pell identity would then force `alpha=1`
- the Pell x-coordinates are positive; `y_p>=k0>=1` and `v_p>0`
- `v_p=y_p² q_v` gives `q_v>0`
- `beta>1` and `beta congruent 1 mod 4y_p` give `q_b>0`
- `t_p` cannot be zero, since `t_p congruent k0 mod 4y_p` and `1<=k0<=y_p<4y_p`
- the strict source modulus bound gives `J_p=M-m0>0`
- every signed congruence quotient can be represented by a difference of two natural multiples, exactly as in the displayed paired variables

Thus both directions of the 15-equation POWER equivalence are accounted for, including the natural/positive boundary cases.

## 5. Radius gate and exact validity predicate

For positive integer input gaps, `Delta=9HD²-K(A²+B²)` is an integer with the same sign as `rho²-||w||²`. The shared equation `Delta=d` with `d>=0` rejects all outside-circle inputs.

- If `Delta>0`, the term `d²` makes every final acceptance sum strictly positive, so the other arithmetic witnesses can be chosen without excluding any interior input
- If `Delta=0`, the final acceptance sum is positive exactly when at least one of `r-1,u-C,v+epsilon*S` is nonzero
- By the preceding reductions, simultaneous vanishing is exactly equality to the forbidden inverse power for that contact

Conjoining the acceptance conditions for all distinct contacts excludes precisely their union of backward orbits. Conversely, the gcd, Bézout, canonical factorization, true bounded Gaussian coefficients, ordinary congruence quotient, and POWER existence statements explicitly supply all witnesses for any valid input. At the center, `q=1,n=0,r=1,u=v=0,C=1,S=0`, so it is not spuriously excluded; its radius witness is also strictly positive.

## 6. Independent count and total-degree ledger

For each contact, the outer witness domains consist of:

- 6 naturals: `n,k,L_C,H_C,L_S,H_S`
- 6 positive integers: `h,q,r,s,t,J_acc`
- 8 signed integers: `u,v,e1,e2,e3,C,S,kappa`, represented by 16 positive leaves

One POWER module contains 13 directly positive leaves (including its output), 2 positive leaves encoding `alpha,beta>=2`, and 11 natural leaves, each changed to one positive leaf. This is `13+2+11=26`, not 26 plus a separate output. The first and second output leaves are respectively `P` and `T` and are not counted a second time.

Hence the native input certificate has one shared radius leaf plus `6+6+16+26+26=80` per contact: exactly **`1+80J` positive witnesses**. Its equations are one radius residual plus 13 outer and twice 15 POWER residuals per contact: exactly **`1+43J` equations**.

The domain adapters are affine, so do not increase degrees. All fixed machine/contact quantities are coefficients. The outer residuals have degree at most 3; the maximum comes from `kappa*(beta_rad²+1)`. POWER residuals have degree at most 6 even for the second base, which is affine in the independent leaf `P`. In particular, expanding equation 13 produces degree-six leading term `-w^4 g²` in its residual; its square has nonzero degree-twelve part. The top homogeneous part of the entire sum of residual squares is a sum of real polynomial squares, so it cannot cancel identically. Since `J>=1`, the total degree is **exactly 12**, not merely at most 12.

The optional Cantor transport was also checked: its two equations are the standard successive pairing identities for `pair(g1-1,pair(g2-1,g3-1))=z-1`. It adds three positive gap witnesses and one natural/positive-adapted inner-code witness, and two quadratic residuals. Therefore its separate ledger `5+80J` witnesses and `3+43J` equations is correct and the degree stays 12.

No uniqueness or finite-fold assertion follows, and the proof explicitly avoids one. In particular, the positive-pair encodings of signed integers already allow infinitely many representations of a single signed witness.

## 7. New polynomial-time corollary

The qualification that the machine and all its contacts are fixed is sufficient and important. For total rational-input bit length `L`, fixed-size rational linear and quadratic expressions have numerator and denominator lengths `O(L)`, including unreduced inputs. Gcd reduction and formation of the primitive joint denominator remain polynomial-time operations on integers of `O(L)` bits.

The exact-power test repeatedly divides by the fixed `c`. There are at most `log_c(q)=O(L)` successful divisions, and no factorization is used. If `q=c^n`, then `n=O(L)`. Every intermediate coefficient of `(a-ib)^k`, for `0<=k<=n`, has absolute value at most `c^k<=q`, so its bit length is still `O(L)`. Repeated multiplication by the fixed Gaussian integer uses `O(L²)` bit operations with ordinary fixed-coefficient arithmetic. Reduced-input numerator comparison has the same bit bound. The number of contacts is fixed.

An `O(L³)` upper bound is conservative and supported by schoolbook division plus the elementary Euclidean algorithm. The proof correctly does not extrapolate this to uniform compilation costs, growing rotation/contact parameters, or the search for enormous Pell witnesses. No large ordinary power from the Diophantine certificate is required by the rational membership algorithm.

## 8. Clock arithmetic, conditional on the physical primitive lemmas

The duration upper bound sums correctly: `2K0` translation gadgets at less than `6D` each, two transfers totaling `2D`, and, when present, homothety duration less than `6(1+lambda)D` yield `(12K0+8+6lambda)D`. For `lambda<1`, summing the geometric bound proves finite total duration. The rational linear-functional formula `T(z)=ell*(I-N)^(-1)z` is valid because the eigenvalues of `N` have modulus `lambda<1`, and rational coefficients give rational time on rational input.

For `lambda>=1`, the two transfers alone provide the lower bound `2D_n=2lambda^n D_0` per macro, whose sum diverges. Thus the clock classification follows from the supplied physical durations without an arithmetic gap.

## Conclusion and limits

The frozen Sections 7–8 pass this independent arithmetic audit. The crucial edge cases are explicitly covered: composite `c`, zero quotient coordinates, negative `a`, either orientation, exponent zero, natural versus ordinary subtraction, strict acceptance/modulus inequalities, and positive-domain adapters.

The certificate is a literal finite polynomial formula for each fixed chamber. This audit does not assert that an arithmetic frontend has been emitted, that a source-specific gate count has been verified, that witnesses are small or unique, or that the proof was checked by Lean. Those limitations agree with the claim boundary in the audited proof.
