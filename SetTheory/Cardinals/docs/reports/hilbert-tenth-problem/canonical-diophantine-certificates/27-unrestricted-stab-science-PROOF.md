# Fixed-arity unrestricted finite global stabilization

Research proof and exact-source packet, 4 October 2026. This is not an article. It extends the prior binary-stabilization certificate to unrestricted toppling multiplicities while keeping the same raw eight-field physical input. Mathematical and exact-source reviews are recorded separately; the inherited constructive Pell dependency is stated explicitly.

## 1. Exact represented language

A positive ordinary input `InputPlus` represents the natural integer `InputPlus−1`. Seven right-associated Cantor pairings decode exactly

`(p−1,q−1,r−1,T,d−1,e−1,f−1,D)`.

Here `p,q,r,d,e,f` are positive. Write `T` in radix 32 with `pqr` declared slots, in order `x+p y+pq z`; every digit must be in 0–5. Write `D` with `def` declared slots, in order `x+d y+de z`; every digit must be in 0–15. Nonzero higher slots are forbidden; declared leading zero slots are allowed. The configuration on the six-neighbor lattice Z³ is the corresponding `(p,q,r)`-periodic background plus the finite nonnegative patch at `[0,d)×[0,e)×[0,f)`.

A legal toppling at a site of height at least six subtracts six there and adds one at each neighbor. **Finite global stabilization** means that some finite sequence of legal topplings ends with every lattice height at most five. It does not mean an infinite, locally finite stabilization. The empty sequence is allowed. There is no multiplicity restriction on a site.

The emitted polynomial has one positive ordinary input and 3,262 strictly positive existential witnesses. Its zero set over that domain represents exactly valid physical codes with finite global stabilization. There are 1,897 residuals and 14,571 counted binary arithmetic gates. Its total degree is exactly 18, independently verified by exact sparse normalization and a separate specialization check. These syntactic figures do not depend on any input dimension, padding size, radix precision or toppling count.

“Unrestricted” removes the binary-odometer restriction on this fixed input class. It does not silently enlarge the external patch-digit alphabet beyond 0–15 or replace the physical instance with a newly quantified input. No target is supplied or certified.

## 2. Finite-support supersolutions suffice

Let η be a natural configuration on Z³. Suppose `u:Z³→N` has finite support and

`F(v)=η(v)−6u(v)+Σ_(w∼v)u(w) ≤ 5`

at every vertex. The certificate additionally requires `F≥0`, which does not weaken the existence equivalence because actual legal stabilization has a natural endpoint.

Every finite legal prefix has toppling-count function `m≤u`. Otherwise take its first step that would exceed `u` at a site v. Immediately before that step, `m(v)=u(v)` and `m(w)≤u(w)` at every neighbor. Its current height is therefore

`η(v)−6u(v)+Σ_(w∼v)m(w) ≤ F(v) ≤ 5`,

contradicting legality. This proof uses no prior claim that the proposed u is a legal odometer.

Starting from η, choose an unstable vertex whenever one exists and topple it. Each finite prefix has at most `Σ_v u(v)` topplings. Thus the procedure cannot keep finding unstable vertices beyond that finite bound and must stop at a globally stable configuration. Its genuine legal odometer `u*` satisfies `u*≤u`. Conversely the odometer of any finite legal global stabilization is a finite-support natural u with a natural stable F of the displayed form. The usual least-action comparison between two stabilizing legal sequences gives uniqueness of `u*`, but uniqueness is not used to interpret a supplied witness.

Hence existence of a finite natural stabilizing supersolution is equivalent to finite global stabilization. The supplied u need not be `u*`: two adjacent sites initially of height five, with zero elsewhere, are already stable, but assigning u=1 at those two sites gives another natural stable endpoint. That witness overfires both sites and is still a valid existence certificate.

## 3. Fully expanded arithmetic primitives

Every mathematical natural variable below is a strictly positive witness minus one. Variables required to be at least two are a positive witness plus one. A positive slack enforces a strict inequality. All equations are integer polynomial equations; the final single polynomial is the sum of their squared residuals.

### 3.1 POWER

The relation `POWER(b,n,o)` means `o=b^n` for `b≥2,n≥0`. It is paid by 15 explicit equations. Put `k=n+1` and `m=bo`. Choose `a,β≥2`; positive `w,M,g,x,y,u,v,s,t,qb,qv,S`; and natural `δwb,δwk,δyk,α1,α2,σ1,σ2,τ1,τ2,ρ1,ρ2`. Require

1. `x²=1+(a²−1)y²`
2. `u²=1+(a²−1)v²`
3. `s²=1+(β²−1)t²`
4. `β=1+4y qb`
5. `β+uα1=a+uα2`
6. `v=y² qv`
7. `s+uσ1=x+uσ2`
8. `t+4yτ1=k+4yτ2`
9. `y=k+δyk`
10. `w=b+δwb`
11. `w=k+δwk`
12. `M=m+S`
13. `a²=1+((w+1)²−1)(wg)²`
14. `2ab=M+b²+1`
15. `x+Mρ1=y(a−b)+m+Mρ2`

The external theorem is precisely the inherited constructive Pell characterization from mathlib4 commit `ac77769fabe23cb237559e7f56578dbead91499f`, `Mathlib/NumberTheory/PellMatiyasevic.lean`, theorems `matiyasevic` and `eq_pow_of_pell`; pinned source SHA256 `993760c797ad0ff66fa77064a616fce779550bc745cbf6c44e04f392fd0bed0a`. The prior approved packets authenticate this dependency. The present work does not run Lean or substitute a generic MRDP existence theorem.

Equations 1–9 select the indexed Pell solution at positive index k. The last six supply the constructive power characterization. Equation 13 and positive g imply `a>w≥b`, so the integer difference `a−b` agrees with the natural subtraction in the source theorem. Paired natural quotients express the congruences in both directions. Each invocation has 25 positive internal leaves plus its separately positive output, and 70 body arithmetic gates.

### 3.2 Sub and AND

For naturals M,U, `Sub(M,U)` means that each binary one-bit of U occurs in M. Set

`ell=2^(M+1)`, `position=ell^U`, `expansion=(ell+1)^M`.

These are three separately expanded POWER calls. Choose natural q,h,r and positive digit/remainder slacks; require

`expansion=(q ell+2h+1)position+r`,
`2h+1+digitSlack=ell`,
`r+remainderSlack=position`.

The strict bounds extract exactly the radix-ell digit indexed by U, which is `binom(M,U)`. All binomial coefficients are below ell. Over F₂, `(1+z)^M` factors as the product of `(1+z^(2^j))` for the one-bit positions j of M; distinct subsets have different exponents. Its U coefficient is odd precisely when U's one-bits are contained in M. The relation includes M=U=0 and rejects U>M without a separate comparison.

For `W=X AND Y`, choose natural A,C and require `X=W+A`, `Y=W+C`, together with `Sub(X,W)`, `Sub(Y,W)` and `Sub(A+C,A)`. The first two subtractions have no binary borrowing. The last Sub is equivalent to A and C having disjoint binary supports: for natural C, adding it to A preserves every bit of A exactly when no carry chain starts at a common bit. Thus W contains every shared bit and no other bit. All three Sub calls are paid.

For `b≥2,n≥0`, `G(b,n)` is the unique natural satisfying `(b−1)G+1=b^n`; its power and one equation are paid.

### 3.3 SPREAD

For power-of-two b, positive n, `s≥n+1`, and `0≤V<b^n`, let

`C=b^(s−1)`, `E=C^n`, `P=b^n`,
`(C−1)G1+1=E`, `(bC−1)G2+1=EP`,
`out=(V G1) AND ((b−1)G2)`.

The source includes three POWERs, both geometric equations, the AND, a natural gap `s=n+1+gap`, and a positive range slack `V+slack=P`.

Writing `V=Σ_(i<n) v_i b^i`, the product `VG1` has terms at exponents `i+(s−1)j`. They are distinct: a nonzero multiple of `s−1≥n` cannot equal a difference of two indices in `[0,n)`. All coefficients remain below b. Such an exponent is a multiple of s exactly when i=j, since it is congruent to `i−j` and `|i−j|<s`. The full-digit mask retains precisely those diagonal blocks. Therefore

`SPREAD(V;b,n,s)=Σ_(i<n) v_i b^(s i)`.

This is a proved polynomial graph, not an array operation or a digit oracle hidden in the output source.

## 4. The same external input, now at adjustable precision

Let `Jt=G(32,pqr)`. Validate the raw tile by natural bitplanes T0,T1,T2 with

`Sub(Jt,T0)`, `Sub(Jt,T1)`, `Sub(Jt,T2)`, `Sub(Jt,T1+T2)`,
`T=T0+2T1+4T2`.

Each bitplane has a 0/1 digit in the declared slots. The unweighted sum T1+T2 has digits at most two, so the last Sub excludes joint 2- and 4-bits. Exactly digits 0–5 result. Validate the raw patch by `Sub(15G(32,def),D)`, giving exactly digits 0–15 in its declared slots.

Choose a positive precision L and a paid power `b=32^L`. Choose positive `h` with `16h=b`. Thus `h=2^(5L−4)≥2`, and `c=h−1=b/16−1` is the low-`(5L−4)`-bit mask.

Use exactly two additional paid calls:

`T_b=SPREAD(T;32,pqr,L)`,
`D_b=SPREAD(D;32,def,L)`.

They enforce `L≥pqr+1` and `L≥def+1`, separately, and certify that these are the same physical digits now packed in radix b. No different quantified tile or patch has replaced the raw ordinary input.

In particular, because both volumes are positive, the complete certificate forces `L≥2` and `b≥1024`. Later carry arguments are valid under the weaker `b≥32`, including equality at the smallest allowed POWER precision L=1 considered in isolation. This distinction avoids an unnecessary assumption or a misleading minimal-radix claim.

## 5. Paid period-aligned padded geometry

Choose `tx,ty,tz≥2` and define

`hx=p d tx`, `hy=q e ty`, `hz=r f tz`,
`A=2hx`, `B=2hy`, `C=2hz`, `N=ABC`.

The finite box has lower corner `(−hx,−hy,−hz)` and side lengths A,B,C. The lower corner is at zero phase for each period. A local site `(x,y,z)` has positional index `x+A y+AB z`. Every side length is at least four. The input patch lies strictly inside: e.g. `hx≥2d` gives its x support from local hx through hx+d−1, below A−1; the other axes are identical.

Two tile SPREADs use respectively

- radix `b^p`, length qr, stride `A/p=2d tx`
- radix `b^(Aq)`, length r, stride `B/q=2e ty`

Their result is `T_emb=Σ t(x,y,z)b^(x+Ay+ABz)` over the original tile. For the second strict input-range obligation, the first result has exponents `x+A(y+qz)`, with `x<p≤A`; each z block fits below its next `Aq` position, so the entire intermediate stream is below `(b^(Aq))^r`.

Multiply by the three paid repetition factors

`G(b^p,A/p) G(b^(Aq),B/q) G(b^(ABr),C/r)`.

The coordinates `x+p i`, `y+q j`, `z+r k` uniquely span the full box, so each position receives exactly one tile digit. The result H is the correct periodic background in every box slot, with digits 0–5.

Two patch SPREADs analogously use radix `b^d`, length ef, stride `A/d=2p tx`, then radix `b^(Ae)`, length f, stride `B/e=2q ty`. Multiply by the paid `b^(hx+Ahy+ABhz)`. The result Δ is the original physical patch at its actual coordinates. Its digits are 0–15. Thus H+Δ has digits at most 20, already below b.

All four spatial stride gaps are explicitly enforced; choose tx and ty large enough for both margins belonging to their axes. All corresponding bases, powers, geometric products and range bounds are included in the DAG. The independent extents may grow without bound and eventually contain any given finite support strictly inside.

## 6. The bounded but nonbinary finite supersolution

Use paid powers `X=b^A`, `Y=X^B=b^(AB)`, `Q=Y^C=b^N`. Define natural J,jx,jy,jz by

`(b−1)J+1=Q`,
`b²((b−1)jx+1)=X`,
`X²((X−1)jy+1)=Y`,
`Y²((Y−1)jz+1)=Q`.

Because A,B,C≥4, these uniquely give `J=G(b,N)`, `jx=G(b,A−2)`, `jy=G(X,B−2)`, `jz=G(Y,C−2)`. Set `I=b X Y jx jy jz`. Unique positional coordinates show that I has exactly one low bit in every strict-interior slot and zero bits on the entire six-face shell.

Choose a natural U and impose

`Sub((h−1)I,U)`.

Because b is a power of two and `h−1=2^(5L−4)−1`, the mask has precisely its low `(5L−4)` bits in each interior slot, without overlap. Thus U uniquely packs a natural u with

`0≤u(v)≤c=b/16−1`

in the interior, and u=0 on the shell and outside the box. In particular `U<Q`. This bound is established from the mask alone, before examining balance; there is no circular no-carry assumption.

Introduce natural nx,ny,nz satisfying `b nx=U`, `X ny=U`, `Y nz=U`. The lower faces are zero, so these exact divisions exist. The six neighbor streams are

`bU, XU, YU, nx, ny, nz`.

The upper faces being zero prevents overflow and spurious forward row/plane wrap. The lower faces being zero prevents spurious backward wrap and discarded nonzero low blocks. Consequently these streams contain exactly the six nearest-neighbor u values at each box site.

Any site outside the box has no positive-u neighbor: a neighbor across the boundary lies on the zero shell. The patch is inside the box, so all exterior sites retain their original stable periodic height. No separate infinite conjunction or uncharged exterior condition is needed.

## 7. Stable endpoint and one exact balance

Choose natural endpoint bitplanes Z0,Z1,Z2 and impose

`Sub(J,Z0)`, `Sub(J,Z1)`, `Sub(J,Z2)`, `Sub(J,Z1+Z2)`.

Then `F=Z0+2Z1+4Z2` has exactly N digits in 0–5, allowing leading zeros. Assert the single polynomial equation

`H+Δ+bU+XU+YU+nx+ny+nz = 6U+F`.

Every left coefficient, considered before any positional carrying, is nonnegative and at most

`20+6c = 3b/8+14 < b`.

Indeed its margin is `b−(3b/8+14)=5b/8−14≥6` when b≥32. Every right coefficient is nonnegative and at most

`6c+5 = 3b/8−1 < b`,

whose margin is `5b/8+1≥21`. At b=32 the respective worst cases are 26 and 11. All shifts are supported in the N slots. Therefore both sides are canonical radix-b expansions and equality is equivalent to every coordinate equation `η(v)+Σu(w)=6u(v)+F(v)`. There are no unexamined top carries or borrows.

Extend only u by zero outside the box, and extend the decoded endpoint by F(v)=η(v) there. The shell and exterior argument supplies the same stabilizing equations globally. Section 2 now proves finite global stabilization.

## 8. Completeness with no horizon or fixed odometer bound

Suppose the valid physical configuration has a finite legal global stabilization. Let u* be its finite-support natural odometer, and `m=max_v u*(v)` (take m=0 for the empty sequence). Choose an integer L with

`L≥pqr+1`, `L≥def+1`, `32^L≥16(m+1)`.

Such an L exists. It makes `u*(v)≤b/16−1` at every site. Choose tx,ty,tz large enough that its finite support lies strictly inside the box and all four spatial SPREAD gap requirements hold. These choices do not invalidate the precision inequalities. Pack u* and its actual stable natural endpoint into U and the endpoint bitplanes.

Every displayed domain, mask, geometric identity, division, and balance then holds. The explicit arithmetic macros are complete on their stated domains, supplying the remaining strictly positive witnesses. No toppling-time tableau is introduced, no time horizon is quantified, and no a priori bound on u* is assumed: the precision is a witness allowed to grow past every finite maximum.

This proves the two directions for unrestricted finite global stabilization on the unchanged raw eight-field physical input.

## 9. Well-founded domain audit

The proof of every macro domain precedes use of its semantic conclusion:

1. Positive descriptor dimensions give positive volumes and valid base-32 geometric calls. Raw bitplanes and patch are natural adapters; every external Sub receives naturals
2. Positive L gives `b=32^L≥32` through POWER at constant base 32 and natural exponent. The separate equation `16h=b` then gives h≥2 and `h−1≥0`
3. Every SPREAD length is a positive dimension or product of positive dimensions. Its explicit stride equation implies `s≥n+1`, hence `s−1≥1`, before the copy-base POWER is interpreted. Its other powers have positive exponents. The positive range slack supplies the required strict range
4. All spatial exponents are sums/products of positive dimensions and extents; every spatial radix is b or a previously established power at least two. The geometric lengths are positive. The second reshape's stricter input range follows from the already established first reshape
5. J,jx,jy,jz are natural adapters; their equations identify geometric sums with nonnegative lengths. I, `(h−1)I`, the supersolution, and endpoint masks are therefore natural before Sub is used
6. In every AND the input products and masks are natural. All partition terms are separately natural. In each Sub, the first POWER has base two and exponent `M+1≥1`; its output is at least two. Its next two POWER bases are that output and that output plus one, and the exponents U,M are natural
7. Each POWER's shifted index `n+1` is positive. Its a and β are at least two; all listed quotient and slack domains are explicit adapters. No statement above relies on applying the constructive power theorem to a negative exponent or base below two

## 10. Exact source and ledger

`build_stabilization.py` is newly authored and self-contained. It imports only the Python standard library. It emits `evidence/polynomial-dag.json`: one free positive input, declared positive witness leaves, fixed integer constants and only binary `+`, `−`, `*` gates. Powers, bit predicates, spread and geometry are metadata labels for expanded equations, never executable primitives in that DAG. Construction loops iterate only fixed syntax and fixed emitted lists.

The literal source has:

- 3,262 positive witnesses and 1,897 equality residuals
- 14,571 gates: 5,734 multiplications, 4,997 additions, 3,840 subtractions
- Body: 3,837 multiplications, 3,101 additions, 1,943 subtractions, totaling 8,881
- Sum of squares: 1,897 multiplications, 1,896 additions, 1,897 subtractions, totaling 5,690
- 117 POWER, 28 Sub, six AND, six SPREAD, five geometric and two stable-bitplane metadata records
- No dead gate or witness

The witness decomposition is

`117·26 + 28·5 + 6·3 + 6·4 + 5 + 8 + 6 + 3 + 2 + 3 + 4 + 4 + 3 = 3262`.

After the four macro terms come: five separate geometric outputs; eight physical descriptors; six internal Cantor codes; three tile bitplanes; precision and sixteenth-radix witnesses; three box-padding leaves; J,jx,jy,jz; U and its three negative shifts; three endpoint bitplanes.

The equality decomposition is

`117·15 + 28·3 + 6·2 + 6·4 + 7 + 5 + 1 + 1 + 4 + 3 + 1 = 1897`.

After macro internals come: seven Cantor equations, five geometric equations, tile reconstruction, exact-sixteenth equation, four box-mask equations, three neighbor divisions and balance.

The POWER decomposition is `84+18+5+1+5+1+3=117`: 84 within Sub; 18 direct in SPREAD; five in geometric sums; one adjustable radix; five tile/patch row/plane/z bases; one patch shift; three box bases.

The frozen DAG SHA256 is `8622585bcafaf9b3aee84e12f229beb17a33d27d6f1bf0b6cb6bc956ee4ac759`. The builder SHA256 is `47c2e5c63ea6eceef26c4bd117ca8a195eb5180e00482f9d9384a7705788fb2c`. Fixed literals are free under this stated accounting convention; no minimality or universal-operation improvement is claimed.

The independent exact source audit verifies every residual, macro interface and exposed port, and the complete sum-of-squares topology. Its exact degree-nine residuals are precisely `patch.shift.eq8`, `.eq9` and `.eq11`, each with leading homogeneous part `−4 p q r d e f tx0 ty0 tz0`, where `tx0,ty0,tz0` are the raw positive padding witnesses. Consequently the degree-18 homogeneous part of the output is `48(p q r d e f tx0 ty0 tz0)²`, which is nonzero. Normal and optimized replays from `/tmp` are byte-identical; eleven deliberately damaged sources are rejected in both modes.

## 11. Separators, verification and limits

The valid zero-tile instance with one patch digit 12 requires at least two origin topplings: after only one, its height is still at least six. Two origin topplings globally stabilize it with origin height zero and six neighbors of height two. The new certificate accepts this instance, which has no binary stabilizing odometer. A second fixture uses patch digits `[12,4]` and legal sequence `origin,origin,neighbor`, with counts `[2,1]`.

The adjacent `[5,5]` fixture has true odometer zero but permits a supplied supersolution with two entries one. This specifically tests the distinction between existence and exact odometer recognition. Conversely the uniform height-five background plus one added chip has no finite global stabilization: for any finite-support u, sum `F−5` over a finite set containing the patch, support and neighboring sites. Toppling contributions cancel and the sum is one, while stability would make every summand nonpositive. It can still have a legal target firing, so finite stabilization is not being conflated with the repeated-target relation.

`check_semantics.py` checks both raw conversions, the full paid tensor construction, masks, shifts, endpoint bitplanes and packed balance on stable, repeated and nonleast-supersolution fixtures, including a nonconstant periodic tile. It separately checks 1,440 finite SPREAD cases, 6,056 capacity-bit cases and carry inequalities for 40 precisions, including b=32 in isolation. These are corroborating finite tests, not a complete enormous Pell witness or a proof by enumeration.

Separate mathematical and exact-source audit directories record independent conclusions. This packet does not claim finite-fold or unique full witness fibers: arbitrary larger precisions and prisms already give infinitely many. It makes no real-witness equivalence claim. No universal loader, raw-program compiler, U15 execution, upstream arithmetic schedule, or theorem-prover run is supplied. No computability corollary is asserted without a separately authenticated reduction for this exact finite-global-stabilization language; a first-firing alarm would not suffice.
