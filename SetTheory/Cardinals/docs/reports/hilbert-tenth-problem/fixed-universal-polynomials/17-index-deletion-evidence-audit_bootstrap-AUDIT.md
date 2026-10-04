# Independent audit of the first-index bootstrap reduction

## Verdict

**PASS for the stated reduction, not for first-index deletion soundness.** I found no circular reuse of the deleted first-index equation, no incorrect normalized-to-ordinary transfer, and no counterexample to the conclusions of `PROOF.md`.

On the full strictly positive candidate zero set, with the entire inherited admissible compiler recipe, the proof establishes

- `p=R ≡ 3 (mod 4)` and `R/2<n<R`
- `d=2n-R` odd, `1≤d≤R−2<E`
- `(k−R−1) mod E=d−1`
- the forced rational inverse `(k−R−1)/E` is positive
- that inverse is integral exactly when `d=1`, equivalently `2n=R+1`

This does **not** establish that `d=1` for every full zero. The operation-bound conclusion remains 85; the 81/82-operation arrays remain candidates. All finite checks below are supplementary and are not a proof by exhaustive testing of the full source.

## Scope and data discipline

I read the two saved source arrays and parent receipts as inert JSON. I did not run an upstream program, evaluator, arithmetic schedule, verifier, compiler, or archive. `check_bootstrap.py` is newly authored code: it performs static row/port comparisons and separately evaluates independently written Pell formulas. Its exact output is `checks.json`.

The parent receipt hashes agree exactly with the hashes in the scout:

- normalized85: `e7ddc113f96cde37efc9d1973daffa5e4cef221db2c1d1c6ad1cf1772cd59edc`
- ordinary86: `f46dd919a038b6dd646489e64585331de30b8c91a380cf9611afbf288122a9a6`

The inert comparison verifies that each candidate deletes exactly `hpm1`, `index_difference`, `norm_index`, and `norm_product`; it redirects only `all_units` from `norm_product` to `norm_four`. The free ports and witnesses change only by deleting `h`. The full lists contain 17 witnesses and retain ordinary input `x` separately. The paid ledgers are 46M+35A=81 and 45M+37A=82.

Thus the abstract first/main/input/auxiliary/transport/strong interface in the proof matches the retained source. In particular `X=wq` and `Y=sq³`, not the older symmetric scaling, and source register `A` is the mathematical discriminant `Delta=(a+2)²−1`.

## 1. Unit signs and outer bounds are independent of the missing factor

There are six retained integer factors with product 1. Each is a unit before any factor sign is inferred.

The main and input factors cannot be −1 modulo 4 because `Delta` is 0 or 3 modulo 4. No positivity of the input root is needed. The normalized strong factor has the same exclusion. The ordinary strong factor has residues `1+square` for `Delta=0`, or `square+square` for `Delta=3`, so it also cannot be −1. After its own strong equation is recovered, the ordinary `Kaux` is a square; normalized `Kaux` is already literally a square. The auxiliary factor is therefore never −1 modulo 4.

The first factor's negative-Pell descent is valid for `u=XY²>1`. A hypothetical solution has `uk<tau<(u+1/2)k`; multiplying by the inverse unit gives the positive smaller coefficient `(2u+1)k−2tau`. Its other coordinate cannot be zero. This excludes the remaining negative norm. With all five norm factors +1, the transport factor is +1 as a consequence of the retained product alone.

The transport equality is

`(Kconstant+w)C + 1−F−(t−1)(q−1)=1`.

Here the trailing summand is nonpositive and `Kconstant+w≥2`, so indeed `C>0` (the proof needs only `C≥0`). Since `C=q−F−Z−alpha−2dx`, positivity of the supplied slacks gives `F+Z<q`. This step uses positive ordinary input and the actual positive fixed input scale. It uses no decoding theorem.

The actual compiler has `B=2^d≥16`, `J≥1`, and `q=(B−1)J+1`, so `q≥16` without assuming `q` itself dyadic. The unshifted masks satisfy `0<MC,MF0<B−1`; the port is `MF0+B−1`. Consequently

`0<(MC+q(MF0+B−1))J<(q−1)(1+2q)`.

The integer inequality `F+Z<q` gives `2q−1≤q²−Z−qF≤q²−q−1`. Substitution yields exactly

`(2q−1)(q²−1)<R<q⁴−q³`.

For the asymmetric source, `E=wsq⁴≥q⁴>R+q³`, and `a=E+Y>R+2`. Neither the stronger old symmetric bound `E>2R` nor any complete-parent conclusion has been imported.

## 2. Genuine indices and the ratio interval need no first-index congruence

The first fundamental integer-coefficient unit has coefficient 2 and first coordinate `P=2XY²+1`. Coefficient 1 is impossible since its first coordinate squared would lie strictly between consecutive squares. Therefore `k=2psi_P(n)`, `n≥1`; this is the source of evenness of `k`.

The main root is positive by its literal definition. Its norm at discriminant `A²−1`, with `A=a+2`, therefore gives `c=psi_A(p)`, `p≥1`. The unit with coefficient 1 is fundamental for the integer-coefficient problem.

The supplied positive `eta,zeta` give exactly `kY<c<k(Y+1)`. The actual source parameters give

- `P−A=XY(2Y−1)−Y−1>0`
- `2A²−1−P=2Y²(X²+X+1)+8Y(X+1)+6>0`
- `A>Y+1`

Monotonicity excludes `p≤n`. Duplication at `Q=2A²−1` excludes `p≥2n`. Hence `p/2<n<p`, before using `R` as a Pell index or recovering a first-index residue.

## 3. The new bootstrap `p≥6` is valid

With `H=4a+3`, the recurrence for `z_j=chi_A(j)−a psi_A(j)` has initial values 1,2. The sequence `2^j` satisfies it modulo `H`, because `5−4A=−H`. The source main projection gives `X≡z_p≡2^p (mod H)`.

The independent outer bounds imply `0<X<H` and `H>32`. If `p≤5`, equality of the two representatives forces `X=2^p`. Since `X≥16`, only `(p,X)=(4,16),(5,32)` survive. The already proved ratio interval gives `n≥3` in both cases.

The elementary estimates in the draft are correct:

`c<[2Y(X+2)]^(p−1)`, and `kY>32X²Y⁵`.

For `(p,X)=(4,16)`, their quotient bound is `18³/(4·16²Y²)<1`. For `(5,32)`, it is `34⁴/(2·32²Y)≤83521/524288<1`, using `Y≥4096`. Both contradict `c>kY`.

Thus `p≥6` is independently proved. The exact value `psi_A(6)=32A⁵−32A³+6A` exceeds `A(A²−1)²`. Also `c>2p` by elementary growth, and `c>2R` already follows from `p≥3`, `c≥4A²−1`, and `A>R+2`. None of these three large-`c` conclusions needs the missing equation or an assumed canonical witness.

## 4. Normalized and ordinary rank arguments are correctly separated

### Normalized

`psi_A(m)=ic²` gives `p|m` by strong divisibility. Writing `m=pk`, the binomial congruence

`psi_A(pk)/c ≡ k·chi_A(p)^(k−1) (mod c)`

and coprimality force `c|k`. Therefore `pc|m`, a stronger conclusion than needed, and `m>2p`. No relaxed-rank size premise is needed in this branch.

### Ordinary

It would be invalid to classify the relaxed equation immediately as the Pell sequence at `A`; the appendix correctly avoids that error. It first classifies integer-coefficient norm-one units in the squarefree field using the smaller fundamental unit `F+y0√d0`. It writes `A=chi_F(e)` and allows `e>1`.

The gcd argument is sound: with `L=psi_F(e)` and `U=Delta/L`, the integer `c gcd(c,Delta)` divides `U psi_F(gcd(b,ep))`. If `gcd(b,ep)` were proper, duplication and `L<A` would give `2h²<Ac`, while the independently supplied `c>A Delta²` gives `h²>Ac`. Thus `ep|b`, recovering `f=chi_A(m)` and `p|m`.

Finally `c²|Delta psi_A(m)` gives `c|Delta k`, not `c|k`. The appendix uses the correct weaker conclusion: `gcd(c,Delta)=gcd(p,Delta)|p` then yields `c|m=pk`. The normalized and ordinary rank conclusions are not conflated.

### Positivity after rank

For the ordinary branch, one can expand the omitted elementary size detail as follows. Since `c>A Delta²` and `A≥2`, `Delta≥3`, we have `c>2Delta`, `c²>4Delta`, and

`f²=1+i²c⁴/Delta>4c²>Delta+c`.

This also gives `f>2c`. Normalized size bounds are immediate from its stronger equation. Hence in either branch

`Kaux−Rf²−c=(Delta−R)f²−Delta−c>0`.

The auxiliary gap excludes every `V<−1`, because a nontrivial absolute value is at least `2Kaux−1` whereas the source has `V>−Kaux`. The residue `V≡−c (mod f)` excludes `V=±1`, and the norm excludes zero. Thus `V>0`. Rank has already established integrality of `j=(V+R)/c`; both `j` and `o=(V+c)/f` are then positive. No restoration of a full parent zero is used here.

## 5. Main-index recovery and fixed-minus parity are valid

With `S²=Delta(f²−1)` and `c|S`, auxiliary classification gives an odd index `ell`, and the polynomial identities for `Q_v` yield both unsquared congruences. Squaring the congruence modulo `f` gives `chi_A(2ell)≡chi_A(2p) (mod chi_A(m))`.

The plus-sign step-down applies because `0<2p<m`, already proved separately in each branch. Its conclusion is `2ell≡±2p (mod 4m)`, hence `ell=epsilon p+2mt` by division of an integer equality. This does not invert 2 modulo an even modulus.

Reduction modulo `c`, together with `c|m`, gives `R≡±p (mod c)`. The established strict bounds `0<R,p<c/2` force equality `p=R`.

Since `ell` is odd, so is `p`. For `p=2r+1`, retaining both original unsquared minus congruences gives exactly `r+mt` odd and `r+(m+1)t` odd. The representative exclusions use the already established `c>2p` and `f>2c`. Their difference makes `t` even, then `r` odd. This proves `p=R≡3 (mod 4)` for all such positive zeros, not merely canonical auxiliary indices.

## 6. Exact defect and scope of the remaining question

The strict ratio interval and `p=R` give an odd defect `d=2n−R` with `1≤d≤R−2<E`. Since `P≡1 (mod E)`, the first Pell recurrence gives `k≡2n (mod E)`. Thus the literal least nonnegative remainder of `k−R−1` is `d−1`, with no modular wrap.

Also `n>R/2`, `R=p≥6`, so `n≥2` and `k≥4P>R+1`. Consequently the forced inverse is genuinely positive over the rationals. Its only unresolved coordinate property is integrality, exactly equivalent to `d=1`.

The known `p=27,n=15,X=2^27` subsystem obstruction does not refute this full-source result or settle deletion: its odd `Y` conflicts with `q|X`, `q≥16`, and `q³|Y`. None of my smaller exact rank or defect fixtures claims full-source admissibility.

## Finite supplements

Fresh normal and optimized runs use explicit exceptions, not assertions. The checks include:

- both inert source deletions, pins, primitive counts, SSA order, and supplied-port sets
- 128 mod-4 exclusions and the two critical small-index endpoint estimates
- 5,390 recurrence/growth/gcd checks
- 28,392 complete-period plus-step-down checks
- four exact main/strong subsystem fixtures, explicitly not full-source zeros
- 432 modular checks involving a smaller fundamental Pell parameter
- 13,200 fixed-minus sign-bookkeeping cases, including both epsilon signs
- 1,608 exact positive-rational-inverse/remainder subsystem cases

The universal conclusions depend on the arguments above, not on these finite counts. No proof of universal `d=1`, compiler/input decoding without it, or bound improvement is supplied.
