# Recovering the arithmetic signs from one normalized remainder bound

AI-assisted internal mathematical proof and audit, 25 October 2026.

Repository snapshot inspected: `VladimirReshetnikov/ProveIt` at
`3ecd6a6cf53d47519228328567f45fb7ee9781d9`.

The immediate parent is the direct 252-integer quartic in
`docs/incoming/ConZFC_Common_Remainders_Radix47_2026-10-25.zip`, extracted as
`conzfc_common_remainders_20261025/direct`. Its exact ordinary proof delta is
`proofs/NORMALIZED_REMAINDERS_PROOF.md`. The signed Pell interface used below
is the one established in the copied round-17 files `PROOF_315.md`,
`ORIENTATION_FIRST_PROOF.md`, and `STRICT_BUDGET_PROOF.md`.

This note proves the source transformation implemented in
`direct_agent/rounded245`. The producer reports an emitted quartic with 245
integer variables, 181 quadratic residuals, 5,304 monomials, and coefficient
height 128,446. Those finite counts belong to the emitted object and its
separate algebraic checker. The proof here is an internal mathematical
audit, not external peer review and not a new Lean/Rocq proof term.

## 1. The transformation and the theorem

All variables in the new source range over unrestricted integers. Keep the
parent's signed Pell frame, signed squared semantic anchor, pooled coordinate
orientation, eighteen power requests, factorial/binomial front, endpoint
equations, Horn-flow data, and eleven normalized digit equations.

Use the following semantic names for existing arithmetic coordinates:

* `t=16+z^2` is the cofinal horizon;
* `F` is the proposed factorial;
* `B` is the exact-binomial output;
* `V` is the output of the request `(F^2+1)^t`;
* `x` is the amplification index;
* `a_1,...,a_9` are the actual CRT representatives, namely their stored
  coordinates plus one;
* `N` is the output of the request `B^x`;
* `q` is the radix output;
* `M` is the output of the request `q^x`.

The old source contains the linear identities

```
B = r + s + 1,       FB = V + s,       q = B + o + 1.
```

Here `r` is the old factorial remainder, `s` is its complementary ceiling
slack, and `o` is the exact-binomial output slack. In the parent's raw
`data/source.json`, their indices are respectively 7, 8, and 185; these
indices describe the pinned input only, not any optimized output.

Make exactly these mathematical changes:

1. Remove the three scalar guards `r>=0`, `s>=0`, and `o>=0`. Each was
   represented by a ternary quadratic guard.
2. Replace the self-radix majorant `1+sum_i a_i` by

   ```
   H = 1 + 2 sum_i a_i.
   ```

   Thus the existing request now reads `q=(BH)^x`. Before any sign has been
   recovered, `H` is an odd integer and is therefore nonzero. Once the
   representatives are proved nonnegative, `H` is at least the old
   majorant. This is a change to one quadratic base-definition row; it
   does not require a new power request.
3. Delete the old multiplication row for `FB`, the old ceiling row, and
   the old factorial remainder/slack row. Replace them by two quadratic
   rows using two new integer coordinates `v_B` and `S`:

   ```
   B v_B = M,       FM = v_B V + S.
   ```

   Algebraically these imply `S=v_B(FB-V)`. In the proof, define
   `s=FB-V` and `r=B-s-1`. They are reconstructed integer expressions,
   not extra coordinates in the final equation. Keeping only these two
   rows avoids materializing the old product `FB` or a separate `s`.

4. Extend the parent's common remainder norm by this one extra square:

   ```
   M^2 = 1 + 4(S^2 + sum_{i=1}^{11} R_i^2)
             + alpha^2 + beta^2 + gamma(gamma+1).       (1)
   ```

   The `R_i` are the already normalized eleven digit remainders.

Every changed or added row is quadratic. Therefore the sum of the squares
of all final residual rows still has degree at most four. The main saving
removes nine ternary-guard coordinates and adds `v_B,S`; the deleted and
reconstructed ceiling wires are handled by the exact monic projection.
The emitted count is seven below the 252-variable parent.

**Theorem.** The transformed source has an integer solution if and only if
the direct C222 arithmetic front has a finite refutation witness. With the
parent's identified C222-to-ZF and ZF-to-ZFC syntactic calibration, ZFC proves
that the fixed emitted polynomial has no integer zero if and only if
`Con(ZFC)`.

The proof below does not assume consistency, an actual refutation, or
positivity of a deleted-guard coordinate. In particular, it does not use
the arithmetic meanings of `q`, `B`, or `F` before they have been derived.

## 2. What survives before any arithmetic sign recovery

The parent signed-frame and anchor proof uses squares of actual atoms and
unrestricted comparison quotients. Its orientation-first variant explicitly
allows the derived-label index to be signed until after the power requests
are interpreted. None of its preliminary conclusions uses any of the three
guards being deleted.

Consequently it still supplies a positive integer `W>=258`, a signed center
`A` with `|A|>W^W`, and canonical signed Pell coordinates for every requested
index. Every requested base `n`, index `k`, and proposed output `m` has
absolute value below `W`. The principal coordinates are

```
X_k(A), Y_k(A),
```

with `X_{-k}=X_k` and `Y_{-k}=-Y_k`. The derived `t+1` pair remains the
ordinary one-step Pell recurrence from the canonical `t` pair.

For clarity, the reused anchor proof first obtains an absolute anchor index
`|h|`, proves every classified principal index below `W`, and then uses the
pooled congruence errors to recover both coordinate signs. It does not
require `h>0`, `B>0`, `q>0`, or nonnegative CRT representatives at that stage.

### Signed-base power lemma

The parent's positive-base lemma extends without a change of polynomial to
every integer base with `|n|>=2`.

Put `T=2An-n^2-1`. From `|n|<W` and `|A|>W^W`,

```
|T| >= 2|A||n| - n^2 - 1 > W^W + W.
```

The canonical Pell recurrence and the power row give `m=n^k mod T` when
`k>=0`. The absolute difference is below `|T|`, so equality follows. If
`k=-j<0`, then `gcd(n,T)=1` because `T=-1 mod n`; the negative-index
recurrence instead yields

```
m n^j = 1 mod T.
```

Its absolute error is below `W^W+1<|T|`. Thus `m n^j=1`, which is impossible
for integer `m`, `|n|>=2`, and `j>=1`. Hence such a request forces `k>=0`
and its exact integer power output. The output may be negative for a
negative base and odd index; no output sign is presumed.

For base `n=1` and an already known nonnegative index, the canonical
recurrence gives `m=1 mod (2A-2)`, and the same magnitude argument gives
`m=1`. This covers both the possible `F=0` request and the temporary
`q=1,x=0` case below. No request at base zero is used in the bootstrap.

## 3. The normalized ceiling immediately bounds the old signed slack

The ternary expression in (1) is nonnegative for every integer argument.
Thus `M!=0` and `|S|<|M|/2`. From

```
B v_B=M,       FM=v_B V+S,
```

both `B` and `v_B` are nonzero. Define the integer `s=FB-V`; the displayed
identities give `S=v_B s`. Division of absolute values then gives

```
|s| < |B|/2.                                          (2)
```

This argument needs no previously interpreted power, no sign of `M` or
`B`, and no sign of `v_B` or `s`.

Since `t>=16` and `F^2+1>=1`, the signed-base power lemma gives

```
V=(F^2+1)^t >= 1.                                     (3)
```

The definition of the reconstructed integer `s` gives

```
FB=V+s.                                               (4)
```

Write `b=|B|` and `u=|F|`. Equations (2)--(4) imply the following useful
bootstrap bounds:

```
b>=2,       u<b,       V<b^2.                         (5)
```

Indeed, if `b=1`, the integer `s` must be zero. Then (4) would give
`V=FB<=u`, contradicting `(F^2+1)^t>u`. If `u>=1` and `b<=u`, then

```
V = FB-s < (u+1/2)b <= u^2+u/2 < (u^2+1)^2 <= V,
```

a contradiction. For `u=0`, the inequality `u<b` is immediate. Finally,

```
V < (u+1/2)b <= (b-1/2)b < b^2.
```

At this point `F=0` and negative `B,F` have not been silently excluded.
They are treated below.

## 4. Recovering a large radix without any initial sign guard

Since `b>=2`, the existing request at base `B` forces `x>=0` and gives
`N=B^x`. Because `H` is an odd integer, `|BH|>=2`; its request gives

```
q=(BH)^x.                                             (6)
```

If `x=0`, then `q=1`. The request for `M=q^x`, at base one and known index
zero, then gives `M=1`. This contradicts `B v_B=M` and `|B|>=2`. Therefore
`x>=1`, and in particular `|q|>=2`.

The canonical requests now give `M=q^x` and the exact denominator
`L=q^(t+1)`. The parent retains a ratio row `L v=M`. If `x<t+1`, dividing
that integer identity by the nonzero `q^x` would give

```
q^(t+1-x) v = 1,
```

impossible because `|q|>=2`. Consequently

```
x>=t+1>=17,       |q|>=b^x>=2^17.                     (7)
```

It follows that `|q+1|>=2^17-1>=2`. Each of the nine actual CRT
representatives is a requested exponent at base `q+1`, so each is
nonnegative. The derived-label request similarly gives `h>=0`; the anchor
already excluded `h=0`, so `h>0`. Thus

```
H=1+2 sum_i a_i >= 1.                                 (8)
```

All of these deductions precede factorial interpretation and all delayed
range-decoding arguments. The large modulus in (7) follows from an existing
ratio identity, not from a deleted coordinate sign.

## 5. Signed normalization and exact centered remainder recovery

The common-remainder argument works with signed nonzero moduli as well as
positive moduli. Suppose

```
L v=M != 0,       v U = M Q + R.
```

Then `v` divides `R`, so `r=R/v` is an integer and `U=LQ+r`. If the norm
bound gives `|R|<|M|/2`, then `|r|<|L|/2`. If another integer `r_0` is
congruent to `U` modulo `L` and has `|r_0|<|L|/32`, the difference
`r-r_0` is a multiple of `L` of absolute value less than `|L|`. Hence
`r=r_0`.

For the factorial digit, let

```
C = binom(F^2+t,t),
r_0 = sum_{j=0}^{t-1} binom(F^2+t,j) q^j.
```

The binomial identity is valid for signed `q`. It shows that the quotient
after division by `q^t` is congruent to `C` modulo `q`. The source's exact
digit row uses `B+qk` as its quotient, so centered remainder recovery gives

```
B=C mod q.                                            (9)
```

There are two cases in proving the required short-remainder bound. The
zero case must be stated separately: the usual coefficient bound is false
for lower coefficients when `F=0`.

### Case `F!=0`

For every integer `m>=1`, `t>=1`, and `0<=j<=t`,

```
binom(m+t,j) <= (m+1)^t.                               (10)
```

An induction proves this. Pascal's identity handles `j<=t` in the next
row using `2(m+1)^t<=(m+1)^(t+1)`; the new edge is bounded directly by
`prod_{i=1}^{t+1}(1+m/i)<=(m+1)^(t+1)`.

Apply (10) to `m=F^2`. With `Q=|q|`, (5) and (7) give

```
|r_0| < V Q^t/(Q-1),
V/(Q-1) < 2/b^(x-2) <= 2/2^15 < 1/32.                (11)
```

Thus the normalized source remainder equals `r_0`. Also `C<=V<b^2`.
Because `b>=2` and `x>=17`,

```
|B-C| <= b+C < b+b^2 < b^x <= Q.
```

Combining this with (9) gives `B=C>0`.

### Case `F=0`

Now `V=1` and (4) gives `s=-1`. Equation (2) forces `b>=3`. Every
coefficient `binom(t,j)` is at most `2^t`; consequently

```
|r_0|/Q^t < 2^t/(Q-1)
             < 2^(t+1)/3^(t+1)
             = (2/3)^(t+1) < 1/32,                    (12)
```

where `Q>=b^x>=3^(t+1)` and `t>=16`. Centered recovery again gives (9),
now with `C=binom(t,t)=1`. Since `b+1<Q`, it gives `B=1`, contradicting
`b>=3`. Therefore this case is impossible.

We have now proved

```
F!=0,       B=binom(F^2+t,t)>0.
```

Together with (8) and (6), this also gives `q>0`, `N>0`, and `M>0`.
The signed intermediate analysis has recovered the positive arithmetic
domain without adding a sign assumption.

## 6. An elementary nearest-integer factorial fixed point

The new source supplies `|s|<B/2`, not the old ceiling inequality
`0<=s<B`. The following lemma gives exactly what is needed.

**Lemma.** Let `t>=16`, let `H_t=t!`, and for a real `u>=0` put

```
f_t(u) = (u^2+1)^t / binom(u^2+t,t)
       = H_t prod_{i=2}^t (u^2+1)/(u^2+i).
```

For an integer `F`,

```
|F-f_t(|F|)| < 1/2
```

holds if and only if `F=t!`. At this value,

```
0 < t! - f_t(t!) < 1/[2(t-2)!] < 1/32.               (13)
```

**Proof.** Write `H_t=H` temporarily and `a=t(t-1)/2`. Each factor in
`f_t(u)` is increasing on `u>=0`; hence `f_t` is increasing, `f_t(0)=1`,
and `0<f_t(u)<H` for every finite `u` when `t>=2`.

For nonnegative `e_i`,

```
prod_i (1+e_i)^(-1) >= 1 - sum_i e_i.
```

This follows by writing each reciprocal as `1-d_i` with
`0<=d_i<1`, applying the elementary product union bound, and using
`d_i<=e_i`. With `e_i=(i-1)/(u^2+1)`, it gives

```
f_t(u) >= H [1-a/(u^2+1)].                            (14)
```

Negative `F` are impossible because `f_t(|F|)>0`; `F=0` is impossible
because `f_t(0)=1`. For positive integers `u=F<H`, split into three
overlapping ranges.

* If `1<=u<=t`, monotonicity gives
  `f_t(u)>=f_t(1)=2^t/(t+1)>t+1/2>=u+1/2`.
  The displayed elementary inequality holds at `t=16` and remains true
  on increasing `t`: its exponential left side grows faster than the
  corresponding quadratic right side.
* If `t<=u<=H/2`, equation (14) gives

  ```
  f_t(u) >= H/2 + H(t+1)/(2(t^2+1)) > H/2+1/2 >= u+1/2.
  ```

  Here `H(t+1)>t^2+1`; for `t>=16` it follows already from
  `t!>=t(t-1)`.
* If `H/2<=u<=H-1`, equation (14) gives

  ```
  H-f_t(u) < 4a/H = 2/(t-2)! < 1/2,
  ```

  hence `f_t(u)>H-1/2>=u+1/2`.

Thus no positive integer below `H` satisfies the half-unit condition.
If `u>=H+1`, the bound `f_t(u)<H` excludes it as well. Finally at `u=H`,
equation (14) gives

```
0<H-f_t(H)<=Ha/(H^2+1)<a/H=1/[2(t-2)!]<1/32.
```

This proves both assertions. All estimates are elementary finite arithmetic;
the real-variable notation is only a convenient presentation of rational
inequalities at integer arguments.

Returning to the source, divide `FB=V+s` by the now positive binomial `B`.
Equations (2)--(3) give

```
|F-f_t(|F|)| = |s|/B < 1/2.
```

The lemma therefore forces `F=t!`. Equation (13) further gives

```
0<s/B<1/32.
```

Since `r=B-s-1` and `s` is an integer smaller than `B`, `r>=0` and `s>=0`
are recovered. Since `q=(BH)^x>=B^x` with `B>=2` and `x>=17`,
`o=q-B-1>=0` is recovered too. Every deleted initial scalar guard can now
be restored by a fresh ternary representation.

## 7. Completing the original arithmetic and Horn-flow soundness

With `F=t!`, the parent's remaining arithmetic proof applies with the
larger majorant `H=1+2 sum_i a_i`.

First, `y=V(V-1)>F+2`. The first endpoint identity

```
x=F+1+(y+1)u_0
```

and the already proved `x>=17` imply `u_0>=0`; otherwise
`x<=F-y<0`. Thus `x>=F+1`. The last endpoint

```
x=1+[1+(t+1)y]u_t
```

then gives `u_t>=1` and

```
x>=2+(t+1)y.                                         (15)
```

Consequently every range lower index, including `y+1`, is at most `x`,
and the strict amplification proof with exponent `K=x` is unchanged.
The source's existing inequality `ell(t+1)<x`, with
`ell=4194304`, remains available for the derived label. Enlarging the
self-radix majorant does not increase the required precision or the local
Horn-polynomial degree bound.

The encoded-index congruence and the factorial product show that its
actual representative is positive. In particular the old sum majorant
`H_old=1+sum_i a_i` is at least two. Since `H>=H_old`, the ordinary
range-binomial coefficient bounds remain

```
binom(a,j)<=max(1,a)^k<=H^x
```

for the needed indices, including the zero-representative case. The
derived-label bound `h<=H_old^ell<=H^ell` gives the same conclusion for
that exceptional upper argument. Since `q=B^x H^x`, every genuine range
low remainder is less than its denominator divided by 32, exactly as in
the parent's proof.

The unchanged normalized digit equations and (1) therefore recover every
ordinary low remainder. The `N`-divisibility range tests, prime-power CRT
decoding, beta quotients, constructor identities, and nonnegative Horn-flow
argument apply. They produce a finite C222 refutation.

This is a semantic extension of the parent's arithmetic proof. It does
not assert that the old polynomial with `H_old` has the identical `q`
coordinate. Its only changed use of that sum was as a self-sized radix
majorant; the new positive `H` satisfies every required majorization and
preserves `N|q`.

## 8. Constructive completeness from a finite refutation

Conversely, start with a finite C222 refutation. Apply the parent's cofinal
construction of a horizon `t=16+z^2`, the exact `F=t!`, `B`, `V`, `y`,
beta-CRT code `x`, and amplification modulus `N=B^x`. The construction has
`x>=2+(t+1)y`, so in particular `x>=17`.

Choose the actual CRT representatives in their required classes at
precision `N^2`, as in the inherited proof. The dominant representative
can still be chosen with parity opposite the designated companion so that
the semantic anchor index is even and exceeds all other requested
indices. That choice depends on `N` and the finite refutation, not on the
subsequent radix `q`.

Now set

```
H=1+2 sum_i a_i,       q=(BH)^x,       M=q^x.
```

This radix is at least the parent's canonical one. The true powers,
binomial numerators, range remainders, and quotient witnesses therefore
exist with the same divisibility and precision properties. Recompute the
square frame from these actual changed atoms, choose the positive canonical
Pell center, and use the parent's even-anchor/odd-auxiliary construction.
No new parity requirement is imposed on `x` or on a CRT representative.

Let `s=FB-V`. The nearest-factorial estimate (13) gives `0<=s<B/32`.
Because `B|q` and `x>=1`, the positive integer

```
v_B=M/B
```

exists. Put `S=v_B s`. Then `0<=S<M/32`. Each of the other eleven
normalized true remainders also lies in `[0,M/32)`. Hence

```
4(S^2+sum_{i=1}^{11}R_i^2)
       < 4*12*(M/32)^2
       = (3/64)M^2
       < M^2.
```

The integer `M^2-1-4(S^2+sum R_i^2)` is nonnegative and has a representation

```
alpha^2+beta^2+gamma(gamma+1).
```

For completeness of that familiar representation, apply the three-square
theorem to `4n+1`: it is never of the form `4^a(8b+7)`, and a three-square
representation has exactly one odd square modulo four. Dividing the other
two even squares by four gives the displayed ternary form.

This fills (1), the two new normalization rows, and every retained source
row. The fixed integral monic projections and integral translations then
transport this witness to the emitted polynomial. Conversely those
transformations restore witnesses from every emitted zero by their exact
algebraic certificates.

## 9. Calibration, internal scope, and verification obligations

The ordinary arithmetic proof establishes, uniformly over integer tuples,
that a new polynomial zero yields a finite C222 refutation, and uniformly
over finite refutations that such a zero can be built. Composition with the
identified inherited syntactic interfaces

```
KEndpoint.c222_iff_zf_refutation
ConstructibleChoice.zf_refutation_iff_zfc_refutation
```

gives the required arithmetic equivalence. The arguments use elementary
integer arithmetic, Pell recurrences, finite CRT constructions, factorial
bounds, and finite syntactic proof translations; they can be carried out
inside ZFC. This supplies an ordinary proof formalizable in ZFC, not merely
checks on externally standard numeral instances. An actual newly emitted
object-language ZFC derivation or complete proof-assistant term is not
claimed here.

The producer and an independent finite checker should bind the following
precise edits to the pinned source:

* remove only the scalar guards for source coordinates 7, 8, and 185;
* change the single `self_radix.base_definition` from the old sum to the
  odd sum (with actual representatives, including their affine offsets);
* remove the three old local rows for the `FB` multiplication, factorial
  ceiling, and factorial remainder/slack sum; add `B v_B=M` and
  `FM-v_B V-S=0`, using source coordinates `B=5`, `F=3`, `V=6`, and
  `M=223` before reindexing;
* add the term `-4 S^2` to the existing normalized-remainder guard;
* retain the squared semantic anchor, all eighteen actual power requests,
  all three old normalization ratios, and the cofinal horizon;
* replay the exact Horn factoring, integral monic projection, translation,
  and fully collected quartic expansion.

Finite checks certify these concrete algebraic objects. The unbounded
proof in Sections 2--8 certifies the semantic change. Neither type of
evidence substitutes for the other.

## 10. Audit findings that must not be lost in abridgment

1. The power lemma must be stated for signed bases `|n|>=2`; a positive-only
   lemma cannot justify the early `B` and `BH` requests.
2. `H` must be odd as an integer polynomial before signs are known. Using
   the unchanged `1+sum a_i` would permit `H=0` and would break the
   bootstrap.
3. The common norm proves `M!=0` before any power interpretation. The
   ratio `B v_B=M` is what transfers its strict bound to `s`.
4. The exclusion of `x=0` uses the known-index base-one case, not a claim
   that every base-one request forces a nonnegative index.
5. `x>=t+1` is derived from the existing integer ratio for `q^(t+1)`;
   no endpoint positivity or factorial meaning is used at that stage.
6. At `F=0`, inequality (10) is false for lower binomial coefficients.
   The separate estimate (12) repairs this case and then excludes it.
7. Before `B>0` is proved, use a centered signed radix remainder and the
   stronger inequality `|B|+C<|q|`. Two unrestricted representatives of
   the same residue class are not equal merely because each has absolute
   value below `|q|`.
8. The nearest-integer factorial lemma, rather than the old one-sided
   ceiling lemma, is essential after all three initial sign guards have
   been removed.
9. Completeness uses twelve remainders and the strict estimate `3M^2/64`.
   It needs no additional parity restriction or prescribed radix residue.
10. The changed self-radix is a majorant substitution with a fresh actual
    frame. It is not an equality of the old and new polynomial zero sets
    at unchanged coordinate values.

## Appendix: the factorial rounding lemma holds for every `t>=4`

The source uses `t>=16` for other arithmetic reasons. The rounding lemma
itself has the sharper uniform range `t>=4`:

```
|F - (F^2+1)^t/binom(F^2+t,t)| < 1/2    iff    F=t!,
```

for every integer `F` and every integer `t>=4`. Its strict completeness
error bound remains

```
0 < t! - ( (t!)^2+1 )^t / binom((t!)^2+t,t)
    < 1/[2(t-2)!].
```

Here is a complete adjustment of the earlier proof. For `t>=5`, change
the small-argument range to `1<=u<=t-1`. Then

```
f_t(u)>=f_t(1)=2^t/(t+1)>t-1/2>=u+1/2.
```

The strict inequality is true at `t=5`; after multiplying by `2(t+1)`
it becomes `2^(t+1)>2t^2+t-1`, and induction follows because
`2(2t^2+t-1)>(2(t+1)^2+(t+1)-1)` for `t>=5`.
The middle range `t<=u<=H/2` is unchanged. In the upper range
`H/2<=u<=H-1`, the error is less than
`4a/H=2/(t-2)!<=1/3<1/2`. The target `u=H` has error less than
`a/H=1/[2(t-2)!]<=1/12`.

It remains to check `t=4`, where `H=24` and `a=6`. For `u=1`,
`f_4(1)=16/5>3/2`. For `u=2,3`, monotonicity gives
`f_4(u)>=f_4(2)=125/14>7/2`. For `4<=u<=12`, the middle-range
union bound gives `f_4(u)>12+1/2`. For `12<=u<=22`, the upper bound
gives `24-f_4(u)<1`, hence `f_4(u)>23>=u+1`. At `u=23`,

```
24-f_4(23) < 24*6/(23^2+1) = 72/265 < 1/2,
```

so it too is excluded. At `u=24`, the error is less than `1/4`, which
proves existence of the intended rounded fixed point. Negative integers,
zero, and integers above `H` are excluded exactly as before.

The threshold cannot be changed to a uniform claim for all `t>=3`:
at `t=3` both `F=5` and `F=6` satisfy the strict half-unit condition.
Indeed `f_3(5)=338/63`, with error `23/63`, and
`f_3(6)=1369/247`, with error `113/247`. At `t=2`, both `F=1`
and `F=2` satisfy it, since their images are `4/3` and `5/3`.
These exact counterexamples concern the proposed uniform threshold;
they do not assert that every smaller individual value of `t` fails.
