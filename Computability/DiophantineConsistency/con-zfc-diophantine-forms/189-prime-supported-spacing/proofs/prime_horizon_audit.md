# Independent mathematical audit: prime-supported Pell growth and beta spacing

Prepared as an internal mathematical review on 25 October 2026.

## Result of the review

The proposed change is sound at the level of the ordinary mathematical proof, provided the inherited arithmetic interface is exactly the one stated below. The key new completeness argument works. It uses a cofinal family of horizons with one large prime as their only odd prime factor, so the existing growth ordinate can absorb all prime support formerly supplied by a separate beta-spacing multiplier.

The new argument is not a proof of consistency and is not a new compiled Lean/Rocq or object-language ZFC derivation. Its claims are uniform arithmetic statements formalizable in ZFC. It composes with the pinned parent's named C222/refutation calibration; that calibration remains inherited.

The matched parent is:

`reference/incoming/ConZFC_Pell_Growth_210_2026-10-25/ConZFC_Pell_Growth_210_2026-10-25/report/main.tex`

in particular its sections on the inherited arithmetic interface, the delayed sign bootstrap, exact digit recovery, prime-support beta CRT, and constructive completeness. The principal parent's literal equation is in `equations/principal210/equation.json` in that package. This note reviews the semantic change; an independent coefficient checker must separately bind it to the emitted 209-coordinate residual list.

## 1. Exact replacement

Set

\[
d=2^{19}=524288,\qquad c=524309.
\]

Here `c` is a fixed positive prime, not a Diophantine coordinate. Replace the old horizon and growth rows by

\[
t=32(2z+1)^2,\qquad Z=ctF,
\]
\[
X^2-Z^2-2ZF=1,\qquad F=ctu-t.
\]

Every displayed residual is quadratic in its quantified coordinates. All coordinates, including `z,u,X,Z,F`, range over unrestricted integers. Every possible horizon is a positive integer at least 32 and has exact 2-adic valuation five.

Replace the old beta-spacing row

\[
y=F(2v+1)
\]

by

\[
\boxed{y=FB.}
\]

The existing binomial-selector coordinate `B` is reused. The old coordinate `v` is deleted. No new quantified coordinate is introduced by this substitution.

The two inequalities on the fixed prime needed below are

\[
c>d+1,\qquad c>32.
\]

They hold since `524309 > 524289`.

### Finite primality certificate logic

The integer `524309` has integer square root 724, since

\[
724^2=524176<524309<525625=725^2.
\]

It is odd. Exhaustively checking nondivisibility by each odd integer from 3 through 723 proves primality: a composite positive integer has a divisor between 2 and its square root. The following complete standard-library check succeeds:

```python
from math import isqrt
c = 524309
assert isqrt(c) == 724
assert c % 2 == 1
assert all(c % q != 0 for q in range(3, isqrt(c) + 1, 2))
```

Primality is needed only for the cofinal completeness argument. Soundness uses the displayed size inequalities and `c > 1`.

## 2. Elementary Pell facts used throughout

For an integer `a >= 2`, define integer sequences by

\[
X_0=1,\quad Y_0=0,\quad
X_{n+1}=aX_n+(a^2-1)Y_n,\quad
Y_{n+1}=X_n+aY_n.
\]

The fundamental positive unit of the Pell equation with discriminant `a^2-1` is `a + sqrt(a^2-1)`: the positive ordinate of a nontrivial positive solution is at least one, and `(a,1)` is a solution. Standard integer Pell descent consequently classifies every solution with nonzero ordinate by

\[
|X|=X_n(a),\qquad |Y|=Y_n(a),\qquad n\ge1.
\]

The following identities or inequalities follow directly from the recurrences:

1. `Y_n(a) = n (mod a-1)`, by specializing the polynomial recurrence at `a=1`.
2. `Y_n(a) >= (2a-1)^(n-1)` for `n >= 1`, because the positive sequence is increasing and `Y_(n+1)=2aY_n-Y_(n-1) >= (2a-1)Y_n`.
3. If `a` is odd, then
   \[
   v_2(Y_n(a))=v_2(n),\qquad n\ge1.
   \]
   Indeed every `X_n(a)` is odd; `Y_n(a)` has the parity of `n`; and `Y_(2m)=2X_mY_m` adds exactly one factor of two on each doubling.
4. If `p` divides `Y_m(a)` and `m` divides `n`, then `p` divides `Y_n(a)`. This follows either by repeated addition of Pell pairs or from the composition identity `Y_(ms)(a)=Y_m(a)Y_s(X_m(a))`.

Only integer recurrences, induction, and finite-field arithmetic are needed in the new proof. Radicals can be replaced throughout by pair notation.

## 3. Initial sign-free bound and delayed large-growth bound

From `F=t(cu-1)` and `c>1`, one has `F != 0`: equality would imply `cu=1` in the integers. Also `F` is even because `t` is a multiple of 32.

Eliminating `Z` gives

\[
X^2-((ct+1)^2-1)F^2=1.
\]

Put `a=ct+1`. It is odd and at least two. Pell classification supplies `n >= 1` with

\[
|F|=Y_n(a).
\]

The divisibility row gives `F = -t (mod ct)`. Combining it with `Y_n(a)=n (mod ct)` gives:

- if `F>0`, then `n=-t (mod ct)`, hence `n >= (c-1)t`;
- if `F<0`, then `n=t (mod ct)`, hence `n >= t`.

In either case,

\[
|F|\ge(2ct+1)^{t-1}>t.
\]

This is the exact initial fact needed by the parent's sign bootstrap. A stronger bound is deliberately not assumed until `F>0` has been recovered.

After that recovery, `n >= (c-1)t > dt`. With the parent's local-label majorant

\[
L=8^{d-1}t^d,
\]

we obtain

\[
F\ge(2ct+1)^{n-1}\ge(8t)^{dt-1}\ge L^t.
\]

For the final inequality, the ratio of the last two expressions is exactly `8^(t-1)/t >= 1`. Thus the parent receives precisely its old large-growth interface once that interface is first needed.

## 4. The parent sign bootstrap survives y=FB

The following are retained source facts, not new assumptions about arbitrary integers: the principal shared-Pell frame authenticates its signed indices; its cap gives `C != 0`; `C` is even; and the arithmetic rows include

\[
B\eta=C+F+1,
\]
\[
D=2(C+F+1),\qquad q=D^x,
\]
\[
x=F+1+(y+1)r_0,\qquad
x=1+[1+(t+1)y]r_t.
\]

The powers are represented by the parent's retained ordinary polynomial certificates. For an integer base of absolute value at least two, those certificates first force a nonnegative exponent and then the exact power. The relevant retained requests have indices `x`, `y+1`, `F+t`, and `C`.

Since `C` and `F` are even, `C+F+1` is odd and nonzero. Therefore `B != 0`, `eta != 0`, and `|D| >= 2`. The new row immediately supplies

\[
|y|=|FB|\ge|F|>t.
\]

Now apply the unchanged argument in its original order:

1. The request `q=D^x` forces `x>=0`. If `x=0`, the terminal endpoint says `1+(t+1)y` divides `-1`, contradicting its absolute value greater than one. Hence `x>=1` and `|q|>=2`.
2. The retained power of base `q` with index `y+1` gives `y+1>=0`. A negative `y` would be at most `-|F|<-1`. Thus `y>0` and `y>=|F|`.
3. If `x=1`, the first endpoint gives `-F=(y+1)r_0`, impossible since `0<|F|<=y<y+1`. Consequently `x>=2`. The terminal endpoint then gives `r_t>=1` and `x>=2+(t+1)y`.
4. It follows that `|q|>=4` and `|q+1|>=3`. The retained base-`q+1` requests give `F+t>=0`, `C>=0`, and nonnegative ordinary representatives. Since `|F|>t`, necessarily `F>0`; since the cap excludes `C=0`, one has `C>0`. Hence `D>0` and `q>0`.
5. If `r_0<=-1`, the first endpoint gives `x<=F-y<=0`. Thus `r_0>=0` and `x>=F+1`.

At this point the large-growth bound of Section 3 is available. The parent's digit estimates and binomial authentication apply unchanged, yielding

\[
B=\binom{F+t}{t}>1.
\]

In particular `B>0` and `y=FB>F`. The endpoint degeneracy `y=F` is now automatically absent. It was excluded separately in the parent.

There is no circular use of `B>0` or of a binomial interpretation of `B`: only the already-present odd selector proves `B!=0` at the beginning.

## 5. Small annihilating indices modulo every prime

The completeness proof does not require a minimal rank-of-apparition theorem. An explicit small annihilating index is enough.

Fix the center `a=ct+1` and write `D_a=a^2-1`. For each odd prime `p`, define

\[
m_p=\begin{cases}
p,&p\mid D_a,\\
p-\left(\frac{D_a}{p}\right),&p\nmid D_a,
\end{cases}
\]

where the parenthesized quantity is the Legendre symbol. Put `m_2=2`. Then

\[
1\le m_p\le p+1,\qquad p\mid Y_{m_p}(a).
\]

Here is a complete proof of the three cases.

### Odd p dividing D_a

Modulo `p`, one has `a=+1` or `a=-1`. The first recurrence becomes `X_n=a^n`. Induction in the second gives

\[
Y_n=n a^{n-1}\pmod p.
\]

For `n=p`, this is zero. Thus `m_p=p` works, even though division by `sqrt(D_a)` would not have been legitimate.

### Odd p not dividing D_a

Choose `s` with `s^2=D_a` in `F_p` when `D_a` is a square, or in the quadratic field `F_(p^2)` otherwise. Put `u=a+s`. Since `(a+s)(a-s)=1`, the element `u` is nonzero and its inverse is `a-s`. The Pell recurrence gives

\[
Y_n=\frac{u^n-u^{-n}}{2s}.
\]

The denominator is nonzero. In the square case, `u` lies in the multiplicative group of `F_p`, so `u^(p-1)=1`; hence `Y_(p-1)=0`. In the nonsquare case, Frobenius sends `s` to `-s`, whence `u^p=u^(-1)` and `u^(p+1)=1`; hence `Y_(p+1)=0`. These are exactly the chosen indices.

### p=2

The center `a` is odd. The recurrence gives `Y_n=n (mod 2)`, so `Y_2=0 (mod 2)`. Thus `m_2=2` is valid without any odd-characteristic argument.

## 6. Cofinal compatible horizons and indices

For every integer `k>=1`, take

\[
t=32c^{2k},\qquad z=(c^k-1)/2.
\]

The latter is an integer because `c` is odd. These horizons have the prescribed form `32(2z+1)^2`, and they are cofinal among positive integers.

For every prime `p<=t`, the annihilating index satisfies

\[
m_p\le t+1=32c^{2k}+1<c^{2k+1}.
\]

Consequently

\[
v_c(m_p)\le2k.
\]

Choose an integer `ell` with `2^ell>t`, and let

\[
M=\operatorname{lcm}\bigl(2^\ell,\{m_p:p\text{ prime},\ p\le t\}\bigr).
\]

The prime factors of `ct` are just `2` and `c`. Its 2-adic valuation is five and its `c`-adic valuation is `2k+1`. The preceding bound shows

\[
\gcd(M,ct)\mid t.
\]

Therefore the two congruences

\[
n\equiv0\pmod M,\qquad n\equiv-t\pmod{ct}
\]

are compatible by the elementary generalized CRT. Their common solutions form a nonempty arithmetic progression and contain arbitrarily large positive integers.

For any such positive `n`, put

\[
F=Y_n(ct+1),\quad X=X_n(ct+1),\quad Z=ctF,\quad
u=(F+t)/(ct).
\]

These are integers, `F>0`, and they satisfy all new growth rows. Integrality of `u` follows from `Y_n(ct+1)=n (mod ct)`. As `n` tends to infinity in the CRT progression, `F` is unbounded.

By the annihilating-index lemma and composition of Pell recurrences,

\[
p\mid F\quad\hbox{for every prime }p\le t.
\]

Also `2^ell | n`, so the 2-adic Pell identity gives `2^ell | F`. Since `0<=t<2^ell`, the binary supports of `F` and `t` are disjoint. There are no carries in `F+t`. The elementary factorial valuation identity therefore gives

\[
v_2\binom{F+t}{t}=0.
\]

Thus the already-determined selector `B=binom(F+t,t)` is odd, exactly as required for choosing the even CRT representative `C` in the inherited completeness proof.

This argument permits arbitrarily large positive `F` at every selected horizon. No growth rate for primes, primitive divisor theorem, or effective asymptotic estimate is used.

## 7. Beta moduli and the finite-state bound

Set `y=FB`. Since every prime `p<=t` divides `F`, every such prime divides `y`. The beta moduli

\[
1+iy,\qquad 1\le i\le t+1,
\]

are pairwise coprime. Indeed, a common prime divisor of the moduli for `i<j` cannot divide `y`, but must divide `(j-i)y`, hence `j-i`. It would then be at most `t` and would divide `y`, a contradiction.

The other role of the deleted multiplier was to make `y` exceed all pending-state encodings. This role is now supplied by the binomial size itself.

Given a finite refutation, first unfold or otherwise choose a finite backward Horn derivation with a finite maximum number `m_*` of nontruth pending formula occurrences. This number is independent of `F`. Choose the cofinal horizon so large that every local parameter is below `t`, the derivation fits, and `m_*<=t-1`. Padding by truth steps does not increase this maximum.

Every pending state is a product of at most `t-1` weights `1+Fj` with `0<=j<L`, so

\[
S\le(1+FL)^{t-1}\le(2FL)^{t-1}.
\]

Meanwhile,

\[
B=\prod_{j=1}^{t}\frac{F+j}{j}\ge\frac{F^t}{t!},
\qquad y=FB\ge\frac{F^{t+1}}{t!}.
\]

Using `F>=L^t`, `t!<=t^t`, and `L>=2t` gives

\[
\frac{y}{(2FL)^{t-1}}
\ge\frac{F^2}{t!\,2^{t-1}L^{t-1}}
\ge\frac{L^{t+1}}{2^{t-1}t^t}
=\frac{L^2}{t}\left(\frac{L}{2t}\right)^{t-1}>1.
\]

Here `L=8^(d-1)t^d>=2t` is immediate from `d=2^19` and `t>=32`. Thus every required pending state is strictly below `y`, including the initial state `F+1`. This is a uniform bound after `F` is chosen; no circular choice of `F` from an already-generated state path is required.

The parent's finite beta CRT can therefore choose an arbitrarily large positive `x` with all correct state residues and the endpoints. Set `N=B^x`. Since `B` is odd, `N` is odd. The generalized binomial CRT and the even cofinal choice of `C` proceed exactly as in the parent. All subsequent radix and shared-Pell witnesses are chosen only after these data are fixed.

## 8. Soundness and completeness conclusions

Soundness proceeds as follows:

1. The independent new Pell block proves `F` even, nonzero, and `|F|>t`.
2. The retained main frame authenticates the signed nominal indices.
3. The selector and new product row prove `B!=0` and `|y|>=|F|`.
4. The unchanged sign bootstrap gives `F>0`, `y>0`, `C>0`, `x>=F+1`, and `x>=2+(t+1)y`.
5. Positive `F` strengthens the Pell-index lower bound to give `F>=L^t`.
6. The unchanged digit argument authenticates `B=binom(F+t,t)>1`, so `y>F`.
7. The retained range compiler and finite-product separation decode a C222 refutation.

Completeness proceeds as follows:

1. Fix a finite refutation and finite backward pending-state schedule.
2. Choose a cofinal horizon `t=32c^(2k)` exceeding all its finite requirements and with maximum pending multiplicity at most `t-1`.
3. Choose a positive Pell index by the finite CRT in Section 6. This supplies positive `F`, all prime support through `t`, an odd binomial selector `B`, and the growth rows.
4. Set `y=FB`. Section 7 gives pairwise coprime beta moduli and enough capacity for every state.
5. Apply the retained beta and generalized CRT constructions; then choose `C`, the radix, the true power outputs, and the shared-Pell witnesses in the parent's original order.

Thus the changed semantic source has a zero exactly when the parent's calibrated C222 calculus has a finite refutation. Negating this equivalence gives the required no-zero/Con(ZFC) equivalence when composed with the explicitly named inherited logical calibration.

## 9. Artifact-binding cautions and rejected variant

The new coefficient checker should explicitly verify the changed horizon row, all three growth rows, the new `y-FB` row, deletion of the unique old multiplier coordinate, and the inverse of any old beta-coordinate shear before projecting. All retained frame occurrences of `F`, `t`, `y`, and other nominal indices must remain bound to their actual coordinates. These are finite algebra obligations separate from the unbounded proof above.

Setting `y=B` is not justified by this proof. For many primes `p<=t`, a highly divisible `F` makes `binom(F+t,t)=1 (mod p)`, so the required prime support is lost. The factor `F` in `y=FB` has a substantive role. It cannot be dropped merely because `B` is very large.

The inspected parent has other metric tradeoffs. A 209-variable unrestricted-integer quartic should be described as an improvement of the matched 210-variable direct quartic, not as a global minimum among all Diophantine consistency equations.
