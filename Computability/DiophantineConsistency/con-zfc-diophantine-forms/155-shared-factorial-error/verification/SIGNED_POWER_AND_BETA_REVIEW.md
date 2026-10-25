# Signed power requests and final arithmetic review

**Final status.** The approved primary construction uses the affine odd
radix `q=2z+1` and the ORIGINAL beta base `y=V(V-1)`. The optional augmented
beta-base analysis retained in Sections 2--4 below is research history,
not a premise or modification of the final equation. Section 6 gives the
final stronger bootstrap; the complete integrated proof is in
`paper_main.tex`. This is an internal AI-assisted mathematical review,
not external peer review.

Independent ordinary-mathematics review for the current research iteration.
This review checks the stated lemmas and their interfaces. It does not assert a
new foundational formalization or an end-to-end proof-assistant build.

## 1. Signed-base canonical power lemma

Let `W >= 3` be an integer, let `A,n,k,m` be integers satisfying

    |A| > W^W,  2 <= |n| < W,  |k| < W,  |m| < W,

and put `T = 2*A*n - n*n - 1`. Suppose the relevant pair is the canonical
signed-index Pell pair `(X_k(A),Y_k(A))`, with
`X_{-k}(A)=X_k(A)` and `Y_{-k}(A)=-Y_k(A)`, and the power row states

    X_k(A) + (n-A)*Y_k(A) = m modulo T.

Then `k >= 0` and `m = n^k`. In particular this lemma does not require
either `A` or `n` to be positive.

Proof. By the reverse triangle inequality,

    |T| >= 2|A||n| - n^2 - 1
         > 4 W^W - (W-1)^2 - 1
         > W^W + W.

The last inequality is valid for every integer `W>=3` (the actual source
has `W>=258`). In the quotient ring modulo `T`, the element `n-A` has square
`A^2-1`, and `n*(2A-n)=1`. Thus evaluation of the Pell recurrence gives the
usual identity for every signed index: for `k>=0`, the left side is
`n^k`; for `k=-j<0`, its product with `n^j` is one.

In the nonnegative case,

    |m-n^k| <= (W-1)+(W-1)^(W-1) < |T|,

so congruence implies equality. In the negative case,

    |m*n^j-1| <= (W-1)^W+1 < |T|,

so `m*n^j=1`, impossible for integral `m` and `|n|>=2`, `j>=1`.

At `n=1` and ANY signed integer index the same canonical recurrence gives
`m=1`. At `n=-1` it gives `m=(-1)^k`; a negative index cannot be excluded
there. At `n=0` no useful large-modulus statement applies. These boundary
cases must not be silently included in the `|n|>=2` conclusion.

### Source frame coverage

The frozen `direct/baseline/factored_source.json` of the incoming
`ConZFC_Symmetric_Remainders_2026-10-25` package has variable 522 named
`self_radix.BH`. Its `shared.frame_definition` contains the summand
`-[522,522]`, and `self_radix.base_definition` identifies this wire with
`B*(1+sum(actual nine representatives))`. The `base2.T_definition` and
corresponding power row use this same wire. The frame already bounds
`|BH|<W`; no new bound atom is needed merely to permit its negative sign.

### Orientation caveat

The package's cheaper linear pool selects only nine abscissas. Its x pair
is deliberately not selected; the old proof instead orients it from a
positive output `q` and an already-positive base `BH`.

That argument fails if `B` is provisionally negative. For a negative base
`n`, a negative odd index `k=-j` and the opposite abscissa give the
congruence/equality `m=-n^j`, which is positive. Thus `q>0` by itself does
not orient the x pair over a signed base. A safe replacement adds
`1-X_x` to the same pool. The finite-residue argument remains unchanged,
using ten nonnegative residues in `{0,2}` instead of nine. It adds no
unknown and allows the signed-base canonical lemma above to be applied.

## 2. Replacing the cofinal beta base

Let `t>=16`, `F=t!`, `V=(F^2+1)^t`, and

    B = binom(F^2+t,t) = product_(i=1)^t (1+F^2/i).

Define

    y = V*(V-1) + (B-1)^2.

Then `y >= V*(V-1)`, and `F^2` divides `y`. Indeed, `V=1 mod F^2`.
Since each `i` divides `F`, every factor `1+F^2/i` is one modulo `F`;
hence `B=1 mod F`, and `(B-1)^2=0 mod F^2`.

Consequently the first beta-CRT moduli `1+(i+1)y`, `0<=i<=t`, are pairwise
coprime by exactly the old argument: a common prime for two distinct
moduli divides the index difference, is at most `t`, hence divides `F`
and `y`, and so cannot divide either modulus. Every old accumulator-size
bound remains valid because the new `y` is at least the old one. Endpoint
identities give the same `x>=2+(t+1)y` bound, with the actual larger `y`.
The strict amplification proof and all range lower-index bounds use this
inequality and `y>=F+1`; they do not require equality with `V*(V-1)`.

Completeness stays acyclic:

    choose t; then F,V,B; then y; then beta code x;
    then N=B^x and CRT representatives; then q and private Pell data.

The early benefit is independent of those meanings: for arbitrary integers
`V,B`, `V*(V-1)>=0`; if `|B|>=2`, then `(B-1)^2>=1`, so `y>=1` before
the sign of `F`, the factorial identity, or the powers at base `B` are known.

## 3. A slightly sparser beta variant

The alternative

    y = V*(V-1) + B^2 - 1

has `y>=3` whenever `|B|>=2`, and also dominates the old beta base after
`B>=2`. It satisfies `F|y`, which is precisely the divisibility used in
the inherited beta-CRT construction; it need not satisfy `F^2|y`.
The inherited source closure was searched for uses of the original
literal beta definition. The relevant arguments use only dominance of
the accumulator bound, `F|y`, and the endpoint growth bound. Thus the
sparser variant is also valid if the final package states and uses only
the required `F|y` property. It removes the linear `-2B` term in the beta
definition, but exact final support must be measured after projection.

## Scope

These are unbounded algebraic and arithmetic proofs. Finite evaluation
cannot replace them. Sections 1--3 supply reusable lemmas rather than
the entire bootstrap: the complete construction must check which scalar
guards are retained, where `|B|>=2` and `q>=2` are proved, and whether the
x pair is oriented. Sections 4--5 below review those premises for the
parent's subsequently supplied concrete construction.

## 4. Review of the revised common-remainder bootstrap

The parent subsequently specified the following actual revision. It retains
the original fourteen squared-abscissa orientation terms, so the caveat in
Section 1 is resolved without adding a new orientation mechanism. Put
`M=q^x`, retain the common normalized remainder rows and their ratio rows,
and add integer variables `vB,S` with

    B*vB=M,                 M*F=vB*V+S.

The common norm now bounds the eleven normalized remainders together with
`S`: its form is

    M^2 = 1 + 4*(sum_i R_i^2 + S^2) + a^2+b^2+c(c+1).

Also set `q=(2z+1)^2` and replace the beta base by
`y=V(V-1)+(B-1)^2`. The former three scalar sign guards for the factorial
interval and the radix gap are removed. The following is an acyclic
ordinary proof of their eventual recovery.

1. The frame, deterministic anchor, and full orientation pool recover the
   canonical signed-index pairs before interpreting front signs. The known
   positive horizon `t>=16` therefore gives `V=(F^2+1)^t>=1`, including
   `F=0`. The common norm gives `M!=0`. Thus `B,vB!=0`, and its bound on
   `S` gives, with `b=|B|` and the integral error `s=BF-V`,

       s=S/vB,             |s|<b/2.

2. If `F=0`, then `V=1`, `s=-1`, and `b>=3`. If `F!=0`, put `f=|F|`.
   Opposite signs of `B,F` would give `|BF-V|=bf+V>b/2`, impossible.
   Hence `BF=bf`. If `b<=f`, then

       V < b*(f+1/2) <= f^2+f/2,

   contrary to `V>=(f^2+1)^2>f^2+f/2`. Therefore `b>f`, `b>=2`, and
   `V<b*(f+1/2)<b^2`. The inequality `V<b^2` also holds in the zero case.
   None of these deductions uses the factorial digit.

3. The odd-square equation gives `q>=1`, so base `q+1>=2` in the nine
   representative requests makes all actual representatives nonnegative.
   Thus `H=1+sum representatives>=1`, and `|BH|>=2`. The signed-base lemma
   at `BH` gives `x>=0` and `q=(BH)^x`. The new beta formula gives `y>=1`
   even before the sign of `F`. The final endpoint

       x=1+[1+(t+1)y]*ut

   excludes `x=0`, hence `x>=1` and `q>=2`.

4. The already present normalization ratio
   `q^(t+1)*v=M=q^x` forces `x>=t+1`. The final endpoint now forces
   `ut>=1`, hence `x>=2+(t+1)y>=t+3`. In particular

       q=|BH|^x >= b^(t+3).

5. For `F!=0`, every needed factorial-row coefficient
   `binom(F^2+t,j)`, `0<=j<=t`, is at most `V<b^2`; the displayed radix
   lower bound makes all low digits very small. The standard geometric
   sum gives canonical low residue `c<q^t/32`. For `F=0`, use the direct
   coefficient bound `binom(t,j)<=2^t` instead of the inapplicable bound
   by `V=1`; since `b>=3` and `q>=3^(t+3)`, it gives `c<q^t/2` (indeed
   `c<q^t/32` is also available).

   The common norm bounds the supplied normalized remainder by `M/2`.
   Its canonical normalized remainder is `(M/q^t)*c<M/2`. Since the two
   are congruent modulo `M`, they are equal. The digit row then gives
   `B=binom(F^2+t,t) mod q`. In either case
   `|B|+binom(F^2+t,t)<q`, so this is an ordinary equality. Hence `B>0`.
   The case `F=0` would give `B=1`, contrary to `b>=3`. Thus `F>0` too.

6. Write

       R_t(F)=(F^2+1)^t/binom(F^2+t,t).

   The bound `|s|<B/2` gives `|F-R_t(F)|<1/2`. The nearest-integer
   factorial argument applies at `t>=16`; a short sufficient derivation
   is included below. It yields `F=t!` and

       0 < F-R_t(F) < 1/32.

   Therefore `0<s<B/32`, so the old slack is nonnegative and
   `r=B-s-1>=0`. Also `q>B` restores the old radix gap. The beta formula
   is the only remaining semantic change, and Section 2 verifies all of
   its required CRT and growth properties. The inherited range/Horn
   decoding can consequently be applied to the restored semantic front.

### A sufficient nearest-integer estimate

For every positive `F`, each factor in `R_t(F)` increases with `F`, so
`R_t(F)>=R_t(1)=2^t/(t+1)`. For `t>=16`, this lower bound exceeds
`t^2+1/2`; the inequality holds at 16 and its left side grows faster than
the displayed quadratic. Thus `|F-R_t(F)|<1/2` implies `F>t^2`.

The product formula and `product(1-u_i)>=1-sum u_i` give

    R_t(F) = t! product_(i=2)^t (1-(i-1)/(F^2+i)),
    t!*(1-t*(t-1)/(2F^2)) <= R_t(F) < t!.

Since `F>t^2`, the lower bound is greater than `t!/2+1/2`, so
`F>t!/2`. Returning to the same estimate gives

    0 < t!-R_t(F) < 2*t*(t-1)/t! < 1/32.

The last inequality holds at `t=16` and remains valid as `t` increases.
Now an integer within one half of `R_t(F)` must be `t!`, proving the
claim. These inequalities are intentionally much weaker than the actual
canonical margins.

### Completeness parity choices

The odd-square radix imposes a real condition, so it needs a constructive
explanation. At `F=t!`, both `V` and `B` are odd and the new `y` is even.
Every beta modulus is odd. Thus the beta CRT class contains arbitrarily
large even codes `x`. Choose such an even code.

Also `N^2=B^(2x)` is odd. Every representative can be shifted by `N^2`
without changing its required CRT residues, while reversing its parity.
Choose the seven representatives other than `a,b` to have odd total
parity, then choose the dominant `a` to have parity opposite `b`. The
constructor identity `h=1+a+b mod 2` gives an even dominant anchor `h`,
while the sum of all nine representatives is even and `H` is odd. The
existing size bounds are preserved by choosing ordinary representatives
in `(0,2N^2]` and the dominant one in `[2N^2,4N^2)`.

Thus `q=(BH)^x` is an odd square and `z=((BH)^(x/2)-1)/2` is an integer.
The requested new quotient is `vB=M/B`, integral because `M=q^x` and
`x>=1`; set `S=vB*(BF-V)`. Then `S/M=s/B<1/32`. Together with the eleven
canonical normalized remainders `R_i/M<1/32`, this gives

    4*(sum_i R_i^2+S^2) < (48/1024)*M^2 < M^2.

The nonnegative remaining integer has a representation
`a^2+b^2+c(c+1)`, supplying the common norm. All new private coordinates
are therefore constructible from a finite refutation.

## 5. Review of deterministic comparison-center compatibility

The center proof in `direct_composition/PROOF249.md`, with its retained
`DETERMINISTIC_CENTER_SOURCE_PROOF.md`, was checked separately. Its
anchor argument is independent of every front sign and remains valid
under the revised bootstrap above.

The identity

    D=A+(1-A)H^2=1-(A-1)(A^2-1)J^2

gives `D=A mod H`, `D=1 mod C`, and `|D|>1` at either permitted sign of
`A`. If the anchor has actual index `i>=2`, the condition `C^2|J` gives
`i|l` and `|C||l` for the common index `l`, by strong divisibility and
the Pell composition expansion. Abscissa residue separation yields
`j=+/-i mod 2l`; the ordinate residue yields `j=+/-h mod |C|`. Since
`Y_i(|A|)>=i+2|A|-2`, the small-range congruence forces `i=|h|<W`.

At `i=1`, the cap forces `h=0` and every other ordinate zero. Their
actual indices are then bounded independently of the desired conclusion.
The retained full squared orientation pool has a positive small residue,
including the anchor ordinate error one, strictly below `|A-1|`. Its
divisibility is impossible. This correctly closes the unit-ordinate case.

For completeness, choose the even dominant anchor `h` already supplied
by the parity construction. Then `C=Y_h(A)` is even and `U=X_h(A)` is
odd. At `l=hC`, Pell composition gives `J=C*Y_C(U)`. Because
`U^2-1=(A^2-1)C^2`, the binomial expansion gives

    Y_C(U)/C = U^(C-1) mod C.

In particular `J/C^2` is an odd integer, as required by the retained
odd-auxiliary row. The choices `S=X_h(D)`, `R=Y_h(D)` satisfy both
comparison congruences by polynomial transfer. Negative `D` is harmless
because these private variables are unrestricted integers.

No conditional status is needed for this comparison-center composition.
The exact final circuit and its row mutations remain the responsibility
of the separate finite checker; this review addresses the unbounded
mathematical argument and its dependency order.

## 6. Final stronger bootstrap: affine odd radix, original beta spacing

The final preferred route removes the odd-square requirement and keeps the
original beta formula without any change:

    q = 2z+1,               y = V(V-1).

All fourteen pairs retain their full squared abscissa and ordinate
orientation. The common radius gives M nonzero, B*v=M, and

    |BF-V| < |B|/2,         V=(F^2+1)^t.

The early argument above therefore gives b=|B|>=2, b>|F|, V<b^2;
if F=0, it gives b>=3.

For epsilon in {1,-1}, the power modulus is T=2A*epsilon-2.
Modulo T, twice A equals twice epsilon. Consequently the bi-infinite
Pell recurrence with initial values f_0=1, f_1=epsilon gives

    X_k(A)+(epsilon-A)Y_k(A) = epsilon^k mod T

for every signed integer k. Since |T|>2W^W-2>W, the framed power
output equals epsilon^k exactly. This applies to the actual literal
pow14 row

    -M+X_x-A*Y_x+q*Y_x-T_q*eta=0.

If q=1 or q=-1, it follows that |M|=1, contradicting B*v=M and
b>=2. Since q is odd, |q|>=3. In particular |q+1|>=2, so every
actual CRT representative is nonnegative by the signed-base power
lemma. Thus H>=1. The request at q gives x>=0 and M=q^x;
the ratio q^(t+1)*v_(t+1)=M forces x>=t+1. The request at BH gives

    q=(BH)^x,               |q|>=b^(t+1).

Let Q=|q|. The true factorial low polynomial is allowed to be signed:

    r_true=sum_(j=0)^(t-1) binom(F^2+t,j)*q^j.

For F nonzero its coefficients are <=V<b^2. For F=0 they are <=2^t
and b>=3. In both cases the elementary geometric bound yields
|r_true|<Q^t/32. The supplied normalized remainder reconstructs an
integer r with |r|<Q^t/2. Both are congruent to the exact numerator
modulo q^t, and therefore r=r_true. Dividing the exact digit equation
by q^t and reducing modulo q yields

    B = binom(F^2+t,t) mod q.

The difference has absolute value <Q, so equality holds. This makes B
positive. F=0 would give B=1, contradicting b>=3. Hence F is positive
by the established equality of signs of B and F. Finally q=(BH)^x
becomes positive. The nearest-integer factorial theorem then gives
F=t!, and both original factorial scalar guards and the original
output-slack guard can be restored after the fact.

The old beta definition now supplies all inherited endpoint and CRT
properties literally. In particular the first endpoint yields x>=F+1,
the final endpoint yields x>=2+(t+1)y, and all later denominators and
range-digit arguments have their original premises.

For completeness, choose the same even dominant semantic anchor and
choose H odd by the already verified parity adjustments modulo odd
N^2. B is odd, so q=(BH)^x is odd regardless of the parity of x.
Set z=(q-1)/2. No even-x restriction or enlarged beta spacing is needed.
The twelve normalized errors all satisfy the strict 1/32 margin,
and the common G-form represents the remaining nonnegative norm gap.

This final argument was independently cross-checked against the literal
power output, base, and frame rows. It introduces no extra source
assumption beyond the explicitly retained equations. Subsequent
coordinate and residual reductions are finite algebraic transformations
checked separately.
