# Recycle the Pell quotient as the center witness

Research contribution, 25 October 2026. This is an ordinary mathematical
proof, not a proof-assistant certificate. It is derived relative to ProveIt
commit `cdfea7d90176775d74c1c30afbe49fa78ade9897`.

## New theorem

For a positive integer a >= 2 define X_n(a), Y_n(a) by

    (a + sqrt(a^2-1))^n = X_n(a) + Y_n(a)*sqrt(a^2-1).

Let q and Omega be positive odd integers such that every prime dividing
Omega divides q. Let W0 >= 2 be arbitrary, and set

    W = q^2 W0,
    K = W^3 (W+2),
    A0 = 1 + q^2/[2(q+1)] mod Omega.

Then there are arbitrarily large positive odd integers k such that, on setting

    L = X_(Wk)(W+1),
    r = Y_(Wk)(W+1)/W,
    A = L^2 + 2r^2,

one has

    r is a positive odd integer,
    L^2 - K*r^2 = 1,
    A = A0 mod Omega.

In particular A >= L^2 and A is cofinal in the positive integers. The
existing frame witness z=(r-1)/2 also serves as the entire center witness.
No new coordinate records k or a modular square root. These occur only in
the completeness proof.

The case Omega=1 is immediate from k=1,3,5,... . Assume Omega>1 below.

## Lemma 1: the divided frame ordinate is a local unit

Let p be odd and p^2 divide W. Put a=W+1, D=W(W+2),

    b=Y_W(a)/W, c=X_W(a).

The recurrence modulo W gives Y_n(W+1)=n mod W, so b is an integer.
The binomial expansion gives

    b = sum_(j>=0) [binom(W,2j+1)/W] a^(W-2j-1) D^j.

Only indices 2j+1<=W occur. For j=0 the term is a^(W-1)=1 mod p.
For j>=1, the identity

    binom(W,h) = (W/h) binom(W-1,h-1)

shows that the p-adic valuation of its coefficient after division by W
is at least -v_p(2j+1). Hence the whole term has valuation at least

    2j - v_p(2j+1) >= 1.

Although individual displayed coefficients can be rational, their p-adic
valuation estimates are legitimate and each full term is p-integral.
Consequently b=1 mod p. Also c=1 mod p by reduction of the scalar
binomial expansion. The Pell identity gives

    c^2-1 = D W^2 b^2.

Since p is odd and c=1 mod p, c+1 is a unit, and c=1 mod p^6. The weaker
c=1 mod p^2 will suffice.

The p^2 hypothesis cannot simply be weakened to p: at W=3,p=3,
Y_3(4)/3=21 is divisible by 3.

## Lemma 2: an elementary Pell-index permutation

If p is odd and c=1 mod p^2, then for every a>=0 and every k>=0,

    Y_(k+p^a)(c)-Y_k(c) = p^a mod p^(a+1).

For h=p^a, use the binomial expansions of X_h(c) and Y_h(c) in
c and D'=c^2-1. The bound

    v_p(binom(h,j)) >= a-v_p(j)

and v_p(D')>=2 show

    X_h(c)=1 mod p^(a+1),
    Y_h(c)=p^a mod p^(a+1).

Indeed every non-leading term in the ordinate has valuation at least
a+2j-v_p(2j+1)>=a+1. Every non-leading scalar term has valuation at
least a+2j-v_p(2j)>=a+1. The leading scalar c^h is 1 modulo p^(a+1)
by the binomial theorem (or the elementary lifting-the-exponent identity).
The case a=0 follows directly. Since X_k(c)=1 mod p, the addition identity

    Y_(k+h)(c)=X_h(c)Y_k(c)+X_k(c)Y_h(c)

proves the claimed congruence.

Thus k -> Y_k(c) induces a bijection modulo p^a for every a>=1.
There is a unique solution modulo p at the first step; at each lift,
adding t p^a changes the next base-p digit by t. Multiplication by any
p-adic unit b preserves bijectivity.

The composition identity

    Y_(Wk)(W+1)/W = b Y_k(c)

and Lemma 1 show that k -> r(k) is a bijection modulo every prime power
dividing Omega. The map is periodic modulo that prime power, so CRT makes
it a bijection modulo Omega as well.

## Proof of the center theorem

For each p dividing Omega, p divides q and p^2 divides W. Therefore

    2(q+1)(K+2) = 4 mod p.

The two simple roots +/-2 of its square-root equation modulo p lift to
the required powers of p by the elementary Hensel step: if d^2 is correct
modulo p^a, the correction d+t p^a is chosen using the invertible coefficient
2d modulo p. CRT gives a unit d modulo Omega with

    d^2 = 2(q+1)(K+2) mod Omega.

Choose the unique k class modulo Omega for which r(k)=q/d mod Omega.
Since Omega is odd, that class has a positive odd representative. Adding
2 Omega to k preserves oddness and the required residue, so arbitrarily
large positive odd k are available.

The Pell identity gives L^2=1+K r^2, whence

    A = 1+(K+2)r^2
      = 1+q^2/[2(q+1)] mod Omega.

The integer r is odd for odd k. To see this, first Y_W(W+1)/W is odd:
if W is odd, its numerator is odd, since odd-index ordinates are odd;
if W is even, W+1 is odd, all abscissae are odd, and
Y_(2j)=2X_jY_j proves v_2(Y_W)=v_2(W). Finally Y_k(c) is odd for odd k,
regardless of the parity of c. Positivity and cofinal growth follow from
the ordinary real Pell embedding, or directly from the positive recurrence.

## Application to package 166

Use `166-fixed-base-modular/stages/compressed/raw_source.json` as the exact
untranslated source. Its relevant coordinates are:

| Coordinate | Source index |
|---|---:|
| `shared.W` | 245 |
| `shared.A` | 246 |
| `shared.Zminus1` | 247 |
| `pow2.output` (q) | resolved by name in code |
| `frame.L` | 560 |
| `free_A.u` | 561 |
| `free_A.v` | 562 |

The code resolves every index by its exact name and checks all source rows.

An exact occurrence audit in the untranslated source finds `shared.W` only
in rows 183, 184 (the two products of the lower Pell frame) and row 361
(its magnitude definition). The two product helpers occur only in those
rows and in the frame norm row 185. Its value is not used as a semantic
proof index or in any digit or power request. The bound parameter for all
other arguments is mathematical and need not be an extra polynomial input.

Replace the frame row

    shared.W - W0 = 0

by

    shared.W - q^2 W0 = 0.

Here W0 is exactly the old polynomial `2+sum(atom^2)`; the stored source
row is already expanded with its affine atom offsets. Replace

    A - L^2 - u^2 - v^2 = 0

by

    A - L^2 - 2(2*shared.Zminus1+1)^2 = 0.

Delete the two now-unused private center coordinates u,v. All other rows
remain literally unchanged, up to renumbering these deleted coordinates.

### Soundness order

The affine radix row gives q=6z+3, so |q|>=3 before exact powers or digit
semantics are recovered. Thus W=q^2 W0>=W0>=2 at every integer zero.
All old magnitude lower bounds hold. The frame equation is unchanged and
the new center has A>=L^2. The inherited signed Pell recovery and sign
bootstrap therefore apply without using the sign or nonzeroness of
Omega=N*q^x. Only after that recovery is Omega interpreted, exactly as in
the parent. In particular no circular nonzero-modulus assumption occurs.

### Completeness order

Construct semantic proof data and exact positive odd q,Omega as in the
parent. Compute W0, then W=q^2W0. Apply the theorem to choose the common
frame and center, with the center made as large as the inherited orientation
construction needs. The existing frame quotient supplies z; no private
center coordinate remains. Continue the parent's simultaneous Pell witnesses
and digit construction unchanged. Theorem hypotheses rad(Omega)|q and
oddness hold because Omega=N*q^x, N=B^x, q=(BH)^x with odd B,q.

### Scope and costs

This is a zero-existence equivalence, not a pointwise map on arbitrary parent
center witnesses. It deletes two free center coordinates relative to package
166 and one relative to the late one-square archive. The raw frame residual
becomes degree four, hence its squared contribution has degree eight; all
other raw residuals remain quadratic. Quadraticization would introduce new
gate coordinates and might erase the variable saving. Projection and exact
coefficient counts must be recomputed; no dimension or degree claim for a
projected endpoint follows just from this local theorem.

The late `ConZFC_Cofinal_Pell_Compression_2026-10-25.zip` already proves that
an even cofinal frame permits a separate center A=L^2+2u^2. The present
change identifies the slack with the frame's existing quotient, using a
q-divisible frame and the local permutation lemma. Its contribution is that
identification and its soundness/completeness proof, not the older scaled
square or the inherited proof-calculus calibration.

## A signed-frame sextic variant

This optional refinement sets W=q W0 instead of q^2 W0. The frame residual
has degree three, so its squared contribution has degree six. The center
row and its quotient reuse are unchanged. The following soundness argument
is required; positivity of W must not be presumed.

At every zero the affine radix gives |q|>=3, so F=|W|>=3W0>=6. If W>0,
the inherited frame proof applies. If W=-F<0, its norm equation is

    L^2 - F^3(F-2) r^2 = 1,   r odd and nonzero.

Write a=F-1>=5 and Y=F|r|. All positive integer solutions of
X^2-(a^2-1)Y^2=1 are X=X_n(a), Y=Y_n(a) for n>=1, as follows from
the elementary Pell descent by the least positive unit a+sqrt(a^2-1).
Modulo F, a=-1 and the recurrence gives

    Y_n(a)=(-1)^(n-1)n mod F.

Thus F divides n, whence |L|>=X_F(F-1). The binomial expansion immediately
gives X_F(F-1)>=(F-1)^F, and therefore

    A >= L^2 >= (F-1)^(2F) > F^F.

This is the large-center inequality needed in the source signed-power
lemmas, with the positive bound parameter F in place of W. All original
atoms satisfy their same strict bounds because F>=W0. No polynomial row
outside the listed frame definition and norm block uses W, so no other semantic
substitution of a signed value is being made.

For completeness, the parent already constructs q=(BH)^x with x>2^32,
B,H positive odd. Thus v_p(q)>=x>=2 for every p dividing Omega=N*q^x.
Consequently p^2 divides W=q W0 and Lemmas 1 and 2 apply verbatim. The
canonical W is positive. Every other step of the center theorem and the
parent completeness argument remains unchanged. This branch exploits the
source's authentic powerful q; the generic q^2 branch requires no such
additional hypothesis on q.

## Formalization scope

All modular lifting steps are finite elementary algorithms: repeated
Euclidean division, modular inversion, square-root digit lifting with
invertible derivative, the inductive Pell-index lift, and finite CRT.
They are defined by bounded searches or primitive recursion once the
positive input integers are fixed. The unbounded choice of a sufficiently
large k is an elementary arithmetic progression, and Pell growth is proved
by induction. The proofs are ordinary ZFC arithmetic proofs valid for all
internally quantified integers. They impose no external standardness,
transitivity, or omega-model assumption. Their composition with the
inherited C222/ZF/ZFC refutation calibration therefore has precisely the
same formalization scope as that calibration. The finite Python checks
corroborate the new formulas and authenticate their literal projection;
they do not decide consistency or substitute for the quantified argument.
