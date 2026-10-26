# Signed cofinal horizons, a reused CRT anchor, and oriented power pools

This is an ordinary proof delta for the literal constructions in `sources/` and
`equations/`. It is not an end-to-end proof-assistant certificate. The
immediate sources are ProveIt package 173 at commit
`02a78a08603cbae248c19c23a75907c6c6bd6443` and the delivered
`ConZFC_Oriented_Powers_2026-10-25` package (ZIP SHA-256
`b5f564d8afc22cd0d17fd831f965baf9fa3423155229c7caa9b1084cddcbbaa2`).

## 1. The arithmetic change and why it needs a new proof

Package 173 reuses the CRT index C as the largest Pell index and removes the
old derived-label range request. Its uncontracted source has 221 integer
coordinates in the moderate-coefficient profile and 219 in the affine-growth
profile. It still retains three singleton power certificates and two same-base
pools. The Oriented Powers theorem replaces these ten private coordinates by
one, two, or three coordinates, depending on the chosen degree budget.

The old Oriented Powers application cannot simply be cited verbatim here.
That application derived B != 0 from a normalized factorial row `B*v_B=M`.
Package 173 has deleted that row. The parity identity below supplies the
missing bootstrap. We also replace the square horizon by a signed affine
progression. Its positive branch must be recovered from the remaining
arithmetic, rather than asserted as an extra domain condition.

All variables in the final equations range over unrestricted integers.
The letter z used for a horizon parameter is unrelated to a pool quotient.

### Moderate-coefficient source, `linear221`

Replace only the horizon row by

    t = 128 + 256*z.

Keep `T=t^2`, `K=T^2=t^4`, and the existing power request `F=t^K`.
Thus `|t|>=128`, `4|t`, and K is a positive even integer before a sign has
been assigned to t. The progression contains arbitrarily large positive t.

### Smaller-source profile, `linear219`

Replace only the horizon row by

    t = 16 + 32*z.

Keep `K=2^20*t` as a polynomial abbreviation in the existing power request
`F=t^K`. Thus `|t|>=16` and `4|t`. The progression again is cofinal.
The multiplier `2^20` and its squared occurrence in the frame increase
literal coefficient size; this is explicitly a size tradeoff.

No statement that the old and new square/linear horizon slices have equal
pointwise zero sets is made. The theorem is existence equivalence with the
same finite-refutation predicate, using the cofinal completeness construction.

## 2. Canonical Pell data precede all arithmetic sign recovery

The retained signed square-frame and cap rows are unchanged. Their proof in
package 173 obtains a signed integer A and an integer W with

    W>=258, |A|>W^W,

and canonical signed Pell coordinates for every nominal index k. Every
actual requested base n, output m, and index k satisfies

    n^2<W, m^2<W, k^2<W.

The preliminary cap proof uses squares and absolute values. It neither
assumes t positive nor interprets a requested power before classifying and
orienting its Pell pair. In particular it first classifies the C anchor at
absolute index |C|, proves C != 0, and recovers its canonical signed index.
The later q+1 power will recover the sign of C.

The finite checker `verify_composition.py` independently authenticates all
sixteen requests, their fourteen distinct Pell pairs, the actual shifted AY
wires, all Pell norm rows, the complete signed orientation polynomial, and
every actual frame atom. In particular the first q-block request is **q^t**,
not q^(t+1). Some inherited explanatory prose uses t+1; the literal equation
and the new proof use t. The frame also contains the atom t+1, but that does
not alter the request's exponent.

## 3. Oriented pooling, allowing temporary zero bases

For a block at integer base n with canonical Pell pairs `(X_i,Y_i)` write
`D_i=X_i-A*Y_i`, and put

    T_n = 2*A*n-n^2-1,
    E_n = sum_i ((m_i-D_i)^2-Y_i^2)
          -2*n*sum_i Y_i*(m_i-X_i).

The five bases in this source are `t,B,BH,q,q+1`; their request counts are
1,1,1,3,10. Every T_n is nonzero even when n=0, since then T_n=-1.
For nonzero n its sign is sign(A*n). The inherited oriented-pooling theorem,
whose hypotheses the retained frame satisfies, gives the following exact
local equivalence:

    sum_j n_j*E_j*product_(l!=j) T_l
       - z*product_j T_j = 0

has an integer z if and only if every request at an actual nonzero base is
exact as a rational signed-index power. A zero-base block contributes zero
and is temporarily unconstrained. This is intentional.

The proof is algebraic plus a strict magnitude bound. Define
`delta_i=m_i-X_i+(A-n_i)Y_i`. Then

    E_j - T_j*sum_i Y_i^2 = sum_i delta_i^2.

After clearing signed index denominators, the pool makes a sum of rational
squared errors an integer of absolute value less than one. The weights n_j
ensure all nonzero error summands have the same sign. Hence every error is
zero. Pairwise coprimality of the T_j is unnecessary. The full theorem in
the inherited `proofs/ORIENTED_POOLING.md` permits at most five bases and
seventeen requests; this composition uses only sixteen.

Three literal partitions are supplied. `all5` uses one base-weighted pool.
`staged` uses one base-weighted pool for t,B,BH and an unweighted reciprocal
pool for q,q+1. `paired` retains the direct singleton quotient for t,
base-weights the pair B,BH, and uses an unweighted reciprocal pool for q,q+1.
For the latter two partitions, q and q+1 have the same sign once neither is
zero, which is established before invoking their unweighted pool.

## 4. New parity bootstrap: all five bases are nonzero

The first base t is nonzero and has absolute value at least sixteen. Its
singleton or first oriented pool therefore enforces `F=t^K` exactly.

For `linear219`, the signed-power theorem gives K>=0. Since K=2^20*t and
`t!=0`, this already forces t>=16 and K>0. For `linear221`, K=t^4 is a
positive even integer regardless of the current sign of t. In both profiles
F is a positive even integer and F>|t|.

The retained CRT index identity is

    B*u = C+F+1,   C=2*c.

Its right side is odd. Consequently B is odd and nonzero. This conclusion
uses neither a binomial interpretation nor a deleted factorial certificate.
The retained self-radix definition has

    BH = B*(2+4*S),

where S is an integer sum of the actual CRT representatives. Its multiplier
is 2 modulo 4, and so is nonzero with absolute value at least two. Thus
`|BH|>=2`. The B and BH blocks are now active; in particular the BH request
forces x>=0 and `q=(BH)^x`. It follows already that q is neither 0 nor -1:
if x=0 then q=1; if x>0 then |q|>=2. Therefore q+1 is nonzero as well.
All five blocks are active. Every one of the sixteen old power requests
is recovered, including the q and q+1 requests in the unweighted partition.

This gives an integral inverse to the deleted certificate coordinates on
the zero set. For a singleton restore T by its defining polynomial and
its old quotient by `-delta/T`; exact power congruence proves integrality.
For an old same-base pool restore

    L=E/T, K_pool=2*sum_i Y_i*(m_i-X_i)+(2*A-n)*L.

Both original quadratic pool rows then hold. The finite checker verifies
the literal identities and every affine chart offset.

## 5. New endpoint bootstrap for the moderate-coefficient horizon

For `linear221` only, positivity of t remains to be recovered after the
first power. Do not discard the beta endpoint rows. They give

    y=F*(2*v+1),
    g=1+(t+1)*y,
    x=1+g*u_t.

Since |y|>=F and |t|>=128,

    |g| >= |t+1|*F-1 >= 127*F-1 > 1.

If x=0, the last equation would give `g*u_t=-1`, impossible in integers.
Together with x>=0 from the BH request this proves x>=1. Hence |q|>=2.
The retained exact power at base q and nominal index t forces t>=0.
The affine progression has no zero value, so t>=128.

There is deliberately no argument claiming that x=0 makes
`B=2^(F+t)`. The digit row has a free high quotient and would give a
sum involving that quotient. The endpoint-divisor proof above avoids this
false inference entirely.

The same endpoint argument is compatible with `linear219`, although there
t's sign was already recovered from K=2^20*t.

## 6. Soundness and completeness

Soundness now has precisely the hypotheses needed by the arithmetic part of
package 173: t is a sufficiently large positive multiple of four; F=t^K;
all sixteen requested powers are exact; C is the same nonzero even CRT
anchor; the retained square budgets and local numerical-calculus rows hold.
For `linear221`, t^4>=2^20*t because t>=128; for `linear219`, equality holds
in the growth exponent. Consequently its label-separation bound, local CRT
decoding, and Horn-flow recovery yield a finite C222 refutation. The same
identified C222-to-ZF and ZF-to-ZFC syntactic calibration gives a finite ZFC
refutation. No consistency assumption enters this direction.

For completeness, start with any finite C222 refutation. Choose the horizon
t sufficiently large in the new positive affine progression. Package 173's
construction needs a cofinal positive horizon divisible by four and the
stated growth inequality, not a specific square representation. All local
label bounds, binomial parity, and cofinal CRT choices therefore apply.
In particular the CRT index C can still be chosen positive, even, and larger
than the other nominal indices. Complete all old Pell and arithmetic
witnesses. The oriented-pooling theorem supplies integral new quotient
witnesses, and the new affine horizon parameter is integral by construction.
Thus the new source has a zero.

Combining these directions gives, in ordinary mathematics formalizable in
ZFC, for each emitted source and each proved polynomial projection P,

    ZFC proves [not exists x in Z^n, P(x)=0] iff Con(ZFC),

with the same explicit inherited calibration boundary as package 173.
No global simplest-polynomial theorem or new kernel-checked ZFC derivation
is claimed.

## 7. Acyclic integer projections and exact complexity

A selected residual has the form `epsilon*v+f=0`, with epsilon=+1 or -1,
and v absent from f. It uniquely reconstructs v as the integer polynomial
`-epsilon*f`. Each supplied list of these definitions is acyclic. Substitute
them into the unselected residuals and sum their squares. This is an exact
bijection between zeros of the reduced equation and source zeros, with
an explicitly ordered integer-polynomial reconstruction map.

The builders retain each oriented pool factored in the final straight-line
circuit. Every operation is addition, subtraction, or multiplication of
integer constants and quantified coordinates. Named registers are not extra
unknowns; there is no variable exponent in any final polynomial.

The independent checker expands every local circuit block at its declared
source-variable cuts, checks the entire source-row partition and every unit
pivot, and re-evaluates the degree certificate. A nonzero leading homogeneous
specialization modulo 1,000,000,007 proves the maximal residual's degree.
Its square cannot cancel against other real polynomial squares. Every
input's actual occurrence is certified by an explicit nonzero modular formal
derivative. Coefficient heights are bounded by propagated l1 norms; the
reported power-of-two bounds are upper bounds, not exact heights.
