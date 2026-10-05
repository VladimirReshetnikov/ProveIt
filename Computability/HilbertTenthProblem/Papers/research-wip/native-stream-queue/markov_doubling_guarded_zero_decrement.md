# Positive doubling masks for a guarded zero line and decrement

Normalized doubling does realize the guarded ZERO/DEC counter example
when ZERO is required to preserve only the zero-counter line. Explicit
rational masks give a common action scale 1/3. ZERO is a rank-one reset
away from its admissible line, so this does not contradict the full-action
identity/decrement obstruction. A full positive increment is impossible
on the same two-sine space, at any action scale.

This is a finite operator construction and interface check. It supplies
no fixed-arity unbounded history, universal computation, or integer gate
saving. Root supplied the two-mask construction and the sharper scale
1/3; the computations and domain checks below verify them independently.

## 1. Masks, normalization and strict positivity

Let theta=2 pi x and s_j(x)=sin(j theta). Define

    a_D=1+(10/9)cos(theta)-(2/9)cos(3 theta),
    a_Z=1+(2/3)cos(theta).

Only odd frequencies occur, so each mask satisfies
`a(x)+a(x+1/2)=2`. The zero mask is at least 1/3. For the decrement
mask, put t=cos(theta). Then

    9 a_D=9+16t-8t^3.

The odd cubic p(t)=16t-8t^3 has extreme absolute value on [-1,1]
at t=±sqrt(2/3), or at an endpoint. Its interior magnitude is
`(32/3)sqrt(2/3)`, whose square is 2048/27<81; its endpoint magnitude
is 8<9. Therefore a_D is strictly positive everywhere. Normalization
also puts it strictly below 2. No numerical approximation of the minimum
is needed. The common denominator of the displayed Fourier coefficients
is 9, although the action scale is 1/3.

For the normalized doubling operator

    (T_a h)(y)=[a(y/2)h(y/2)+a((y+1)/2)h((y+1)/2)]/2,

averaging retains exactly the even total Fourier exponents. Direct
product-to-sum identities give

    T_D s1=(2/3)s1-(1/9)s2,       T_D s2=s1,
    T_Z s1=(1/3)s1,              T_Z s2=s1.          (1)

There are no unlisted output frequencies in these identities.

## 2. Integral basis and the actual counter domain

Use the independent integral-coefficient basis

    f=3s1-s2,       g=-3s1.

Equation (1) becomes

    T_D f=f/3,      T_D g=(g-f)/3,
    T_Z f=0,        T_Z g=g/3.                       (2)

Thus the full matrices in basis (f,g) are D/3 and diag(0,1)/3,
respectively. For a nonnegative integer counter c, encode the signed
function `Phi_c=c f+g`. A positive scalar multiple H Phi_c is also an
allowed homogeneous representative. These are signed trigonometric
coordinates, not positive probability densities.

For c>=1, decrement satisfies `T_D Phi_c=Phi_(c-1)/3`. At c=0,
ZERO satisfies `T_Z Phi_0=Phi_0/3`. These are exactly the two admissible
counter actions. In positive-hat coordinates C=c+1, the encoded function
is `(C-1)f+g`, not `C f+g`; the zero state is C=1.

For strictly positive homogeneous hats X,H with C=X/H an integer hat,
the physical function is

    (X-H)f+H g.

At an admissible decrement its successor coordinates obey
`3X'=X-H, 3H'=H`; at an admissible zero step X=H they obey
`3X'=H, 3H'=H`. These are the previous guarded homogeneous equations
on their respective permitted branches. No assertion of equality of
the old and new operator actions away from those branches is made.

**Remark 1 (the zero guard remains necessary).** In fact `T_Z Phi_c=g/3`
for every c: without the explicit test c=0, this mask resets a positive
counter illegally. Likewise decrement at c=0 leaves the nonnegative
counter domain. Strict positivity of the masks supplies neither guard.
This construction must not inherit a cheaper packed history merely by
deleting its synchronized zero-test constraint.

## 3. No increment on this space

For every normalized doubling mask, regardless of its Fourier support,
the half-period-even function s2 satisfies `T_a s2=s1`. Since
`f+g=-s2` and `g=-3s1`, this forces

    T_a(f+g)=g/3.                                   (3)

A full increment at scale nu>0 would require

    T_a f=nu f,       T_a g=nu(f+g),

and hence `T_a(f+g)=nu(2f+g)`. Equation (3) is incompatible with the
independence of f,g. No higher-frequency continuous mask can evade this
fixed even-input relation. In particular the ZERO/DEC construction
does not immediately provide the INC/DEC instruction interface of a
universal counter program.

Even allowing a positive scale depending on c cannot realize projective
increment on all integer counter states in this fixed chart. Such an
operator maps the whole span into itself because two different state
vectors already span it. Write its matrix as [[p,q],[r,s]]. Requiring
the image of (c,1) to be a positive multiple of (c+1,1) for every c>=0
gives `pc+q=(rc+s)(c+1)` on infinitely many integers. Coefficient
comparison yields r=0 and p=q=s, with s>0. It is therefore a positive
constant multiple of the full increment matrix already excluded above.
State-dependent coordinate charts are a separate interface.

## 4. Action denominator three in this fixed two-sine family

For a fixed positive scale lambda, take
`f_lambda=s1-lambda s2`, `g_lambda=-s1`. A full action lambda D on
their span would have, in the physical basis (s1,s2), the matrix

    [[2lambda,1],[-lambda^2,0]].

The unique continuous normalized mask with this action is

    a_D(lambda)=1+2(2lambda-lambda^2)cos(theta)
                   -2lambda^2 cos(3 theta).         (4)

To verify uniqueness, the action on s1 gives
`(a-1)sin(theta)=2lambda sin(2theta)-lambda^2 sin(4theta)`.
Division away from the finite zeros of sin(theta) determines (4), and
continuity determines its values at those zeros. Thus a different
continuous mask cannot repair a failure of positivity of (4).

The zero-line mask is `a_Z(lambda)=1+2lambda cos(theta)`. The elementary
bound `a_D(lambda)>=1-4lambda` proves the construction for
0<lambda<1/4. Section 1 proves that lambda=1/3 also works, beyond that
sufficient bound. Scaling both basis vectors by 3 gives Section 2's
integral basis.

For lambda=1/q with positive integer q, formula (4) at cos(theta)=-1/2
has value `1-2/q-1/q^2`. This is -2 for q=1 and -1/4 for q=2.
Both fail positivity; q=3 succeeds by Section 1. Hence 3 is the minimum
positive integer reciprocal action denominator in this specified
two-sine Jordan family. This is not a denominator optimum over other
Fourier coordinate spaces or other guarded encodings, and it is not
the Fourier-coefficient denominator, which is 9 for a_D(1/3).

## 5. Paid integer interface and scope

The existing positive-integer guard graph can be retained with fixed
q=3. With positive integer hats C,C',B, let t=B-2 and u=C-1. Its two
residuals `t u` and `C'-u+t` force exactly ZERO and DEC by positivity.
With raw positive X,H,X',H',B, use

    t=B-2, u=X-H,
    t u=0,       3X'-u+tH=0,       3H'-H=0.         (5)

At zeros the positive domain forces B=1 or 2, and the equations give
exactly the two legal operator actions in Section 2. Arbitrary positive
X/H need not be integral; paid endpoint links or the existing integral
initialization remain necessary. Equation (5) uses the guard to replace
the off-branch reset action by the old affine transition expression;
there is no off-zero polynomial identity between the two operator laws.

The already proved literal templates, valid for every fixed integer q>=2,
give the following costs after choosing q=3:

| Interface | Full SOS operations | Positive witnesses |
|---|---:|---:|
| Direct one-step, supplied C,C' | 8=3M+5A | 1 |
| Raw ratio step, supplied X,H,X',H' | 14=7M+7A | 1 |
| Raw linked step, supplied C,C' | 22=11M+11A | 5 |
| Direct fixed duration T>=1 | 9T+1 | 2T |
| Raw fixed duration T>=1 | 15T+2 | 3T+1 |

These counts are inherited template consequences, not newly emitted or
executed arrays. Multiplication by the fixed numeral 3 remains one paid
multiplication, just as for 5 or 7. No integer operation count improves.
The input is initialized by the same paid integer binding, and raw
completeness has `H_0=3^T H_T`; this is an existence formula, not an
unpaid variable-length POWER operation. The fixed-duration language
remains x<=T and the number of witnesses grows with T.

If physical sine coefficients are explicitly requested from X,H, one
producer schedule is `u=X-H`, `v=u-H`, `A=3v`, `Bcoef=0-u`, costing
1M+3A and yielding `A s1+Bcoef s2`. This is only a coefficient conversion;
it does not evaluate sine as an ordinary integer operation or pay a
history certificate. Conversely no such conversion is silently added
to, or claimed free within, the table's chart-coordinate interfaces.

The proof is elementary and exact; no numerical tests, supplied or frozen
programs, saved arrays, predecessor helpers or builders were executed.
The complete guard and fixed-duration proofs were read inertly in
`markov_projective_counter_step.md` and `markov_positive_guard_savings.md`.
The all-degree full-action theorem was read inertly in
`markov_distinct_scale_fixed_point_obstruction.md`; its conclusion is
respected because T_Z is rank one, not a scaled identity on the full
space. Only this new proof and fresh metadata are authored under `/tmp`;
no repository or Git mutation occurs.
