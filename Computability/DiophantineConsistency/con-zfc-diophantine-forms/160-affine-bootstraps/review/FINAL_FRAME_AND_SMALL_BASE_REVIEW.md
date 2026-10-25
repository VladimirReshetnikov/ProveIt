# Independent addendum: the coordinate frame and smaller growth base

Prepared with AI assistance, 25 October 2026.

This updates the mathematical review for the final candidate
`research_direct/new_artifacts/equations/horizon8_linear_frame`.
Its front has

    t=8h, d=t+2, F=d^t, R=F, y=F(2v+1), q=4z+1.

The earlier sign-recovery, first-binomial-digit, generalized CRT and
completeness arguments continue to apply with the explicit changes below.
No mathematical gap was found. This is an ordinary proof review, not an
end-to-end proof-assistant certificate.

## 1. A coordinate frame suffices

For every integer u and integer a,

    a*u <= u^2+floor(a^2/4),
    -a*u <= u^2+floor(a^2/4).

Indeed the maximum of a*u-u^2 over integer u is floor(a^2/4), by completing
the square and taking the nearest integer to a/2. Therefore an affine atom
L=c+sum(a_i*u_i) satisfies

    |L| <= sum(u_i^2)+|c|+sum floor(a_i^2/4).

Let U be the union of the coordinates used by all actual affine power
atoms, with each coordinate included once. If C is strictly larger than
each displayed constant bound, then

    W=C+sum(u^2 : u in U)

satisfies |L|<W for every actual base, exponent and output. The main
Pell argument needs these absolute bounds; it does not need L^2<W.

For the literal final source I independently checked the JSON ledger:

- all37 original affine atoms are transformed by the four declared
  substitutions into exactly the37 listed new atoms;
- the substitutions are t0=8h-16, d=8h+2, R=F, and q=4z+1;
- every constant bound equals |c|+sum floor(a_i^2/4);
- the maximum bound is18, attained by d=8h+2;
- the exact union has33 coordinates, with no duplicates;
- C=19 is max(16,1+maximum bound);
- the literal raw frame row is precisely W-19-sum(u^2)=0.

Every coordinate in that union is a semantic front register, a genuine
power output, a stored derived-label value, the horizon parameter, or
the radix parameter. In particular coordinate522 is self_radix.BH, not
a private Pell coordinate. None is a Pell center or a principal ordinate.
Thus completeness chooses these values and W before choosing the large
center A. There is no hidden feedback from A into its own size bound.

## 2. Restore the coarse orientation estimate

The sharper square-atom estimate used for the earlier W>=7 variant is
not available with this new frame, and must not be cited for it.
Instead use the inherited coarse estimate. The semantic-anchor argument
gives classified indices j_i<=|h_*|<W, apart from the already handled
|C_anchor|=1 branch, where j_anchor=1 and all others0 and the same absolute
bound holds. Every requested k_i also satisfies |k_i|<W. Consequently

    (s_i-1)^2 <= 4,
    (r_i-k_i)^2 < 4W^2.

For at most15 pairs the nonnegative reduced error is

    E < 60(W^2+1) < 4W^3  (W>=16).

The final frame has W>=19, so this inequality applies. The odd frame norm
again gives |A|>W^W and |A-1|>4W^3. Divisibility forces E=0, and the
exceptional |C_anchor|=1 branch is contradicted by its positive anchor
orientation error. All requested signed Pell coordinates are therefore
canonical before any positivity claim about t.

For every nonunit base the modulus bound remains

    |2An-n^2-1| > 4W^W-W^2-1 > W^W+W.

The positive- and negative-index congruence errors are below that modulus,
using only absolute atom and index bounds. Thus the existing signed-power
lemma remains valid for this frame.

The latest semantic-anchor completeness proof, PROOF_315.md, requires
|h_*|<W and the independently arranged domination of all other requested
indices by h_*. It does not require h_*^2<W. The older historical round16
construction had a different anchor at index W and used W>=2*maxindex+1;
that historical construction has been superseded by semantic-anchor reuse.
It is the latest proof that is applicable here.

## 3. Smaller growth base

Now d=8h+2, so |d|>=2 at every integer h. The growth request forces t>=0.
At t=0 its output is F=1, and the endpoint parity contradiction

    1=(y+1)(u_t-u_0),  y=2v+1,

still excludes t=0. Therefore t is a positive multiple of8.
The smallest growth value is

    F=(t+2)^t >= 10^8 =100,000,000.

Thus F>=7, F>ell=2^22, F>(t+1)^t, F>1, and (t-1)F>t. Since d is even,
v_2(F)>=t still supplies every required factor2 in the beta construction.
The first signed-digit estimates use only F>=7 and x>=2+(t+1)F, so they
are unaffected by the reduced growth constant.

For the selector bound there are two cases. If t=8, then

    L_8=840,  L_8^2=705,600<100,000,000=F.

Every other permitted positive t is at least16, when the already proved
L_t<=4^(t-1) gives

    L_t^2<=16^(t-1)<(t+2)^t=F.

Thus R=F remains sufficient for both prime-power coverage directions.

## 4. The local evaluation budget

The old proof used F>2^32 only as a convenient way to make x sufficiently
large; its other use was to imply F>ell. We replace that sufficient bound
explicitly. The endpoint inequalities give

    x>=2+(t+1)y>=2+(t+1)F>=900,000,002>2^29.

For E=2^23, the needed inequality (2x)^E<2^x holds for every integer
x>=2^29. At x=2^29, the binary logarithm of the left side is
E*30=251,658,240<536,870,912=2^29. If it holds at x, then

    (1+1/x)^E < 1/(1-E/x) <=64/63<2

for x>=2^29; multiplying the left side by this ratio and the right side
by2 proves the next integer case. This establishes the claim by induction.
The bound 1/(1-E/x) follows by bounding each binomial coefficient by E^k
and summing the resulting geometric series.

All remaining range bounds and the strict inequality
2+t+x+y+F<2x follow exactly as before. In particular the derived-label
bound needs F>ell, which the new minimum100,000,000 satisfies.

## 5. Completeness and record of finite checks

A sufficiently large positive multiple of8 is chosen by truth padding.
The same positive odd multiplier supplies y as a large even multiple of
t!, and the same CRT parity choices give an even x, odd B and H, and
q=1 modulo4. All semantic atoms and power outputs are then known. Compute
the new coordinate frame W=19+sum(u^2), choose the large canonical frame
center and the semantic-anchor completion afterward, and fill the power
and remainder certificates. The changed frame introduces no new unknown
and no requirement that a former arbitrary zero be mapped pointwise.

The independently inspected raw rows were:

    row0: R-F=0;
    row363: t0-8h+16=0;
    row381: d-t0-18=0;
    row382: q-4z-1=0;
    row383: beta_multiplier-2v-1=0;
    row361: W-19-sum(33 distinct coordinate squares)=0.

The independent ledger check used only standard-library JSON parsing and
integer polynomial operations, importing neither producer nor checker.
It verified exact substitutions, all37 atom costs, the exact33-coordinate
union, C19, and the literal frame residual. Subsequent balancing may change
final sparse counts without changing these source facts. Whole final
polynomial coefficients remain the responsibility of the release collector.


# Frozen difference-pool update

# Independent final review: the difference of two orientation errors

Prepared with AI assistance, 25 October 2026.

## Reviewed literal candidate

The reviewed frozen source is
`research_direct/new_artifacts/equations/horizon8_difference_frame/raw_source.json`.
It composes the previously reviewed coordinate frame C=19 and front

    t=8h, d=t+2, F=d^t, R=F, y=F(2v+1), q=4z+1

with a change to the orientation pool. The detailed earlier arguments are
in FINAL_FRAME_AND_SMALL_BASE_REVIEW.md. This note supplies the additional
proof and literal check required by the final pool change.

## Exact change

Let the two raw ordinate errors be

    e_t = Y_t_proposed-t,
    e_Rt = Y_Rt_proposed-(R+t).

Replace e_Rt^2 in the orientation sum by (e_Rt-e_t)^2, retaining e_t^2,
every other ordinate-error square, and every abscissa-error square.
Since R=F, the new difference is

    Y_Rt_proposed-Y_t_proposed-F.

The change of error-vector coordinates is integral and invertible:
(e_t,e_Rt) -> (e_t,e_Rt-e_t), with inverse (u,v)->(u,u+v).
Thus all new errors vanish exactly when all old errors vanish.

I compared the two complete raw source JSON files. Their560 variable
records and384 row counts agree. The only row changed between
horizon8_linear_frame and horizon8_difference_frame is row374,
`cap.pooled_index_residue`. Its exact difference is

    (Y_Rt_proposed-Y_t_proposed-R)^2
       -(Y_Rt_proposed-R-t)^2,

with t=t0+16. The raw coordinate identities are t0 at0, R at4,
Y_t_proposed at258 and Y_Rt_proposed at297. No abscissa or anchor error
was deleted, and the e_t square remains. This literal delta is precisely
the intended change, including all constant and cross terms.

## Soundness before the powers are interpreted

At this stage the coordinate frame gives W>=19 and absolute value less
than W for every actual atom, including F and the requested indices.
The inherited cap and anchor argument bound every classified principal
index j_i by the absolute nominal anchor, hence j_i<W, except for the
separately excluded |C_anchor|=1 branch, where j_anchor=1 and the other
classified indices vanish and the same bound holds.

Modulo A-1 the small ordinate residue is r_i=plus-or-minus j_i. Every
unchanged ordinate error has absolute value below2W. The new difference
has small residue

    r_Rt-r_t-F,

whose absolute value is below3W because |r_Rt|,|r_t|,|F|<W. Every
abscissa error has absolute value at most2. For m<=15 principal pairs,
the nonnegative reduced orientation sum therefore satisfies

    0<=E < 9W^2+4(m-1)W^2+4m
          =(4m+5)W^2+4m
          <=65W^2+60 <4W^3 <|A-1|.

The penultimate inequality holds for W>=19; after division by W^2 its
left side is at most65+60/19^2<66, whereas4W>=76. The pooled row makes
A-1 divide E, so E=0. It follows first that the retained e_t small
residue vanishes, then that the old e_Rt small residue vanishes by
adding it back to the vanishing difference. Every original error
vanishes, and all intended signed Pell coordinates are recovered.

The exceptional |C_anchor|=1 branch still contradicts this conclusion.
Its cap gives nominal anchor0 and all other principal ordinates0, but
the classified anchor ordinate is plus-or-minus1. The anchor error was
not one of the two changed entries, so E>=1 in that branch. The same
strict upper bound excludes it.

This orientation proof precedes growth, radix, beta, binomial and CRT
sign recovery. It uses no property of a power that is still waiting to
be authenticated.

## Completeness and exact scope

On canonical semantic witnesses, every original coordinate error is
individually divisible by A-1, by the Pell-polynomial congruences. The
difference of the two errors is therefore divisible by A-1 as well.
The new sum of squares has an integer quotient by A-1, supplying the
same one free quotient variable in the pool. The frame and all other
canonical witnesses are unchanged. Thus every finite refutation still
constructs a zero of the changed source.

The pool replacement is a semantic-certificate change justified by this
bounded-residue proof. It should not be described as an unconditional
invertible operation on the old pooled residual itself: its quotient
can change, and the equivalence of the two pooled certificates depends
on the retained size and Pell constraints. The later explicit elementary
residual-row operations are separate, genuinely invertible algebraic
steps.

## Observed frozen metrics

The final balanced artifact records238 unrestricted integer coordinates,
174 quadratic residuals, degree4,5479 collected monomials and height7968.
The final dense artifact records237 coordinates,173 residuals,degree4,
14129 monomials and height7968. Both have residual coefficient height64.
These agree with the displayed METRICS.json files read during this review;
the release collector independently verifies their full coefficients.

No mathematical gap was found in this additional source change. This is
an independent ordinary mathematical and literal-source review inside
the AI-assisted workflow, not an outside human review or a new complete
proof-assistant certificate. The inherited logical calibration and the
full release verification boundary remain explicit.
