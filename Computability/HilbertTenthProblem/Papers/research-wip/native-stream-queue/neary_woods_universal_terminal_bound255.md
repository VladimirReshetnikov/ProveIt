# Deriving the terminal radix bounds gives255 operations

The [literal source](neary_woods_universal_terminal_bound255.py) removes one
more height addition from the [256-operation compiler](neary_woods_universal_height256.md).
The default complete polynomial costs **255=133M+122A**, with **43 positive
witnesses**, four positive program parameters, ordinary positive input and
degree **at most1384**. Its certificate has254 operations and one final
product comparison. The separate fifth duration-bound interface remains
available. The [receipt](neary_woods_universal_terminal_bound255.json)
records the emitted sources and exact checks.

The initial word remains in the paid height. The terminal values need
not be bounded there: after native typing, the update words and transport
equalities force both terminal digits below the history radix. This
argument preserves the accepted-input relation on valid shifted program
slices. It does not weaken the ordinary-input duration floor or assume
chronology to justify native typing. The established75/87 bounds are
separate.

## 1. Source change and unconditional initial bounds

Let W denote the emitted `load__tag_input`, so the true initial sentinel
on a valid shifted slice is V_0=W+1. Let U_f be the supplied upper
endpoint and V_f the unchanged computed lower endpoint. The parent and
new height definitions are

    D_parent=W+V_f+eta_parent,
    D_new=W+eta_new,                                (1)
    V_f=t*U_f+c,
    t=2^(beta+1), c=2^beta, beta>=2.

All supplied coordinates are positive. The unchanged paid loader has

    W=(program_A*rload+program_B*z)*Q
        +program_T*rload+program_E,

with every displayed variable positive before equations. In particular
W>=4. Consequently, writing b=c_h*D for the history radix and using
the fixed multiplier c_h>=8,

    D>=5, b>=8D,
    0<=W-1<W+1<=D<b,
    D<b-1.                                         (2)

The equality W+1=D is allowed when eta_new=1. The proof needs the
initial digit below b at this stage, not strictly below D. At a genuine
positive lower transport it will equal the first history digit, which
the range lanes separately force below D.

The literal edit deletes `hist__height_sum__1` and changes
`hist__height_sum__2` to `hist__height_slack+load__tag_input`. No terminal
row disappears: V_f remains explicitly computed and used by the lower
transport. Guards reconstruct the complete256 parent and verify the
terminal definitions, private sum/slack consumers and recursive active
exports. The same edit accepts the parent's canonical bases and exact
partition schedules. Every emitted gate must reach the complete output.

## 2. All typing and sign arguments precede terminal bounds

At a positive zero the integer factors of each paid group are units.
The [257 history-scale proof](neary_woods_universal_history_scale257.md)
uses only D>=4, b=c_h*D, positive supplied histories/product hats and
their paid global sum for its pretyping estimates. The new source still
has

    P=H_U+H_V+ZUhat0+ZVhat0+ZVhat1+global_bound>=6,
    P=(b-1)J+epsilon_G, epsilon_G in{-1,+1}.

The same consequences J>=1, b<=P+2, J<=P/6 and all weak-repunit
packed-lane margins therefore hold. Neither terminal endpoint enters
those packed words or the global sum. The new D satisfies every numerical
height assumption in those estimates.

The native rank/sign sequence is unchanged: safe norms and strong-square
restoration, local rank and linear recovery, exclusion of the negative
joint index, exclusion of the negative geometry index using the paid
loader, and the mask sign. The independent top-lane/Mersenne argument
then excludes epsilon_G=-1. None uses a terminal upper bound. It yields

    b dyadic, P=b^T, J=1+b+...+b^(T-1), T>=1.

Controller and selected-product lanes recover one actual tile at every
time and its exact selected history products. Range lanes give current
history digits

    0<=u_j,v_j<D, j=0,...,T-1.                     (3)

The upper unit is

    N_U=H_U+P*U_f-b*N_Uupdate in{-1,+1}.

Reduction modulo b gives N_U=u_0 modulo b. Since u_0<D<b-1, its sign
cannot be negative. Thus N_U=1 before any use of terminal chronology.
Both lower-unit signs remain possible for the next step.

## 3. A terminal digit follows from the transport equation

Here is the needed elementary lemma. For integers b>=2, T>=1 and P=b^T,
suppose

    0<=N<P, 0<=H<P, 0<=i<b,
    b*N+i=H+P*f, with f>0.                         (4)

Then

    P*f=b*N+i-H<=b(P-1)+(b-1)=bP-1,

so 0<f<b. Both sides of(4) are now canonical base-b expansions. If
N=sum n_j*b^j and H=sum h_j*b^j, comparison of their T+1 digits gives

    h_0=i, h_(j+1)=n_j (0<=j<T-1), f=n_(T-1).      (5)

No prior upper bound on f was used. Initial zero and T=1 are included.

To apply this to the source, let a_i*x+c_i be one coordinate's affine
update for a selected tile i. The fixed history multiplier satisfies
c_h>max_i(a_i+c_i). Each current digit in(3) therefore gives

    0<=a_i*x+c_i<=a_i(D-1)+c_i<b.                  (6)

The typed selected-product expressions are exactly those updates,
as proved in the [slope-class history](pcp_affine_slope_class_history.md),
Section3. Thus each computed update word has exactly T digits in[0,b):

    0<=N_Uupdate<P, 0<=N_Vupdate<P.                 (7)

This derivation uses only current digits and selected tiles. It does
not use either terminal endpoint. Also H_U,H_V<P by their range digits
or the strict global sum.

The two source equations are now

    b*N_Uupdate+1=H_U+P*U_f,
    b*N_Vupdate+(W+epsilon_L)=H_V+P*V_f,
    epsilon_L in{-1,+1}.                           (8)

Both terminal values are positive from their supplied/computed domains.
Both initial digits lie in[0,b) by(2). Applying(4)--(5) to each equation
proves U_f,V_f<b and every initial, interior and final transition of
the same selected tile sequence. A terminal value may exceed D-1:
the range lanes concern the current states, and the final update is
allowed to produce such a value. It is still below b, exactly as(6)
requires. No hidden terminal-height comparison is added.

If epsilon_L=-1, this common tile sequence starts its lower history at
W-1=V_0-2. The inherited valid input ends in the tag letter b and has
deletion number beta>=2. The [lower-unit sentinel obstruction](neary_woods_universal_lower_unit259.md)
then excludes the word equality: subtracting2 from the true initial
sentinel creates an internal zero run of length1, which no lower append
can erase, whereas every zero run of the upper word with its terminal
suffix has length beta. Equation(8) supplies precisely the complete
chronology needed for that word argument. Thus epsilon_L=1 and the
true initial sentinel is recovered.

The [four-tile word theorem](binary_tag_four_tile_history.md) now gives
the genuine tag computation. All loader, duration, physical-counter
and valid program recipes are unchanged, so the full ordinary-input
acceptance theorem follows. This is direct soundness, without invoking
a parent theorem at a possibly nonpositive height gap.

## 4. Positive completeness and the exact affine identity

At any positive parent256 zero on a valid program/input slice, keep
all other coordinates fixed and set

    eta_new=eta_parent+V_f>0.                       (9)

The height D is identical. Every subsequent source value, unit factor,
group and complete output remains identical. This proves positive
completeness for every supported strong/scale form and grouping.

For arbitrary integer assignments at fixed numerals, the reverse map

    eta_parent=eta_new-V_f                         (10)

gives an exact complete polynomial identity. It also preserves every
retained source register. The map is affine in the supplied coordinates
because V_f=t*U_f+c with fixed t,c. The numerical API accepts these two
fixed numeral values explicitly; it does not materialize the enormous
universal constants in the finite tests.

Map(10) can give zero or negative parent gaps, even when all new supplied
coordinates are positive. The checker forces eta_new=V_f and eta_new=1
as boundary cases. Such algebraic tuples are not asserted to be full
native zeros. The theorem claims accepted-input equivalence on valid
slices, not a positive inverse or same-tuple positive-zero identity.

## 5. Literal cost, degree and inherited partition family

The certificate loses exactly one addition, giving254=133M+121A and
one final product comparison; the polynomial costs255=133M+122A.
Witnesses, comparisons, parameters and fixed numerals are unchanged.
The height still has propagated degree3 through W, while P remains a
degree1 witness sum. Every complete degree dictionary equals its parent
dictionary, including the default factor bounds

    14,40,9,209,490,114,24,264,6,96,6,96,4,4,4,4,

whose sum is1384. These are conservative bounds, not asserted exact
degrees or arithmetic lower bounds.

Every schedule in the frozen256 inherited partition family contains
the same private sum. The source transformation changes neither factor
weights nor residual degree bounds, so that finite family's frontier
shifts down by one operation again:

| Operations | Degree bound | Witnesses |
|---:|---:|---:|
|255|1384|43|
|257|1242|43|
|258|1196|43|
|259|858|43|
|260|606|44|
|261|560|44|
|262|458|44|
|263|412|44|
|264|306|44|
|265|276|44|
|266|230|44|
|267|212|44|

With43 witnesses fixed, the low-degree endpoint is263/456; with45 fixed,
it is270/212. This uniform shift inherits the prior finite-family
optimization scope and does not search new circuits. Both ordinary-input
program-bound interfaces remain covered.

```sh
python3 neary_woods_universal_terminal_bound255.py
```

The checker audits the literal counts and closure, unchanged degree
dictionaries, complete affine source/output identities, positive parent
projections and nonpositive inverse-gap boundaries. A separate elementary
transport executor checks canonical digit splitting, including initial0,
duration1 and terminal values near the radix. These are algebraic/domain
fixtures, not full native Pell witnesses. Six further actual four-tile
paths encode the one-step halts b^beta to b as P_b D_b^(beta-1), for
beta=2,3,5,7,11,17. They use a dyadic height above every current state
but strictly below the final lower word, with positive height/global
slacks and negative affine parent-height gaps. The two full chronological
transport equations hold exactly. These are local tag/outer-history
fixtures, not instantiated universal U9 slices or complete Pell zeros.
The author writer and final fresh replay pass:82 literal ledgers,
1312 complete affine output/register identities,328 signed assignments,
656 positive parent projections,164 nonpositive inverse-gap boundaries,
2906 canonical transport cases (9032 individual digit equalities),
45 pretyping initial-bound cases and seven incompatible-caller rejections.
All seven local links resolve.

Root independently reviewed the complete proof/source and ran a fresh
default replay, with no findings. His separate literal executor and
manual affine map checked320 complete output identities,160 signed,
across ten contexts, including247 nonpositive inverse-height gaps.

Franklin independently reviewed the full proof/source and its typing,
history and sentinel dependencies and ran a fresh default replay, with
no findings. His own executor checked480 complete source/output affine
identities,240 signed, across40 contexts and both program interfaces
and finalizers;357 inverse parent gaps were nonpositive. Forty source
closure/equal-degree checks passed. He also independently constructed15
multistep b-only tag histories with174 selected steps, terminal values
above the height and negative parent gaps, and checked2000 elementary
transport splits. All seven local links passed. These independent fixtures
are exact source/domain or outer-history checks, not full native Pell zeros.
