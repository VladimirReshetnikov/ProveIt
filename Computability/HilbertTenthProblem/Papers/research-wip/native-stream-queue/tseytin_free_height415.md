# Recovering the Tseytin history bounds gives415 operations

The [source](tseytin_free_height415.py) removes three additions from the
[418-operation repunit-sharing compiler](tseytin_repunit_sharing418.md).
Its complete universal polynomial costs **415=194M+221A**, with395
certificate gates, seven comparisons,65 positive witnesses, one fixed
positive program parameter, ordinary positive input and degree at most5868.
The separate-power form costs417 and has degree at most5814. Both SOS
forms have the same respective operation counts, with degree bounds11460
and11352. The [receipt](tseytin_free_height415.json) emits all four sources.

This transfers the established U9
[bounded-zero-run input argument](neary_woods_universal_initial_bound254.md)
and [terminal-radix lemma](neary_woods_universal_terminal_bound255.md)
to the actual C2 query encoding. It is not a new general height lemma.
The C2-specific facts are its fixed multiplier65536 and the nonzero
base-eight digits in its fully paid ordinary-input query.

## 1. Supply the history height directly

Let I be `c2_initial`, U be the positive supplied `Ufinal`, and
V=4096U+3145 the unchanged computed terminal endpoint. The old source
uses the three additions

    D=U+I+V+rho_old.

The new source interprets the same positive coordinate `height_slack`
directly as D. It deletes `height_sum__0`, `height_sum__1` and
`height_sum__2`; the radix and range-cell consumers now read D itself.
All transports, endpoint definitions, comparisons, native factors and
paid program/input equations are unchanged.

For arbitrary integers the exact affine coordinate maps are

    D=rho_old+I+4097U+3145,
    rho_old=D−I−4097U−3145.                              (1)

Every retained source register and final polynomial agrees under(1).
The forward map is positive on positive old tuples. Its inverse need
not be positive, even at a perfectly reasonable outer history; terminal
states can exceed the height of the current-state digits. We prove
soundness directly below, and claim accepted-input equivalence on valid
program slices, not a positive inverse or identical supplied tuples.

## 2. Pretyping remains valid for every positive D

Write B for the history radix, J for the sum of decoded selectors and
P for the chronological scale. The unchanged source gives

    B=65536D, J=sum_(i=0)^23(Shat_i−1), P=(B−1)J+1.

Thus D>=1, B>=65536, J>=0 and P>=1 before any comparison. Every decoded
selector and selected-product coordinate is nonnegative, as is D−1.
All unhat packs and joined words are consequently nonnegative; the
native ports `16H+12,16M+10,16Z+8` and scale `16P^36` are positive.
The remaining supplied native truth fields and ratio slacks remain
positive. In particular no removed endpoint bound is needed for the
computed native fields or its strict bound X=q(r+beta)>r.

At a complete polynomial zero, all ordinary residuals vanish and the
two unit products multiply to1. The independent exponent52 signed
projection and the retained query comparison exclude its negative
branch exactly as in the [425 theorem](tseytin_universal425.md).
This uses no history-height inequality. Its own product and the native
word product therefore both equal1, and the initial value is exactly

    I=8 enc8(S phi(beta r_x beta))+6.                       (2)

The positive global comparison gives P>=11>1, hence J>0 and B<=P.
It bounds both supplied histories and all eight product hats below P.
Every selector and class selector is at most J; their full-cell masks
are at most `(B−1)J=P−1`. The range coefficient obeys

    0<=(D−1)J<(B−1)J=P−1.

Therefore all eight physical,24 selector and two range lanes fit, with
the original two top lanes allowing B=P at duration one. These estimates
remain true when D=1 and the range coefficient is zero.

The complete native coupled-unit theorem now gives the same prescribed
AND as before. Its proof needs positive ports/fields, q>=16, the retained
native bound and its complete strong equation; none uses a transport
endpoint. The top region of the resulting AND forces
`B AND(B−1)=0`. Consequently B and D are dyadic; the native scale also
makes P dyadic. The unchanged exact repunit relation gives

    P=B^t, J=1+B+...+B^(t−1), t>=1.

The selector sum and24<B recover one actual tile at every row. The
range and physical lanes recover current digits `0<=u_j,v_j<D` and
their exact selected slope-class products. This is the original
[slope-class proof](pcp_affine_slope_class_history.md), with its
height-dependent inequalities explicitly rechecked at D=1. No
chronological initial or terminal bound has been used yet.

## 3. The literal input supplies its own initial bound

Each nonzero base-eight digit1 through6 has at most two leading and
two trailing binary zeros. Across two adjacent digits, a zero run
therefore has length at most4. The leading sentinel1 adds no longer
run. The literal query in(2) uses digits1 through5, followed by delimiter
digit6; thus its ordinary binary expansion has no zero run longer than4.
This conclusion follows from the paid exponent and query relation,
independently of the high history's chronology.

The U9 lemma says: if D=2^d, B=2^(d+k), k>beta, and a positive integer
I has no zero run longer than beta, then `I modulo B < D` implies I<B.
Otherwise the nonzero high block and a residue below2^d leave all
k positions d through d+k−1 zero in I, a contradiction. It includes
a zero residue, whose zeros would be trailing.

Reducing the unchanged lower transport modulo B gives

    I modulo B=v_0<D.

Here k=16>4, so the lemma yields **I=v_0<D<B**. The unchanged upper
transport similarly gives u_0=1 modulo B; since u_0<D<B, it gives
u_0=1. Thus D=1 is impossible at a zero; this is recovered after typing,
not assumed in the pretyping argument.

The valid input promise is essential. An arbitrary integer I=B+1 has
residue1<D when D>1 and would evade the conclusion; it has a long zero
run and is not one of the encoded query values(2). No claim about
unrestricted program coefficients or arbitrary initial integers is made.

## 4. Typed updates bound the terminal digits

The actual tile maps have positive slopes and nonnegative offsets,
with `a_i+c_i<65536` and `b_i+d_i<65536`. Therefore at a typed current
digit z<D,

    0<=a_i z+c_i<(a_i+c_i)D<B,

and likewise for the other coordinate. Both selected update words N
and both history words H consequently lie in[0,P). The two transports
have the form

    B N+initial=H+P terminal,

with positive terminal and `0<=initial<B`, now proved in Section3.
Hence

    P terminal<=B(P−1)+(B−1)=BP−1,

so the terminal is below B. Comparing the canonical base-B expansions
recovers every initial, interior and terminal state. The terminal can
exceed D−1; only the current digits are constrained by the range lanes.
This is precisely the established terminal-radix lemma, applied to
both positive endpoints without an unpaid upper bound.

The resulting common tile sequence has the unchanged literal endpoint
relation. Its restored input is the actual query word(2), so the C2
word theorem, primary Tseytin reduction and effective program recipe
prove membership in the specified computably enumerable set. This
proves soundness without attempting to apply a parent theorem at a
nonpositive old height gap.

For completeness, every positive418 zero maps by the forward formula(1)
to a positive new zero, with all surviving registers unchanged. The
parent supplies such a zero for every accepted input. Equivalently one
may choose a sufficiently large dyadic D for any actual finite history
and rebuild its positive packed/native extension. The number and meaning
of the computational program/input parameters are unchanged.

## 5. Count, degrees, guards and evidence

Only the three height additions disappear. All retained register degrees
are unchanged because both the old height expression and the new supplied
height have degree1. Both literal main-norm cancellation graphs are
unchanged. The complete degree dictionaries therefore stay exactly those
of418; they remain upper bounds rather than exact universal degrees.

`rewrite` requires the complete canonical418 packet. It checks the three
sum rows, both terminal rows, the fixed radix and range consumers, and
the exact private consumer of the old slack. The output and degree APIs
require the entire canonical successor, including its program recipe,
interfaces and new coordinate meaning. Historical parent records retain
their old gap meaning and are used only after the affine lift(1).

The receipt audits complete arbitrary-integer affine source/output
identities, including signed assignments and nonpositive inverse gaps;
positive parent projections; the binary digit and bounded-zero-run lemma;
literal program/input queries; exhaustive small terminal transports;
and real tile updates that exceed the current-state height. Pretyping
fixtures include D=1 and verify the complete top/lower block separation
with the positive global sum. They are explicitly component assignments,
not full native Pell zeros. Every source gate is live in all four forms.

Run `python tseytin_free_height415.py` for a fresh receipt comparison;
`--write` regenerates it. Author generation and a fresh replay pass. An
independent full proof/source/dependency review and fresh replay pass with
no findings. Its separate checks include320 complete affine register and
manual-finalizer identities(160 signed assignments),125 nonpositive
inverse gaps,64 positive forward projections,6336 untyped lane contexts
(including1056 at D=1),186620 actual-language/radix cases,3600 terminal
transport splits, all four degree/opcode/domain/closure ledgers, and20
malformed successor rejections. Seven local links and whitespace pass.
These fixtures test the stated source and component lemmas; they do not
assert construction or exhaustive enumeration of full native Pell zeros.
