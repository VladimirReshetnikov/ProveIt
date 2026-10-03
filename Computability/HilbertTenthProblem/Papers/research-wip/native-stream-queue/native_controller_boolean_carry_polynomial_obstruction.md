# Polynomial input does not make the hidden-carry controller family universal

Fix an integer polynomial P that is positive and even on every positive
integer. Replace the initial scalar value2x of the
[hidden Boolean-carry paired queue](native_controller_boolean_carry70.md)
by P(x), retaining its positive split, empty endpoint, four positive stream
words, and one arbitrary fixed affine external controller. No other
occurrence of x or extra relation is included. This note concerns that
exact family; evaluating a general P is not a free arithmetic operation.

**If this family accepts every positive even x, its accepted language is
decidable.** For nonconstant P, the external controller must be redundant,
and the exact resulting predicate is

    the ternary expansion of P(x) contains a digit2.    (1)

For constant P, the accepted x-language is automatically all or empty.
The same conclusion holds with the paid restriction that width and duration
are both even. Thus the family cannot represent the union of all positive
even integers with a nonrecursive computably enumerable subset of the odds.
This does not assert decidability for every controller that rejects some
even inputs, or for additional filters or different endpoint semantics.

For the paid marker P(x)=6x+2, (1) is always true. Hence a controller in
the exact71/73 marker family accepting all even inputs accepts all inputs.
The established complete universal bound remains76.

## 1. Exact model, endpoints and arbitrary finite input prefixes

Use read bits d0,d1, append bits a0,a1, hidden bit e and external carry c:

    3e_next=e+2a0+a1+d0+d1-2, e_initial=e_terminal=0,
    3c_next=c+h+u0*d0+u1*d1+v0*a0+v1*a1,
    c_initial=cs, c_terminal=cf.                       (2)

All coefficients and endpoints are fixed integers. The two width-m queues
start at positive Boolean ternary words with sum P(x)<W=3^m and end at
zero. Every read and append rail is used. During the first queue sweep,
the scalar input trit is exactly d0+d1, without a ternary addition carry.

Put U=u0+u1. The reviewed terminal-tail theorem bounds
`3^(m-1)*|2cf-h-U|` by a fixed constant. A nonconstant P positive on all
positive integers tends to infinity. Thus acceptance of all even x forces

    2cf=h+U.                                          (3)

Every external carry has a uniform bound

    |c|<=C=max(|cs|,ceil((|h|+|u0|+|u1|+|v0|+|v1|)/2)). (4)

We use the proved finite-prefix lemma from the
[integer-polynomial input audit](input_bridge_filtered_polynomial_obstruction.md):
for nonconstant P in Z[x], the 3-adic closure of P(positive even integers)
contains a ball. Equivalently, above a fixed low ternary prefix, every
prescribed finite continuation occurs at some positive even ordinary input.
The proof chooses even a with P'(a) nonzero, puts e3=v3(P'(a)), v=e3+1,
and expands

    (P(a+3^v*z)-P(a))/3^(v+e3)=u*z+3R(z), 3 not dividing u.

The right side is a permutation modulo every power of3 by successive
digit lifting. Changing z by a suitable multiple of that power enforces
even x and positivity. This statement uses integer-coefficient polynomials;
no rational integer-valued extension is assumed.

We append a final raw trit1 to every prescribed pattern below. It ensures
all its positions lie inside the initial width, because W>P(x). Thus the
argument never mistakes a feedback symbol for an unread input trit.

## 2. Long zeros synchronize both carries

At a raw trit0, hidden0 forces append10 and hidden1 forces append01;
both transitions end at hidden0. On all subsequent consecutive zeros,
the append is10. Let

    c*=(h+v0)/2,
    choose L>=1 with3^L>2C+|h+v0|,
    Z=0^(L+1).                                       (5)

On a raw0/append10 step, `b=2c-h-v0` satisfies `b_next=b/3`.
An integral path through L such steps has3^L dividing its entry b,
whose absolute value is smaller than3^L. Therefore the entry, exit and
all intermediate carries equal c*. Consequently an accepted block Z
ends exactly at hidden0 and carry c*. This also proves c* is integral.

The following deductions use input continuations `Z,2^n,Z,1`,
`Z,1,Z,1`, and `Z,0,1`, available by Section1. Here powers denote
repeated trits in low-first order, not exponentiation inside the source.

## 3. Arbitrarily long two-runs force v0=u0+u1

Start the block2^n just after Z. Its hidden path either stays0 throughout,
appending00, or first switches to1 at a position k with0<=k<n, appending11
there and10 at every remaining two. Once hidden1 is reached, it cannot
leave on another raw2.

The first following raw0 resets hidden to0. The remaining L zeros force
its external output carry to c*. Therefore, writing z=c-c*, the carry
at the end of2^n must be0 when hidden ends0 and v0-v1 when hidden ends1.
Set

    D=U-v0, A=2v1-v0.                                (6)

If there is no hidden switch, telescoping the external recurrence gives
`D*(3^n-1)=0`, so D=0. If the switch is at k, the exact equation is

    D=A*3^k+(D+A)*3^n.                               (7)

For clarity, the centered increments through the two-run are D before
the switch, U+v1 at the switch, and U after it. Their weighted sum,
with terminal centered carry v0-v1, gives(7).

Suppose D is nonzero. Equation(7) implies3^k divides D, so k<=v3(D).
If D+A is nonzero, choose n larger than this bound and with
`3^n*|D+A|>|D|+|A|*3^v3(D)`. Then(7) is impossible. If D+A=0,
equation(7) instead becomes `1=-3^k`, also impossible. Acceptance for
every even input supplies the displayed patterns for arbitrarily large n.
Thus

    v0=U, c*=cf.                                     (8)

This exact integer argument permits both signs of every coefficient.

## 4. The two asymmetric coefficient branches both fail

In `Z,1,Z,1`, the middle raw1 has read10 or01, while its hidden state
remains0 and it appends01. Its entry and exit external carry are cf.
Equation(2) gives u_i+v1=U for the read rail i that equals1. Hence

    u1=v1 or u0=v1.                                  (9)

First suppose u0=a and u1=v1=b. Put k=c-cf and ell=k-b*e. Using(8),
the exact difference between the external and hidden recurrences is

    3ell_next=ell+(a-b)(d0+a0-1).                    (10)

Take the suffix after Z in the third pattern `Z,0,1`. At its beginning
ell=0; at the terminal endpoint ell=0. If a!=b, telescoping implies
that a finite balanced-ternary sum with digits d0+a0-1 in{-1,0,1}
equals zero. Each digit must be zero: reduce modulo3 and divide repeatedly.
Thus d0+a0=1 on every remaining step.

Substitution into the hidden recurrence gives
`3e_next=e+a1+d1-d0`. Starting at e=0, its numerator lies in[-1,2],
so integrality forces e_next=0 and a1+d1=d0. The entire remaining
physical table is therefore

    00->10, 10->01, 11->00; read01 has no transition.  (11)

The prescribed next raw0 creates symbol10. On a run ending with an empty
queue, every nonzero appended symbol must later be read. Reading this10
creates01, which must also later be read, but has no transition. This
contradiction rules out a!=b in the first branch.

Now suppose u1=a and u0=v1=b. The exact counterpart is

    3ell_next=ell+(a-b)(d1+a0-1).                    (12)

The same balanced-ternary suffix argument forces d1+a0=1. The hidden
recurrence becomes `3e_next=e+a1+d0-d1`; starting at0 it stays0 and
forces a1+d0=d1. This time the table is

    00->10, 01->01, 11->00; read10 has no transition.  (13)

The prescribed raw0 immediately appends the unprocessable symbol10.
The zero endpoint is again impossible. This second branch is treated
separately; it is not a symmetry assumption about the two queue rails.

Both cases yield

    u0=u1=v1=b, v0=2b.                               (14)

## 5. Collapse, exact remaining language and source scope

With(3) and(14), h=2cf-2b and(10) becomes

    3ell_next=ell, ell=c-cf-b*e.

Its terminal value is0, so its initial value is0 as well. Since e_initial=0,
this forces cs=cf. Conversely these constants make

    c_j=cf+b*e_j                                     (15)

an integral external path for every hidden path. The controller is exactly
redundant, not merely harmless on the test inputs. Its reduced source
coefficients g0,g1,g2 and gap are all zero.

The reviewed [positive erasing construction](input_bridge_boolean_carry_loader65.md)
proves the exact bare predicate(1) for every positive even initial value.
It lifts to both physical rails, uses all four streams, and supplies the
positive Pell extension. Its odd intermediate loop also supplies even
duration at any sufficiently large even width. Hence both the unaligned
and square-aligned collapsed languages are exactly(1), which is decidable
by evaluating P(x) and reading its finite base-three expansion.

If P is constant, no remaining equation uses x, so the accepted set is
all positive inputs or empty. If P is nonconstant but an incompatible
endpoint is used, the finite width bound already prevents accepting all
even x. These cases complete the theorem stated at the start.

For any nonrecursive computably enumerable set K of nonnegative integers,
the set `{2n:n>=1} union {2n+1:n in K}` is computably enumerable and
nonrecursive. If represented by this family, acceptance of all even inputs
would make it decidable, a contradiction. Additional equations, a different
filter, nonzero terminal queues or a different input interface are outside
the statement. No claim is made about controllers that omit some even x.

No new arithmetic schedule is proposed. The checker audits the existing
raw70 and marker71/73 schedules, then verifies that their entire external
equation vanishes under(14) and cs=cf. General polynomial evaluation has
whatever separate cost its chosen straight-line computation requires.

## 6. Evidence

The checker independently derives the long-two endpoint formula and both
asymmetric recurrences, tests explicit rejecting lengths for bounded signed
D,A, and replays the two forced suffix tables on bounded physical queues.
It constructs actual even polynomial inputs for every required finite
prefix pattern and checks positive erased tuples with the proportional
external carry, including even width/time. These finite tests supplement
the parametric proof; they are not an enumeration of accepted languages.
Independent full proof/source/default review passed with no findings.
Fresh replay686158 matched the saved receipt, including both asymmetric
suffix arguments, signed two-run bounds and the positive aligned converse.
