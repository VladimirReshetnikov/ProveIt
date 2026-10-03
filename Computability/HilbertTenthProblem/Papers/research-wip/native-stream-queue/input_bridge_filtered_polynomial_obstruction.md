# Polynomial input prefixes do not repair this filtered paired controller

The exact [64/69/72 filtered paired source](native_controller_paired_filter70.md)
remains a useful arithmetic component, but its particular one-carry family
cannot represent all computably enumerable sets. This remains true after
replacing the ordinary initialization `I0+I1=2x` by **any fixed integer
polynomial P(x) that is positive and even for every positive integer x**.
All other queue, filter, endpoint and positivity conditions are retained.
The assertion concerns the input substitution and the affine carry family.
Section6 also covers finite conjunctions of carries and fixed affine linear
equalities solely in the four stream words and q. Other additional
program-dependent relations and changed local rules are not covered.

More precisely, if the resulting language contains every positive even x,
then it contains every positive x. For nonconstant P, its centered carry
coefficients and initial carry must all vanish. For constant P the language
is automatically all or empty because the remaining equations do not use x.
The same implication holds with the paid fixed block alignment.

Thus this family cannot represent, for example, the union of the positive
even integers and a computably enumerable nonrecursive subset of the odd
integers. This is an expressiveness obstruction; it is **not** a decision
procedure for every language admitted by the family. It does not exclude
nonlinear or otherwise richer filters, another local rule, input supplied
through other equations, or an initialization with different semantics. The established
complete universal bound remains76.

## 1. Exact model and centered endpoint

Write the primary/secondary read bits as d0,d1 and append bits as a0,a1.
The paid filter is

    a0+a1+d0=1.                                           (1)

The two width-m queues begin at positive Boolean ternary words I0,I1 with

    I0+I1=P(x)<W=3^m,

and both queues end at zero after t steps. Each of the four read/append
words is strictly positive. A carry relation at the compatible endpoint,
after subtracting its terminal carry, is exactly

    3k_(i+1)=k_i+g0*a0_i+g1*a1_i+g2*d1_i,
    k_0=s, k_t=0.                                       (2)

All g0,g1,g2,s are fixed integers independent of x. In the uncentered
notation of the source, `g0=v0-u0`, `g1=v1-u0`, `g2=u1`,
`s=cs-cf`, and `2cf=h+u0`. The global equation is

    s+g0*F0+g1*F1+g2*F3=0.                              (3)

An incompatible endpoint has only finitely many accepted inputs when
P is nonconstant and positive: the unchanged final-tail proof bounds W
by a controller constant, and P(x)<W. Consequently it cannot contain
every positive even x. It suffices to analyze (2).

During the first queue sweep, the input trits are exactly d0+d1. There
is no ternary carry when adding two Boolean words. Thus their allowed
increments in (2) are

| Raw trit | Allowed increment |
|---:|---|
| 0 | g0 or g1 |
| 1 | 0, g0+g2, or g1+g2 |
| 2 | g2 |

No choice of the positive initial split changes this table.

## 2. Long runs of the raw trit2 force an exact carry

Put

    G=|g0|+|g1|+|g2|,
    C=max(|s|,ceil(G/2)).

Every carry has absolute value at most C, since an increment has absolute
value at most G. Choose L with

    3^L>2C+|g2|.                                        (4)

At a raw trit2 the pair read is11 and the append is00, so
`b_i=2k_i-g2` satisfies `b_(i+1)=b_i/3`. An integral path through L
consecutive2s therefore has `3^L` dividing its entry b. Its absolute
value is smaller than `3^L`, hence it is zero. The entry, exit and every
intermediate carry are exactly `k*=g2/2`. In particular g2 must be even
whenever such an input block is admitted. This uses an exact divisibility
bound and does not merely take a limit of contracting real paths.

Suppose initial input words can contain, above a fixed low prefix, any
prescribed finite continuation. Use the two continuations

    2^L,0,2^L,1    and    2^L,1,2^L,1.                  (5)

Here powers denote repeated trits, written low-first. The final1 ensures
the whole displayed word lies within the initial queue width. The carry
immediately before and after the middle trit is k*.

For the middle0, one of g0,g1 must equal `2k*=g2`. For the middle1,
either its increment0 equals g2, or one of g0+g2,g1+g2 equals g2.
Thus either g2=0, or

    {g0,g1}={0,g2}.                                    (6)

## 3. Both coefficient alternatives collapse

If g2 is nonzero, (6) and the terminal identity (3) give `g2 | s`.
All increments in (2) are then multiples of g2. Reaching k*=g2/2
after j steps, as required by either input in (5), would imply

    3^j*g2/2=s+g2*N

for an integer N. Dividing by g2 makes the odd integer `3^j` equal an
even integer, a contradiction. This argument allows any fixed prefix,
any initial carry s and either ordering of the two append coefficients.

It remains to handle g2=0. The middle0 test shows that at least one
append coefficient vanishes. The other cannot be dismissed just by
positivity in (3), because s can be nonzero after changing the input
prefix. The queue semantics supply the missing argument.

The reviewed terminal-tail proof, independent of the numerical input,
gives `t>2m`. Its final m steps read10 and append00. Therefore

    a0_i=1 for t-2m <= i < t-m.                         (7)

This follows by tracing those final reads back one queue delay.

If g0 is nonzero and g1=0, choose any admissible continuation starting
with `2^L` and with further specified initial trits afterward. At its
exit time j<m the carry is zero. Telescoping the remaining path to the
zero terminal carry gives

    g0*sum_(i=j)^(t-1) a0_i*3^(i-j)=0.

Every future a0 is therefore zero. But (7) includes the index
`i=t-m-1>=m>j`, a contradiction.

If g0=0 and g1 is nonzero, use the continuation

    2^L,0,2,0,1.                                       (8)

After the long2 block, at time j<m, the same suffix argument forces
every future a1 to be zero. Equation (1) now makes the primary queue
follow the invertible map that removes its first bit and appends its
complement. The orbit of the all-zero width-m word consists precisely
of

    0^r 1^(m-r) and 1^r 0^(m-r), 0<=r<=m.              (9)

Indeed successive iterations flip each original position once, producing
the first m+1 words, then flip them back, returning after2m steps. Since
the map is a permutation, (9) is also the exact set of words that can
ever reach zero. Each has at most one change in its low-first bit string.
The three unread initial trits0,2,0 in (8) force the primary queue's
first three bits to be0,1,0 at time j. This word is outside (9), so it
cannot reach zero. The final1 in (8) ensures those three positions are
still in the initial queue. This is the second contradiction.

Consequently g0=g1=g2=0. Equation (3) then forces s=0.

## 4. Every nonconstant integer polynomial supplies the needed prefixes

The precise statement is about finite residues: the 3-adic **closure**
of `P(positive even integers)` contains a nonempty 3-adic ball. The set
of ordinary integer values itself is not asserted to contain a ball.
Here is a constructive elementary proof, without assuming a digit
conversion or a paid arithmetic primitive.

Choose a positive even integer a with `P'(a)!=0`, possible because a
nonzero polynomial has only finitely many roots. Put

    e=v3(P'(a)), v=e+1, K=v+e.

Taylor expansion of an integer-coefficient polynomial gives an
integer-coefficient polynomial

    Q(z)=(P(a+3^v*z)-P(a))/3^K=u*z+3R(z),              (10)

where `u=P'(a)/3^e` is prime to3 and R has integer coefficients. In
fact every term of degree at least2 is divisible by3 after the displayed
division: its valuation is at least `2v-K=v-e=1`.
Therefore `Q'(z)=u modulo3` for every z. Each solution of
`Q(z)=b modulo3^n` has exactly one lift of the form `z+d*3^n`,
`d in {0,1,2}`, to each prescribed next digit. Starting modulo3 proves
that Q is a permutation modulo every `3^n`.

Let r be any residue modulo `3^(K+n)` whose low K trits agree with
P(a). Solve

    Q(z)=(r-P(a))/3^K modulo3^n.

Then x=a+3^v*z gives `P(x)=r modulo3^(K+n)`. Replacing z by
`z+3^n` if needed makes x even, and adding positive even multiples of
`3^n` makes x positive without changing the residue. Thus every finite
continuation above this fixed low prefix occurs at a positive even input.
In particular all the continuations (5) and (8) occur. The added final1
forces P(x) to be large enough that the prescribed positions precede m,
because W=3^m>P(x).

This argument is proved here for integer-coefficient polynomials. No
extension to arbitrary functions or integer-valued rational polynomials
is being silently imported.

## 5. Conclusion and the paid affine special case

If every positive even x is accepted, Section4 supplies the finite
prefixes required by Sections2–3, so the controller is zero. For any
positive even input value I=P(x), there is a positive Boolean ternary
split I0+I1=I: a trit2 can be split, and in its absence the even digit
sum contains at least two1s. Choose W=3^m>3I and apply the reviewed
three-sweep construction. It gives positive filtered fields, zero
terminal queues and the full positive Pell witnesses. The zero controller
accepts this path. Choosing m divisible by any prescribed fixed block
length also provides t=3m with the paid alignment. Hence every x is accepted.

For the affine input `P(x)=2(cx+d)`, c>=1 and d>=0 fixed, replace the
old product2x by the fixed scalar product(2c)x and add the fixed offset2d.
This costs one additional addition. The literal sources are
**70=35M+35A** and, with alignment, **73=37M+36A**. They retain20/22
equations and29/31 positive witnesses. These are distinct source variants
from the same-count bound-sharing references. The checker independently
expands their complete equations. The theorem above refutes this proposed
input repair for all c,d, without claiming that a particular finite test
settles a universal statement.

## 6. More affine carries and fixed linear word filters do not repair it

For nonconstant P, the same conclusion holds for any fixed finite conjunction
of independent affine carry controllers. If their intersection contains every even input,
each individual controller does. Each is therefore trivial by the preceding
proof, and their conjunction accepts every input. This observation concerns
the shared old filter (1); it does not transfer to a changed local relation.
For constant P, the conjunction is input-independent and therefore all or
empty; its carry coefficients need not be trivial.

More generally, suppose P is nonconstant and add a fixed affine equality
solely in the four complete stream words and q:

    r0*F0+r1*F1+r2*F2+r3*F3+rq*q=c.                   (11)

Using F2=H-F0-F1 and q=2H+1, this is

    a*F0+b*F1+g*F3+d*H=e,
    a=r0-r2, b=r1-r2, g=r3, d=r2+2rq, e=c-rq.        (12)

It is exactly the global equation of an integral carry with initial -e,
terminal0 and increments `a*a0+b*a1+g*d1+d`. The global equation implies
integrality of each successive carry by reduction modulo3, as usual.
Its carries are bounded by a constant independent of input and width.
On the final m steps, the sole physical label read10/append00 makes the
increment d constant. Thus

    W*|d| <= 2C+|d|

for a fixed carry bound C. If every positive even x is accepted, P(x)
and hence the required widths are unbounded. It follows that d=0.
The remaining equation is precisely (3), with s=-e, so the polynomial
input theorem forces a=b=g=e=0. Consequently every such row must satisfy

    r0=r1=r2=-2rq, r3=0, c=rq.                         (13)

It is just a fixed multiple of the already imposed filter
`q-1-2(F0+F1+F2)=0`. Applying the argument separately to each row proves
the same nonuniversality result for any finite set of these additional
equalities. With constant P, the language is already independent of x,
so the all-or-empty observation suffices without (13).

This corollary does not cover added variable witnesses, inequalities,
divisibility conditions, terms involving W or the initial split, or
nonlinear constraints. It does cover a second or third affine carry and
literal fixed linear equalities in the complete stream fields and q;
these do not supply the missing compiler even if their operation cost
is disregarded.

## 7. Evidence

The accompanying checker audits both full affine sources; verifies the
Taylor divisibility and exact lifting for several nonlinear polynomials,
including critical derivatives modulo3; constructs even ordinary inputs
realizing all prescribed prefix patterns; and exhausts the complement-
rotation zero orbit for widths1 through8. It also checks the bounded
long2 carry argument and its local coefficient alternatives. These are
focused symbolic and finite checks supporting the parametric proof.
No new universal certificate, Lean formalization or general decidability
theorem is claimed. Independent full proof, source and fresh default
review passed for Sections1–5, with no findings. The additional Section6
corollary, symbolic reduction and fresh default replay also passed a second
independent review after explicitly separating the constant-P case.
