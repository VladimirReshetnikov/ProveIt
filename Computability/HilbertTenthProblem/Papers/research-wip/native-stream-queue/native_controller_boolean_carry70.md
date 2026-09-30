# A paid Boolean carry inside a paired ternary queue

The [constructive marker extension](input_bridge_boolean_carry_loader65.md)
now characterizes the bare input language exactly and supplies positive
witnesses for every ordinary input after one additional initialization addition.
It also proves an odd loop for the even-duration interface.

The [paired Boolean FIFO63](native_boolean_pair_fifo63.md) supports a new
one-operation filter. Its exact semantics include a two-state hidden carry;
the filter is not a coefficientwise linear rule. Together with one arbitrary
fixed affine carry controller at the necessary terminal value, it costs
**70=35M+35A**, with20 equations and29 strictly positive witnesses besides x.
Two more multiplications enforce even time and queue-width exponents, giving
**72=37M+35A**,22 equations and31 positive witnesses.

These are exact finite-machine components. The raw-input component already omits x=2, as proved in Section6.
No universal simulation, typed macro alphabet, or repaired ordinary-input
loader is supplied. The established complete
universal bound remains76. The source, proof and default receipt have passed independent full review
by the input-bridge agent, with no findings.

## 1. Source and inherited interface

The paired base supplies q=3^t, W=3^m, t>m>=1 and positive Boolean ternary
words F0,F1,F2,F3 of length t, with

    F2=I0+W*F0, F3=I1+W*F1,
    I0+I1=2x<W, q=W*L,
    F0+F1+F2+F3+alpha=q.                                (1)

I0,I1,alpha,L and all other supplied coordinates are strictly positive.
I0,I1 are Boolean ternary words of width m. The pair (F0,F1) records append
bits (a0,a1); (F2,F3) records read bits (d0,d1). The exact projection of(1)
is a t-step two-track FIFO from (I0,I1) to (0,0), with each of the four
read/append tracks containing a1. The width bound applies to the scalar
sum of the initial coordinates.

The only added operation is

    slack=F0+1; alpha=slack.                             (2)

Equality is free. Thus(1)–(2) give

    2F0+F1+F2+F3=q-1.                                  (3)

The base plus(2) costs**64=32M+32A**,19 equations and29 positive witnesses.
The original positive slack is reused; it is not replaced by an unrestricted
coordinate. Conversely(3) makes alpha=F0+1 positive and gives the base's
joint bound automatically.

## 2. Exact hidden-carry semantics

At position j define

    R_j=2a0_j+a1_j+d0_j+d1_j-2.

It lies in[-2,3]. Since the ternary digits of q-1 are all2, (3) says
`sum R_j*3^j=0`. It is equivalent to the existence of a hidden path

    e_0=e_t=0,
    3e_(j+1)=e_j+R_j, e_j in{0,1}.                      (4)

To recover it from(3), reduce modulo3 and divide successively. Starting
with e0=0, the divisible numerator lies in[-2,3] when e=0 and in[-1,4]
when e=1. Its quotient by3 therefore belongs to{0,1}. The final equality
gives et=0. Conversely telescoping(4) gives(3). Every hidden carry is
uniquely determined by the physical label prefix. No e_j is a supplied
arithmetic witness or a freely chosen phase bit.

Writing r=d0+d1, the complete table is:

| Hidden state | Read sum r | Append pair | Next hidden state |
|---|---|---|---|
|0|0|10|0|
|0|1|01|0|
|0|2|00|0|
|0|2|11|1|
|1|0|01|0|
|1|1|00|0|
|1|1|11|1|
|1|2|10|1|

A read sum1 permits both physical reads10 and01. They remain distinct
symbols in the paired FIFO. Thus the table contains11 physical edges,
including both branches shown at read sum2/state0 and read sum1/state1.
In particular the digit residual3 is intentional; interpreting(3) as
`2a0+a1+d0+d1=2` would incorrectly discard valid paths.

## 3. A six-operation external controller

Choose fixed integer coefficients and endpoints, with steps

    3c_(j+1)=c_j+h+u0*d0_j+u1*d1_j+v0*a0_j+v1*a1_j,
    c_0=cs, c_t=cf.                                    (5)

All integral carry states and all compatible labels are allowed. The
controller is not restricted to a chosen subgraph. Its exact global form is

    2cs+h(q-1)+2u0F2+2u1F3+2v0F0+2v1F1=2q*cf.         (6)

Suppose the fixed constants satisfy

    2cf=h+u0+u1.                                       (7)

Substituting(3) into(6) gives

    g0F0+g1F1+g2(F2-F3)=gap,                            (8)
    g0=2v0-2u0-2u1, g1=2v1-u0-u1,
    g2=u0-u1, gap=2cf-2cs.

These coefficients and gap are fixed numerals. The literal schedule is

    difference=F2-F3;
    term0=g0*F0; term1=g1*F1; term2=g2*difference;
    sum01=term0+term1; total=sum01+term2;
    total=gap.                                         (9)

It costs3M+3A. The difference is a computed register; it need not be
positive. Supplied witnesses retain the strictly positive domain.
Together with64, this gives70.

Conversely(8), (3) and(7) recover(6). Modulo3 reduction and successive
division of the global identity recover an integral c_j at every step,
ending at cf. This proves both directions for the whole external carry
graph. Combining with Section2 and the paired base gives the exact
projection: a finite path with both carries, hidden endpoints0, external
endpoints cs,cf, zero terminal queues, positive initial split summing to2x,
and all four tracks nonempty.

For the positive converse, any such path gives(3), hence the positive
joint slack F0+1. Its base parity requirement is automatic:

    F0+F1+F2+F3=2x+(W+1)(F0+F1)

is even. The established positive Boolean55/Pell converse then supplies
all remaining positive coordinates. No additional parity or origin
condition is suppressed.

If u0=u1, g2=0. Omitting difference and term2 and comparing
`g0F0+g1F1=gap` costs2M+1A. This exact specialization has
**67=34M+33A**,20 equations and29 positive witnesses. It does not certify
an arbitrary controller with unequal read coefficients.

## 4. Why the terminal condition is necessary for unbounded input

Initially allow arbitrary fixed constants in(5). Put

    G=|h|+|u0|+|u1|+|v0|+|v1|,
    C=max(|cs|,ceil(G/2)), B=2C+|h+u0+u1|.

Every external carry has absolute value at most C: the next magnitude
is at most(C+G)/3<=C.

The zero terminal queues force the final m append pairs to be00.
On such a step, (4) reads `3e_next=e+d0+d1-2`. The numerator is at most1,
so its nonnegative multiple of3 is0. Thus e_next=0 on every final-tail
step. After the first of these m steps, the hidden carry is0, so all
of the final m-1 read pairs are11. This conclusion does not require
t>2m, an initial zero prefix, or any particular incoming carry.

On those final m-1 steps, set b=2c-h-u0-u1. Equation(5) becomes
`b_next=b/3`, giving the exact bound

    3^(m-1)*|2cf-h-u0-u1|<=B.                           (10)

This includes m=1, when the forced-label segment is empty. If(7) fails,
then W=3^m<=3B, hence `2x<W<=3B`. The accepted ordinary-input set is
finite, with an effective bound depending only on the fixed controller.
For each width below the bound, reachability in the finite space of paired
queues, e in{0,1}, c in[-C,C], and four track-use flags decides acceptance.
This is a scoped finite-input result for the wrong endpoint. When(7)
holds, (10) supplies no width bound or decision procedure.

The first of the final m read pairs may have sum1 rather than2. The
positive m=1 example below does exactly this; strengthening the forced
suffix from m-1 to m would be false.

## 5. Two paid operations for pair alignment

Supply positive time_root,width_root and compute

    time_square=time_root*time_root; time_square=q,
    width_square=width_root*width_root; width_square=W.  (11)

Since q and W are already powers of3, (11) is exactly the restriction
that both t and m are even. Conversely the roots3^(t/2),3^(m/2) are
positive integers. These2M give72 from70. This aligns two-step blocks
in time and queue delay; it supplies no block code or phase-dependent
routing rule.

## 6. A scoped ordinary-input omission

If the ternary digits of2x all lie in{0,1}, every initial positive split
I0+I1=2x has no physical symbol11: adding two Boolean trits cannot carry,
so a shared1 would produce a trit2. Initially e=0. In that state, reading
00 forces append10, while either read10 or01 forces append01. These
steps keep e=0 and never append11. Thus the no11 alphabet is invariant,
and every step appends a nonzero physical symbol.

The most recently appended pair occupies the highest queue position.
Consequently the paired queue is nonempty after every positive-duration
step. It can never reach the required zero endpoint. This excludes all
such x at every width, even without an external controller or alignment.
For example x=2 has2x=4=(11)_3. More generally
`x=(3^n+1)/2` for every n>=1 is omitted. No choice of the fixed external
controller can restore these inputs by imposing additional conditions
on the same source.

This is a limitation of the precise raw2x initialization. Replacing it by
an input containing a trit2, such as6x+2, escapes this particular invariant
but requires a changed paid source and a proved loading simulation. It
is not supplied by the present packet.

## 7. Positive examples and validation

For x=1 choose W=3, q=27, I0=I1=1 and

    (F0,F1,F2,F3)=(4,1,13,4).

The successive physical reads/appends are11/11,11/10,10/00. The hidden
path is0,1,1,0. All four fields are positive Boolean ternary words,
alpha=5=F0+1, width_beta=1, and L=9. The external controller

    (u0,u1)=(-1,1), (v0,v1)=(2,1), h=0, cs=cf=0

has the same0,1,1,0 carry path and satisfies(7). The symmetric controller
`(u0,u1)=(1,1), (v0,v1)=(-1,13), h=-2, cs=cf=0` instead has path0,4,1,0.
Both therefore have full positive arithmetic extensions by the base theorem.

An aligned72 example is x=3, W=9, q=81, I0=I1=3 and
`(F0,F1,F2,F3)=(4,3,39,30)`. Here m=2,t=4, alpha=5, width_beta=3,L=9,
with positive roots time_root=9,width_root=3. Its fixed controller is
`(u0,u1)=(-2,1), (v0,v1)=(4,-3), h=1, cs=1, cf=0`; it satisfies(7).

The [checker](native_controller_boolean_carry70.py) symbolically audits
all equations against separately written polynomials and counts every
operation in the imported literal63 schedule and these additions.
The [receipt](native_controller_boolean_carry70.json) records:

- 69,904 Boolean-field tuples through length4, with628 admitted hidden paths
 and438 having all fields positive;
- 13,244 hidden-word/controller cases through length5, with3,516 admitted
 integral external paths;
- whole finite graph searches at widths1 through3 for the listed inputs and
 controllers:371 configurations,11 positive-track zero endpoints, including
 a wrong-endpoint witness satisfying(10);
- the positive70,67,72 examples and100 exact square/power checks;
- the closed no11 input alphabet through queue width5, including all
  possible physical initial words and their deterministic orbits.

The local-word tests include zero fields to test the algebraic equivalence
independently of positive-domain restrictions. The full examples enforce
all outer positivity conditions. Their large Pell coordinates are not
materialized; the parametric positive extension is the already proved
base theorem. Finite tests supplement the proofs and do not establish
universality.

Replay with the pinned dependency environment:

    /tmp/diophantine-research-venv/bin/python native_controller_boolean_carry70.py
