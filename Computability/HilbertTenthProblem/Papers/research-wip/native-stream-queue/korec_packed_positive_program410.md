# A positive program coordinate gives a 410-operation universal counter polynomial

The [literal compiler](korec_packed_positive_program410.py) removes one
subtraction from the [411-operation U21 construction](korec_packed_counter_units.md).
Its complete polynomial costs **410 = 147M + 263A**, with **50 positive
witnesses**, one positive program parameter E, ordinary positive input x,
and degree **at most 42589**. The certificate costs 409 operations and has
one comparison. The [receipt](korec_packed_positive_program410.json) records
all five inherited forms and their complete emitted sources. The separate
254-operation U9 and established 75/87 bounds are unchanged.

The initial register vector is now directly

    (R0,R1,R2,R3,...,R7) = (0,E,x,0,...,0), E>0.

A restriction to positive program indices requires proof. The actual
machine's programs 0 and 2 both diverge on every input, as established
below by symbolic loops. Replacing program 0 by program 2 therefore gives
an effective positive program recipe without changing any represented
partial function or accepted-input set. The table, native arithmetic,
control labels and ordinary-input convention remain the same.

## 1. Two exact infinite-loop certificates

The parent contains the literal 21-instruction contraction from Korec's
[*Small universal register machines*](https://www.cs.cmu.edu/~cdm/resources/Korec1996-small-universal-RM.pdf).
Its Main Theorem (a3) supplies strong universality, with input program in
R1 and ordinary input in R2. The following additional argument concerns
that literal table, rather than a general claim about universal numberings.

For every X>=0, program 0 reaches the configuration

    q0: (1,0,X,0,0,0,1,0)

after 21 steps. From q0 with vector (A,0,X,0,0,0,1,0), the 12-instruction
state sequence is

    0,2,3,4,5,6,8,9,10,11,14,19,

and returns to q0 with vector (A+1,0,X,0,0,0,1,0). Each conditional test
in this sequence concerns a constant register value; X and A are never
tested. The halt state 21 is absent. This proves nontermination for every
input by induction on the number of loop traversals.

Program 2 reaches q0 with vector (1,2,X,0,0,0,1,0) after 59 steps. Its
corresponding 30-instruction loop is

    0,1,0,1,0,2,3,4,5,6,7,4,5,6,7,
    4,3,2,3,2,3,4,5,6,8,9,10,11,14,19.

It maps (A,2,X,0,0,0,1,0) to (A+1,2,X,0,0,0,1,0), again without a
symbolic conditional test or a visit to halt. The checker represents
registers as exact affine triples c+aA+bX, checks every prefix and loop
step, and requires all coefficients to remain nonnegative. The receipt
contains the full branch traces.

Let g be the parent's effective program compiler. Define g'(i)=g(i) when
g(i)>0, and g'(i)=2 when g(i)=0. Both excluded and replacement programs
compute the nowhere-defined function, so this change preserves every
partial function, not only its halting set. It proves that the same fixed
U21 remains strongly universal when its program coordinate is positive.
No input-dependent program choice, search for a second equivalent index,
or padding lemma is needed.

## 2. Literal graph change and its scope

The parent computes e=program_hat-1 and h=program_hat+x+eta_old. Delete the
private e subtraction, use the supplied positive E in its sole consumer,
and compute

    h=E+x+eta, D=2h, B=2D^8.                         (1)

There is no extra gate in (1): the existing two height additions are reused.
All selector, range, payload, control, packing and native rows remain.
The source guard accepts only the complete canonical U21 source in one
of the five inherited forms, checks the private consumers and preserves
closure in both finalizers. Historical parent packets retain their old
coordinate meanings.

On arbitrary integer assignments the exact affine coordinate map is

    program_hat_old=E+1, eta_old=eta-1.                (2)

The old computed e equals E. The first height partial sum is one larger
in the parent, but its final h and every other retained register agree.
Consequently all residuals, unit factors and both complete outputs agree.
The inverse is E=program_hat_old-1, eta=eta_old+1.

Map (2) can have a zero or negative parent height slack. It is not used
to infer positive soundness, and no identical supplied-positive-zero-set
claim is made. Conversely every positive parent zero with program_hat>=2
maps to a positive new zero. The program_hat=1 slice is empty by Section 1;
the effective program recipe replaces it by E=2 when necessary.

## 3. Soundness still holds at eta=1

The new unconditional bounds are h>=3 and E,x<=h-2. The initial integer
is ED+xD^2, with both coefficients below h and D, and it is strictly below
B=2D^8. These are the initial-height facts required by the parent proof.
Its old private program value e=program_hat-1 has simply been replaced
by E. In particular the weaker minimum eta=1 does not permit a carry or
an alternative input encoding.

For clarity, the order of the complete sign and typing argument is:

1. The range unit gives J>=1 and W<RJ<P before native typing. All selector,
   range and zero-test lanes are nonnegative and below P. The computed
   native truth fields are strictly positive and sum to q-1.
2. The unchanged native norm, normalized strong and local Pell-index
   argument restores the native signs. The raw population theorem types
   q; the fixed padded residue excludes the negative index sign. This
   restores the full prescribed AND, and hence dyadic D and P=B^T.
3. Since D=2h>=6 and is dyadic, D>=8. The default control labels are at most
   5, hence strictly below D-2. The range lane puts all counter digits in
   [0,h-1]. Adding one selected action gives digits at most h, without carry.
4. The negative counter-transport sign would require low digit D-2>h;
   the negative control-transport sign would require D-2 or D-1, outside
   the current-code digit set. Both signs are therefore positive. The
   product then restores the positive range sign.
5. The exact initial integer below B, one selected edge per row, all
   local zero/decrement/test conditions and exact chronological transports
   recover a genuine finite run starting at (0,E,x,0,...,0) and ending at
   the unique halt. The terminal vector is derived from transport as in
   the parent; no extra endpoint bound is assumed.

Every assertion above has the same native, packing and control source as
the parent. The only changed initial coefficient still satisfies the
required bounds. The raw, native-coupled, computed-field and range-unit
forms have the corresponding stronger comparisons and the same conclusion.

For completeness, take any actual finite halted run with E>0 and choose
a dyadic h larger than E+x+1 and more than two above every counter in the
run. The parent's packing and complete positive native extension apply.
The new height slack is one larger than the old one under (2), so it is
positive. All new outer factors and native factors are +1. This proves
both directions of the complete ordinary-input relation.

## 4. Ledgers and checks

| Form | Certificate | Comparisons | Witnesses | Polynomial operations | Degree bound |
|---|---:|---:|---:|---:|---:|
| Raw |394|19|60|450|7024|
| Native coupled |402|6|53|419|43780|
| Computed fields |401|4|50|412|42580|
| Range unit |403|3|50|411|42589|
| All chronological units |409|1|50|410|42589|

The default SOS alternative costs 411 operations and has degree at most
85178. Degree dictionaries agree with the matching parent forms, including
the inherited guarded main-norm cancellation. These are propagated upper
bounds, not exact-degree or optimality claims.

Run `python3 korec_packed_positive_program410.py`; `--write` regenerates
the receipt. All five forms pass 160 complete retained-register and affine
map checks, including 80 signed assignments and 105 nonpositive formal
parent slacks. Both finalizers give 320 complete output identities. The
symbolic prefixes and loops prove nontermination for unbounded A and X;
they are not extrapolations from finite simulation. Twenty actual halted
U21 histories, with 5668 chronological rows, pass positive outer packing,
all paid outer equations and the complete joined AND. Eight malformed
callers are rejected. Outer-history checks do not materialize full private
native Pell witnesses.

Author receipt generation and a separate fresh replay pass. An independent
full proof/source/dependency review and fresh replay pass without findings.
Its separate affine table interpreter proves both infinite loops; additional
literal runs check 262144 nonhalting steps. An independent source executor
checks 160 manual affine register maps and 320 complete outputs (160 signed
outputs), including 116 nonpositive formal parent slacks. Ten independent
opcode and closure ledgers cover both finalizers. The review specifically
checks the direct height argument at eta=1 rather than invoking a positive
parent theorem at a zero old slack.
