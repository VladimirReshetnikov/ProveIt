# A fixed program radix gives a 409-operation counter tradeoff

The [literal compiler](korec_packed_program_radix409.py) trades a second
fixed positive program parameter for one operation in the
[410-operation positive-program U21 construction](korec_packed_positive_program410.md).
It gives **409 = 148M + 261A**, with **50 positive witnesses**, one final
comparison and uniform degree **at most 80458**. The certificate costs
408 operations. The 410 construction retains its one-program-parameter
interface and smaller degree bound 42589. The separate U9 and 75/87
results are unchanged.

For a fixed positive U21 program E choose a fixed C satisfying

    C is a power of two, C>=4, C>E.                    (1)

For example C=2^max(2,bit_length(E)) works. This C stays fixed as the
ordinary positive input x varies. These are effective program recipes,
not uncharged equations constraining arbitrary parameter values. The
[receipt](korec_packed_program_radix409.json) includes all five literal
forms, their source schedules and validation records.

## 1. The paid source change

Use a positive height slack eta and replace

    h=E+x+eta, D=h+h

by

    h=x+eta, D=C*h.                                   (2)

The program-height addition disappears. The radix addition becomes a
charged multiplication, so the complete count changes by +1M-2A: one
operation saved. The time radix remains B=2D^8, and the initial integer
is still ED+xD^2. All range, selector, counter, control and native rows
retain their literal meaning. The guard requires the complete canonical
positive410 U21 caller and checks the private deleted consumer.

There is an exact arbitrary-integer identity to the parent in which its
radix row has first been specialized to D=C*h with C a fixed numeral:

    eta_parent=eta-E, eta=eta_parent+E.                (3)

Every retained register, factor, residual and both complete outputs
agrees under (3). This is not an identity to the original D=2h source
for general C. The formal parent slack may be nonpositive; positive
soundness therefore uses the direct bounds below. No same-supplied-zero-set
or positive-inverse claim is made.

## 2. Pretyping and native restoration with h>=2

Before typing, (1)-(2) give

    h>=2, D>=4h>=8, E<C<D, x<h, B=2D^8.

The initial integer ED+xD^2 is below B, even when E>=h. This is the
reason for the fixed program bound C>E. The source does not need to add
E to h or constrain C as an existential witness.

Write R=(h-1)(1+D+...+D^7). Since h<=D/4, R<B-1. The unchanged signed
range unit still gives J>=1 and W<RJ<P, where P=(B-1)J+1. Each selector
word is at most J, and the zero-test lane (D-1)Zword is below P. Thus all
34 selector lanes and both counter lanes are nonnegative and below P.
With the same packed H,M,A and Q=B*P^64 as the parent,

    H-A>=0, M-A>0, Q-H-M+A>0.

The padded native truth fields are consequently strictly positive and
sum to q-1 before binary semantics is used. The complete native proof
restores the norm and index signs in its original order and gives the
full prescribed AND and dyadic B,P. Since B=2D^8, D is dyadic. The valid
fixed C is dyadic too, and D=C*h with integer h, so h is dyadic. This
last step is required for h-1 to be the counter digit mask.

The repunit identity gives P=B^T. There are 34 edges and B>34, so exactly
one edge is selected in every chronological digit. The range lane puts
all post-decrement digits in [0,h-1]; adding one selected action gives
digits at most h<D, without carry. Zero branches and the pure test retain
their exact local meanings. Default control labels are at most 5, while
D-2>=6, so the control codes stay injective with the required margin.

The negative counter-transport sign would require low digit D-2>h. The
negative control-transport sign would require D-2 or D-1, excluded by the
same label margin. Hence both transport factors are +1 and the product
restores the positive range sign. The exact initial integer below B and
the two chronological transports then recover precisely the initial
register vector (0,E,x,0,...,0), every transition and the final halt.
The counter bound on E is now a consequence of a valid typed first row,
not an assumption used to establish the native fields. This proves
soundness even at h=2.

The other four emitted forms retain stronger ordinary comparisons and
use the corresponding portions of this argument. Their program recipe
and ordinary input are identical.

## 3. Completeness at one fixed C

For any finite halted run of program E on input x, keep the same C from
(1). Choose a power of two h larger than x+1 and more than two above
every counter in the run. Then eta=h-x>0 and D=C*h is dyadic. Pack edge
selectors, post-decrement vectors and the terminal vector exactly as in
the parent. Every post-decrement digit is at most h-3. Thus

    RJ-W >= 2(1+D+...+D^7)J > 2,

so gamma=RJ-W-2 is a positive range slack for the unitized form. All
outer factors are +1 and the joined AND is genuine. The unchanged
complete native extension theorem supplies the private positive Pell
coordinates and normalized strong auxiliaries. This proves completeness
for every finite run with one C fixed per program.

The preceding positive410 packet proves that positive E alone suffices
for strong universality, including an effective replacement for index0.
Choosing C by (1) therefore yields a universal polynomial with two fixed
program coordinates and ordinary positive input. No uniform claim on
invalid E,C recipes is needed or asserted.

## 4. Counts, degree and validation

| Form | Certificate | Comparisons | Witnesses | Polynomial operations | Uniform degree bound |
|---|---:|---:|---:|---:|---:|
| Raw |393|19|60|449|13264|
| Native coupled |401|6|53|418|82708|
| Computed fields |400|4|50|411|80442|
| Range unit |402|3|50|410|80458|
| All chronological units |408|1|50|409|80458|

The default SOS alternative costs 410 operations and has degree bound
160916. The uniform degree includes C as a parameter: D now has degree2.
The nine factor bounds are13307,31038,7207,16626,6101,6101,16,31,31.
Their sum is80458. Specializing C to a numeral first recovers the matching
parent's degree dictionary; that is different from the uniform degree
reported above. Only the inherited guarded main-norm cancellation is used.

Run `python3 korec_packed_program_radix409.py`; `--write` regenerates the
receipt. Across all five forms, 160 complete retained-register maps and
320 complete fixed-C output identities pass, including 80 signed
assignments and 108 nonpositive formal parent slacks. Eighteen actual
U21 outer packs at two valid C values per history cover2970 rows and
check all paid outer equations, scale margins and the joined AND.
Eighty pretyping/digit contexts include sixteen cases at h=2. Ten invalid
callers or recipes are rejected. These checks do not materialize full
native Pell witnesses or substitute for the unbounded extension proof.

Author generation and a separate fresh replay pass. An independent complete
proof/source/dependency review and fresh replay pass without findings. Its
separate executor checks480 complete fixed-C output identities (240 signed),
240 retained-register maps,82 positive assignments with nonpositive formal
parent slack, and ten degree/opcode/liveness contexts covering all five
forms and both finalizers. Its own U21 interpreter and packing formulas
check eighteen halted histories at two fixed C values each:36 outer packs
with5940 rows, plus36 altered-terminal rejections. Another192 pretyping
corners include32 at h=2, nondyadic heights and both range signs. All three
local links and whitespace checks pass; these remain finite algebraic and
outer-history checks rather than materialized native Pell witnesses.
