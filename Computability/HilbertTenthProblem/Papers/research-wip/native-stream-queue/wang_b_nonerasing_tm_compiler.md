# An exact non-erasing TM-to-Wang compiler with paid binary input

The [finite record-compiler successor](wang_b_erasing_bridge_compiler.md)
now supplies explicit erasing-to-non-erasing microcode and its framed
ordinary-input loader. The [materialization audit](native_binary_dependency_projection.md)
realizes the complete illustrative composition at312942 operations;
neither successor instantiates a fixed universal table/input slice.

This packet turns every fixed finite non-erasing binary Turing machine
into a literal Wang B instruction list and then a single Diophantine
polynomial for halting on its ordinary positive binary input x. The
instruction expansion, head position, finite blank exterior and input
pair map are explicit. All recoding and arithmetic finalizers are paid.

The [source](wang_b_nonerasing_tm_compiler.py) implements the expansion in
[Neary–Woods–Murphy–Glaschick2014](https://mural.maynoothuniversity.ie/id/eprint/12409/1/Woods_Wang_2014.pdf),
Theorem7, Section3.1, printed pp638–640, equations(1)–(5). It uses the
[computed-action Wang compiler](wang_b_computed_actions.md) and
[complete radix-four unit recoder](native_binary_input_dilation_unit179.md).
The [receipt](wang_b_nonerasing_tm_compiler.json) records literal source
ledgers and differential physical-machine checks.

The example machine has one nonhalting state: on0 write1 and move right
to halt; on1 retain1 and move left to halt. Its14-instruction Wang list
costs454 polynomial operations on a supplied paired-word integer. The
complete ordinary-input polynomial costs **642=285M+357A**, with566
certificate operations,25 comparisons,83 positive witnesses, one positive
parameter x and degree **at most16124**. This example is not universal.

No fixed universal non-erasing table or ordinary-TM-to-non-erasing
transition compiler is instantiated. The2014 paper's Lemma5 copying
overview remains a separate implementation obligation. In particular,
the repository's erasing U15 table cannot be fed directly to this compiler.
The established75/87 and explicit285 universal results are unchanged.

## 1. Exact finite machine and instruction conventions

Let h>=0. TM states are0,...,h, with start0 and sole halt h. The supplied
table has h rows, each containing two transitions (write,direction,target),
indexed by read0 and read1. Every nonhalting state has both transitions;
write is0 or1, direction is L or R, target belongs to0..h, and a read1
transition must write1. The halt has no outgoing row. Arbitrary finite
state names may first be bijectively renamed with a nonhalting initial
state first and halt last. If the initial state is already halting,
discard the other unreachable states and use h=0. The API rejects
partial rows, erasing writes, stationary moves and out-of-range targets;
it does not interpret malformed or absent rows as acceptance.

The tape is bi-infinite with blank0, a finite set of1 cells and one head.
A TM transition writes its symbol, moves, and then enters its target
state. Halting means entry into h, after that final move. Ordinary input x
places bit_j(x) at cell j>=0, leaves every other cell0, and starts the
head at0. We do not silently reverse the binary input word.

Use the repository's one-based Wang labels. For each i<h emit

    R, J(13i+9), zero_tail, one_tail.                (1)

The six-instruction zero tail, with transition target j, is

| Write / direction | Tail |
|---|---|
|0 / R|R,M,M,M,M,J(13j+1)|
|0 / L|L,L,L,M,M,J(13j+1)|
|1 / R|M,R,M,M,M,J(13j+1)|
|1 / L|M,L,L,L,M,J(13j+1)|

The five-instruction one tail is R,M,M,M,J(13j+1) for a right move and
L,L,L,M,J(13j+1) for a left move. Append one final M at label13h+1.
These are exactly the primary expansion with every instruction address
increased by1. Thus the list has13h+1 instructions,3h jumps and16h+1
transition edges in the arithmetic controller. Every jump target belongs
to the list, including the final M. No jump outside the list is needed.
For h=0 the list is just M.

## 2. Physical invariant and both directions of halting equivalence

Fix integer coordinates on the TM tape. Encode a finite set I of
initialized cells, containing the head and every1 cell, as follows:

* cell i in I has Wang cells(2i,2i+1) equal to(1,tape_i);
* every pair outside I is00;
* TM state i and head a correspond to Wang label13i+1 and head2a.

In physical left-to-right order the initialized pairs are0->10 and
1->11. The encoding has finite support; it requires no periodic or
infinitely marked background. We may initialize additional blank cells
as10 without changing the represented TM configuration.

For i<h the first R moves from2a to2a+1, so the following jump reads the
actual represented bit. Read0 takes the zero tail; read1 takes the one
tail. If the transition writes1 from0, the initial M in its tail marks
the odd cell2a+1. If it preserves0, that cell is not marked. A read1 tail
never erases anything.

A right tail moves once from2a+1 to2a+2; a left tail moves three times
to2a-2. In either case a subsequent M marks the new even head cell.
The odd cell of that destination is unchanged. Thus an uninitialized00
destination becomes the correct blank pair10; a previously initialized
10 or11 pair remains unchanged. Repeated padding M instructions have no
further effect. The final jump reads the newly marked even cell, hence
always transfers to13j+1. The resulting tape is exactly the encoding of
the updated TM tape with I enlarged by the new head cell.

This proves the invariant for each of the six allowed transition types,
including both exterior extensions and a destination already containing1.
A read0 transition executes exactly8 Wang instructions, a read1 transition
exactly7. There is no early fall-through halt inside a block: the tail's
last jump is taken. If the target is h, the final M is executed on an
already marked even cell and the Wang list then falls through to halt.
No other instruction falls past the end.

Consequently a t-step halting TM run corresponds to a Wang run of between
7t+1 and8t+1 steps. Conversely every Wang run from a valid encoded initial
configuration follows these deterministic blocks, so Wang halting implies
TM halting. If the TM runs forever, the block invariant extends forever.
When h=0, the TM is already halted and the single final M gives a one-step
Wang halt without changing the valid encoded tape. This handles the
arithmetic compiler's nonempty-history convention explicitly.

## 3. A complete positive-input pair loader

The complete radix-four recoder has positive parameter x and positive
output z. On every positive zero it supplies an integer n>=2 with

    0<x<2^n, Q=4^n, z=sum_j bit_j(x)*4^j.           (2)

Conversely each x>0 and every sufficiently large n have a positive
extension. Its unit179 source already computes modulus=Q-1. Make z an
existential positive coordinate in the present composition. Add one
positive witness r and these three literal gates:

    pair_repunit_times3=3*r,
    pair_twice_z=z+z,
    y=r+pair_twice_z,                               (3)

with the additional comparison3r=modulus. The fixed3 multiplication is
charged. On every zero,

    r=(4^n-1)/3=sum_(j=0)^(n-1)4^j,
    y=sum_(j=0)^(n-1)(1+2*bit_j(x))*4^j.            (4)

Because cell positions correspond to increasing binary exponents, the
base-four digit1 has physical bits10 and digit3 has physical bits11.
Equation(4) therefore gives exactly the finite pair tape from Section2,
initialized on cells0,...,n-1, with the head at the first bit of cell0.
The padding positions j>=bit_length(x) are blank TM cells encoded10.
Their presence changes neither the represented infinite TM tape nor its
future behavior. This is stronger than assuming an input-normalization
routine: no such routine is needed for this particular blank padding.

At all supplied positive tuples, before any equations, y=r+2z is positive.
It is therefore a legitimate replacement for the Wang literal-input
parameter. Its physical head and finite-window spatial shift are supplied
by the already-paid literal Wang compiler. The shift translates the entire
pair tape and head together and may have either parity; pair alignment is
relative to that shifted head. A finite bi-infinite run always admits such
a nonnegative-window translation. Head typing is not assumed from(3).

Add the repunit comparison inside the recoder's own retained sum of
squares. Its new product polynomial R costs185 operations and has the
same positive-zero semantics as the full recoder plus that comparison.
This follows directly from its existing integer-unit argument: if
U(1+sum residual^2)=1, both integer factors force the retained residuals
to vanish and U=1. Adding another squared residual does not weaken that
argument or change any kernel sign assumption.

Let W be the complete computed-action Wang polynomial after substituting
its positive literal input by y. All native auxiliary coordinates of R
and W are disjoint. The final polynomial is explicitly

    F=R^2+W^2.                                     (5)

Both R and W are integer polynomials, even when one uses an unsquared
norm-product finalizer. Thus F=0 if and only if both component outputs
are0. No product of unrestricted checksums or unproved sign condition
is used to merge the two complete kernels.

Soundness: a positive zero first restores(2)--(4), then a genuine halted
Wang run from that pair tape, and finally a halted ordinary-input TM run
by Section2. Completeness: for a finite halted TM run choose any adequate
n>=max(2,bit_length(x)), use the recoder's positive extension, set the
positive integer r from(4), and invoke the literal Wang compiler's positive
extension for the simulated finite run. Its five normalized auxiliaries,
when that form is selected, are reconstructed by the inherited theorem.
The disjoint extensions give a positive zero of(5). No arbitrary old/new
native-witness bijection is claimed for the parent's normalization.

## 4. Literal costs, degree bounds and API

Write C,e,w and c for the selected computed-action Wang child's certificate,
comparison, positive-witness and polynomial counts. The paired-word child
has one parameter y. The ordinary-input construction has

    certificate=C+138, comparisons=e+16,
    witnesses=w+38, parameters=1,
    polynomial=c+188=(M_child+90)M+(A_child+98)A.      (6)

The recoder contributes135 certificate gates,15 comparisons and36 native/
outer witnesses before making z existential. Gates(3) add1M+2A and one
comparison; z and r add two positive witnesses. Its completed polynomial
is185=88M+97A. Equation(5) adds two squares and one addition, so its total
increment is188=90M+98A. The extra two operations relative to a single
generic comparison-count finalizer are real: this source closes two
complete component polynomials separately and then squares both.

The example's actual source ledgers are:

| Native form | Paired-word Wang polynomial | Complete ordinary-input polynomial | Certificate | Comparisons / witnesses | Degree bound |
|---|---:|---:|---:|---:|---:|
|Raw|482|670=291M+379A|561|36 /90|2312|
|Positive scale|479|667=290M+377A|561|35 /89|2312|
|Six computed fields|461|649=284M+365A|561|29 /83|5312|
|Normalized units|454|642=285M+357A|566|25 /83|16124|

The recoder product degree remains at most186: its only new retained
comparison has degree2, below its existing outer bound, and(3) has affine
y. Substituting y into the Wang input preserves its existing degree
envelope because y is affine in the independent positive coordinates r,z.
If d_W is the child's proved degree bound, (5) has degree at most
2max(186,d_W). These are conservative bounds, not minimality or exact-degree
claims. The source replays the child's actual degree audits for every ledger.

`compile_tm(table)` returns the exact one-based list. `build(table,
ordinary_input=True,form='units')` emits the complete ordinary-input
packet; its only parameter is x. The form can instead be raw, scaled or
projected. Setting ordinary_input=False returns the literal Wang child
with its positive input parameter; interpreting an arbitrary value of that
parameter as a TM tape still requires the pair condition from Section2.
`polynomial_source` returns the actual acyclic schedule and output name;
`ledger` counts its literal gates, including fixed-numeral multiplications.

## 5. Reproducible evidence and remaining scope

Run `python3 wang_b_nonerasing_tm_compiler.py`. The writer and default
compare against the saved JSON receipt. The finite checks are:

* 18 exhaustive local rule/neighbor cases cover every allowed rule and
 each destination00,10,11. Separately executed ordinary-TM and physical-set
 Wang simulators agree on384 random bounded traces,4,843 TM steps and
 37,400 Wang instructions. There are246 halts,1,198 left exterior
 extensions and1,259 right exterior extensions, including h=0.
* 2,035 exact pair-word cases and128 padded physical traces check the bit
 orientation and padding semantics.
* 32 actual source ledgers span four TM tables, four native forms and both
 input interfaces. There are192 complete-output identities,96 signed and
96 positive, obtained from the independent raw residual oracles of both
 components under the actual coordinate lifts, not only from their final
 emitted polynomials.
* 112 halted packed outer histories contain952 chronological rows. The
 inherited eight outer equations and joined AND are checked before the
 four-action projection, followed by all four surviving outer equations
 and exact action-hat restoration. Native coordinates are placeholders;
 these fixtures are not claimed to be complete positive Pell zeros.

The TM and Wang interpreters use different state/tape representations;
the ordinary stepper does not inspect the Wang list. Erasing, partial,
stationary and invalid-target tables are explicitly rejected. These
checks support the general invariant and complete positive-converse
proof; finite tests alone are not the halting-equivalence argument.

An explicit universal non-erasing binary transition table, its ordinary
input convention, or a proved ordinary-TM-to-non-erasing table compiler
would supply the next missing interface. The present packet makes its
subsequent Wang expansion and ordinary binary input cost computable; it
does not fill that earlier gap or claim a numerical universal bound.

Author receipt generation and a fresh default replay pass. Root and
Native independently completed full proof/source/fresh-default reviews
with no findings. Native reopened the primary Theorem7 and Section3.1.
Its separate integer-tape Wang interpreter and dictionary TM simulator
passed192 traces,3,074 TM steps and23,702 Wang instructions, with134
halts and435 left/739 right exterior extensions, including odd physical
offsets. Its separate executor also passed144 complete namespace and
conjunction identities,72 signed, across12 table/form contexts. All four
local links resolve.

Root's independent packed-integer Wang executor and dictionary TM
simulator exhaustively covered32 one-state total tables,15 inputs and
two paddings:960 bounded runs,8,040 TM steps,63,034 Wang instructions,
664 halts and5,407 newly initialized blank pairs. Block-boundary states,
heads and complete tapes agreed throughout. These are physical trace
and algebraic checks, not constructed complete positive Pell zeros.
