# A fully paid chronological compiler for a fixed Wang B program

For every fixed nonempty Wang B instruction list, this packet gives a
single Diophantine polynomial whose positive solutions are exactly its
nonempty halted histories between the supplied tape/head endpoints within
the nonnegative tape window.
Instruction choices, current-read branches, initial/final control and
common duration are paid. A second interface accepts one ordinary
positive integer x as the **literal binary Wang input**, with a paid
spatial shift; its existential positive projection is exactly halting
of that fixed Wang program on x.

The [source](wang_b_packed_program.py) and [receipt](wang_b_packed_program.json)
compile arbitrary finite lists of M,L,R,J instructions. This closes the
instruction-control obligation of the [motion component](wang_b_packed_motion.md).
It does not instantiate a universal Wang instruction table or pay the
published TM-to-Wang input morphism. The established75/87 and explicit288
universal bounds are unchanged.

The illustrative six-instruction list

    1:M, 2:R, 3:J(1), 4:L, 5:J(6), 6:M

has eight transition edges. With the reviewed normalized-unit finalizer,
its endpoint interface costs312 certificate operations and350=150M+200A
polynomial operations, with13 comparisons,37 positive witnesses and
degree at most3838. Its literal-input version costs314 certificate and
352=151M+201A polynomial operations, with13 comparisons,40 witnesses
and degree at most5767. The projected SOS alternatives357/1264 and
359/1900 remain available at17 comparisons and the same witness counts. These example counts concern this particular
program, which is not asserted universal.

## 1. Exact program convention and finite layout

The primary [Neary–Woods–Murphy–Glaschick paper](https://mural.maynoothuniversity.ie/id/eprint/12409/1/Woods_Wang_2014.pdf),
Definition6, uses a binary non-erasing bi-infinite tape. M writes1;
L/R move one cell; J(target) jumps precisely when the current cell is1.
All other cases advance one instruction. Falling off the list halts.
The paper's Theorem1 supplies effective TM simulation, but it does not
identify the ordinary binary input x here with its encoded TM tape.

We number the m>=1 instructions1 through m, start at1 and use m+1
as the terminal control label. Every J target must belong to1..m;
the API rejects a jump directly outside the program. For a nonjump
instruction at i, create one edge to i+1. For J(target), create the two
edges

    (i -> i+1, read0), (i -> target, read1).

They remain distinct when their targets coincide. If j instructions
are jumps, the number of edges is K=m+j. Let delta=1 when j>0 and0
otherwise. Supply K positive hats E_e_hat, with E_e=E_e_hat-1>=0.
There is one further positive branch_output_hat only when delta=1.

Keep the four positive endpoint parameters and all thirteen outer
witnesses of the motion parent. Its ten raw words are

    T,G,C,I,W,V,L,R,MH,LH,

with the additional Stay_hat. Keep its paid D, action repunit
J=I+L+R+Stay, P=(B-1)J+1, H=G+J, tape transport and folded head
transport. Replace only its fixed radix multiplier by

    c = the least power of two >= max(16,K+2),
    Bhalf=(c/2)D, B=Bhalf+Bhalf=cD.                  (1)

This still uses one fixed-numeral multiplication and one addition.
It preserves every parent range/head argument: c>=16>8. In particular,
D is a sum of the four positive endpoint parameters and height_slack,
so both endpoint tapes and heads are below D. The fixed integer c/2
is paid whenever used, not treated as an uncharged arithmetic step.

## 2. Bounds, one row partition and one common duration

Add the paid comparison

    sum_e E_e = J.                                  (2)

It gives 0<=E_e<=J at every zero, before using the native AND theorem.
The sum of any subset of edges is also bounded by J. This is the
pretyping bound needed for masks (B-1)sum_subset E_e<=P-1.
It is an explicit equation, not an assumed selector invariant.

Retain the parent global comparison, adding branch_output_hat when
there are jumps:

    J + sum_(ten words X) X_hat + global_bound
        + delta*branch_output_hat = P.              (3)

The last term is omitted entirely when delta=0. It costs one extra
addition when present. The positive left side excludes J=0. All ten
raw words, H=G+J and the branch output then lie below P. The parent
mark/move/left and range masks also lie below P as before. No use of
(2) or (3) assumes a typed radix or duration.

Keep the twelve AND lanes of the parent. Append K lanes

    E_e AND J = E_e.                                (4)

For jumps, append two further lanes specified in Section3. There are
L=12+K+2delta lanes. Every input/output coefficient is nonnegative on
all positive supplied tuples. At zeros each is below P by (2),(3).
Pack all three arrays in powers of P and prescribe the native scale

    S=B*P^L.                                        (5)

The source pays an explicit binary multiplication chain for P^L and
one multiplication by B. It folds the positive input hats into the
literal AND64 ports16A+12,16M+10,16Z+8 and q=16S. These are legitimate
positive native ports even away from the outer zero set.

The complete AND theorem gives S dyadic and Z=A AND M. Since B and P
are positive factors, both are dyadic. The repunit equation and J>0
give P=B^t and J=sum_(r=0)^(t-1)B^r for a unique t>=1. All lanes
were already canonical, so the joined AND splits exactly. The parent
lanes recover the tape, one-hot heads, action choices, selections and
both chronological transports at precisely these t rows.

By (4), each E_e has only Boolean digits at these same t row positions.
The coefficient of sum_e E_e in any base-B row is at most K<B by(1).
There is therefore no carry in(2). Every row has exactly one selected
edge. There are no independent controller rows before or after the
physical history and no separate unbounded time parameter.

## 3. Current-read branches and chronological instruction control

Let E_M,E_L,E_R,E_J be the sums of edges of the respective instruction
types. Add three paid comparisons

    I=E_M, L=E_L, R=E_R.                            (6)

The edge partition and the parent's four-action partition then imply
Stay=E_J. Thus a jump is read/stay, a mark stays, and L/R have their
specified physical actions. Each instruction selected at a row has
exactly its own physical action.

If j>0, let E_take be the sum of the read1 jump edges and let V_J be
branch_output_hat-1. The two appended AND lanes are

    C AND ((B-1)E_J) = V_J,
    H AND ((B-1)E_take) = V_J.                         (7)

Their mask bounds follow from(2). After edge typing, they give
E_J,r*C_r=E_take,r*H_r at each row. The parent already gives
H_r>0 and C_r in{0,H_r}, reading the **current** tape. On a jump row,
E_J,r=1, so the selected edge is the read1 edge exactly when the
current read is1. On nonjump rows both selectors vanish. One shared
positive output hat and these two native lanes enforce(7); no
separate uncharged multiplication of Boolean selectors is used.

Compute the two weighted control words with literal fixed-numeral
multiplications and additions:

    Current = sum_e source(e)*E_e,
    Next = sum_e target(e)*E_e.

Add the single paid chronological comparison

    B*Next + 1 = Current + P*(m+1).                  (8)

The row partition makes every Current digit lie in1..m and every
Next digit in1..m+1, all strictly below B. The constants1,m+1 are
also canonical. Uniqueness of base-B expansion of(8) gives:

* the first instruction is1;
* each row's target equals the next row's source;
* the final target is m+1.

No intermediate source can be m+1 because the table has no such edge.
Thus the certificate cannot halt early and resume. It certifies the
actual first halt at the end of this nonempty execution. The equation
is chronological; equality of aggregate incoming/outgoing edge counts
would not be a substitute.

For a concrete rejected shortcut, the program J(4),M,J(3),M on empty
tape has the exact lasso1->2->3->3. A false final-tape read would allow
1->4->5: the first jump sees a bit marked only by the later row. The
receipt packs this forged two-row history. All eight outer comparisons
and every other bit lane hold, but the selected-current-read lane in(7)
fails. This is a rejected outer fixture, not a full native Pell zero.

## 4. Full converse and literal-input halting projection

Take a genuine finite nonempty halted run in a nonnegative tape window,
with no left step from cell0, and the supplied endpoint parameters.
Choose a dyadic D>=16 greater than every tape integer/head and the sum
of the four positive endpoint parameters. Form B=cD, P=B^t, J, the
parent physical/action words, the actual edge masks and the branch
selected read. All hats are these nonnegative packed words plus1.
Every equation and joined AND lane then holds, including (8).

The height slack is positive. The motion parent's ten raw words sum
to at most(7D-2)J, while the branch output is at most DJ. Therefore
one coarse bound valid with or without jumps is

    global_bound >= (c-8)D*J-10 > 0.                (9)

For no jumps, the parent bound is stronger. This includes t=1.
The native input words are below P^L<S and their exact AND is the
output, with S dyadic. The complete AND64 converse supplies all22
positive native auxiliaries. No finite numerical Pell fixture is
needed or claimed in this existence argument.

For literal positive input x, the initial Wang tape has bit_j(x) at
cell j>=0, every other cell blank, and the physical head at0. Replace
the supplied initial tape hat by the computed register

    initial_tape_hat = x*initial_head + 1.           (10)

This costs exactly one multiplication and one addition. Move the
initial_head, final_head and final_tape_hat from parameters to positive
witnesses. The resulting polynomial has only x as its parameter.
Initial-head typing is **already paid** by the full motion history;
it is not inferred from the two gates in(10).

Any finite bi-infinite execution visits finitely many negative cells.
Choose b>=0 at least the negative of its least visited head position,
and translate every cell by b. With initial_head=2^b, (10) gives exactly
the translated initial tape x*2^b. Marks, both moves and current reads
commute with translation. Section4's converse therefore supplies a
positive certificate for every halted literal run.

Conversely, every positive zero has initial_head=2^b for an integer
b>=0, by the typed first row. Translate its decoded finite execution
back by b. Equation(10) restores precisely the original binary input
at head0, all negative cells initially blank. Sections2–3 give the
actual fixed instruction list and its first halt. Thus, with all other
coordinates existential positive integers,

    polynomial_program(x, witnesses)=0
        iff program halts on its literal positive binary input x.

This proves a uniform-in-duration fixed-program interface. The number
of gates and variables depends on the fixed program. It does not
replace the published TM input encoding by x or supply a numerical
universal program at the illustrative count.

## 5. Literal schedules, projections and degree bounds

Let C_W be the emitted endpoint certificate cost for a particular
program. The source records its exact multiplication/addition histogram,
including every fixed label and every power-chain multiplication.
The raw endpoint system has24 comparisons and35+K+delta positive
witnesses: the three parent outer equations, five new control equations
and sixteen native equations.

The reviewed [positive-scale rewrite](native_binary_positive_scale.md)
removes one native comparison and witness without changing C_W. Its
host hypotheses hold: q=16B*P^L>=16 before equations and the full
legitimate parent AND embedding was proved above. The reviewed
[computed-field rewrite](native_binary_computed_fields.md) then removes
six more comparisons and witnesses. Here q>0 and F3=16Z+8>0 before
equations. Both are full positive-zero bijections; they preserve all
controller data and the accepted literal inputs.

The default additionally applies the reviewed
[normalized native-unit helper](native_binary_norm_units.md) to that
six-field packet. It replaces the first positive root by its positive
gap, uses the three sign-safe norm units and the checksum, then includes
the normalized strong unit in their product W. Its recursive export and
dependency guards inspect the entire program interface, including edge
lists and absent optional branch ports. All program/control constraints
are independent of the five native auxiliaries reconstructed by strong
normalization.

The final polynomial is W*(1+sum retained_residual^2)-1. Over integers,
its zeros force W=1 and every retained residual zero. The helper's
actual mod4 sign argument and positive root map then restore the full
native kernel. Strong normalization preserves all outer coordinates by
i_old=Delta*i in one direction and a fresh canonical reconstruction of
f,i,j,o,y in the converse. It is not a bijection on every supplied native
tuple. It preserves the complete fixed-program history and literal-input
halting theorem proved above. No endpoint-flow relaxation or changed
read condition is introduced.

| Form | Endpoint polynomial | Comparisons | Endpoint witnesses |
|---|---:|---:|---:|
|Raw|C_W+71|24|35+K+delta|
|Positive scale|C_W+68|23|34+K+delta|
|Scale and six computed fields|C_W+50|17|28+K+delta|
|Normalized norm product|C_W+43|13|28+K+delta|

The normalized-unit certificate costs C_W+5; all other displayed
certificates cost C_W. Literal input adds2 gates and3 witnesses to each
row, with the same comparison count. It introduces no additional equation for(10), since
every use receives the computed register. All witness coordinates
remain strictly positive.

For a program-size upper bound, write
mu(L)=floor(log2 L)+popcount(L)-1 for the paid binary chain length.
Counting the56 physical prefix gates, edge definitions, subset sums,
weighted controls, up to six Horner gates per extra lane and the64-gate
native core gives

    C_W <= 115+7K+6L+mu(L)+delta*(j+3).              (11)

Literal input adds2 and the normalized-unit certificate adds5. The bound
charges every term; exact source CSE and
identity coefficients may make the actual ledger smaller. It is an
upper bound, not an optimal compiler claim.

Let e=1 for endpoint parameters and e=2 for literal input, nu=e+1,
sigma=e+L*nu and zeta=(L-1)*nu+1. D has degree at most e, P at most nu,
S and native q at most sigma, and the joined output at most zeta.
The propagated bounds for the displayed finalizers are

    raw or scale: 12*sigma+16;
    scale and six fields: 24*sigma+4*zeta+12;
    normalized unit product: 72*sigma+13*zeta+39.    (12)

For the six-field and unit forms, the computed native r has degree at
most3sigma+zeta,
X at most4sigma+zeta, a at most5sigma+zeta+1, c at mostsigma+2,
and d at most6sigma+zeta+3. Squaring the main norm bound gives(12).
For the unit form, the five factor bounds are respectively
11sigma+2zeta+5,30sigma+6zeta+14,6sigma+zeta+4,sigma,
14sigma+2zeta+12. Their sum is62sigma+11zeta+35 and the remaining
residual bound is5sigma+zeta+2, yielding(12). The first factor uses the
helper's guarded exact polynomial cancellation of the a^2*c^2 terms.
The source independently propagates every register degree and checks
these bounds. No zero-set equation or exact-degree assertion is used.

The six-instruction example has j=2,K=8,L=22,c=16 and C_W=307=132M+175A:

| Interface and form | Certificate | Polynomial | Comparisons | Witnesses | Degree bound |
|---|---:|---:|---:|---:|---:|
|Endpoints, raw|307|378=156M+222A|24|44|556|
|Endpoints, scale|307|375=155M+220A|23|43|556|
|Endpoints, six fields|307|357=149M+208A|17|37|1264|
|Endpoints, normalized units|312|350=150M+200A|13|37|3838|
|Literal input, raw|309|380=157M+223A|24|47|832|
|Literal input, scale|309|377=156M+221A|23|46|832|
|Literal input, six fields|309|359=150M+209A|17|40|1900|
|Literal input, normalized units|314|352=151M+201A|13|40|5767|

The example is intentionally a finite concrete compiler test. None of
these numbers is promoted to a universal polynomial bound.

## 6. Verification scope

```sh
python3 wang_b_packed_program.py
```

The receipt includes64 complete ledgers across eight programs, two
input interfaces and four native forms. It checks1,024 whole polynomial
identities,512 signed, against an independently assembled canonical
AND invocation after the exact coordinate lifts. Every emitted gate
reaches the output, and all degree/program-size bounds are checked.

There are240 genuine halted outer histories with1,336 chronological
rows, including112 duration-one histories and both branch outcomes
(80 read0 and148 read1 jump rows). They satisfy every outer comparison,
the actual joined AND and all positive bounds. Native auxiliaries are
placeholders: these are not numerical complete Pell zeros. The complete
positive extension is established in Section4.

The256 unit-form identities use a separate full raw-comparison oracle,
not only the helper's intermediate factor audit. After the composed
coordinate restoration, the normalized auxiliary factor equals
1+raw_auxiliary_residual exactly: the ordinary strong-RHS correction
cancels the normalization correction. The other factors are
1+raw_main_residual,1-4*raw_first_residual,1-raw_checksum_residual
and the new strong norm. Both complete finalizers and every retained
raw residual are checked. Off zeros, even positive root gaps may lift
to half-integral old roots (40 positive cases here); these are exact
rational identities, not
integer witness claims. At zeros the sign/parity theorem restores
integrality. Thirty genuine outer paths also transfer through all
unit maps without changing their words, bounds or eight outer equations.

A separate exhaustive714-edge-sequence audit checks exactly that
(8) is equivalent to initial/final/adjacent control consistency, and
the explicit future-read lasso fixture isolates the branch lane needed
for soundness. These checks supplement the all-duration proof; no
bounded testing is substituted for it.

Author receipt generation and a fresh default replay pass after the
normalized-unit integration. All six local links resolve. No parent
source or navigation file was modified by this packet.

The root reviewer completed full proof/source review and a fresh default
replay without findings. Its separate set-tape interpreter on640 random
programs produced461 halted literal-input histories with2,803 rows,
including261 traces visiting negative cells and409 read0/244 read1 jump
rows. It independently chose the spatial shift and every packed hat,
then checked all eight outer equations, joined AND/scale bounds and
literal input against the actual raw source without the author's run,
packing or independent-assembly helpers.

A second reviewer completed full proof/source/fresh-default review with
no remaining findings, including the primary Definition6 convention.
Its independent physical-set simulator and packing executor checked201
halted literal-input runs,91 visiting negative cells, with850 rows and
142 read0/58 read1 jump rows. Every outer equation and the joined AND
passed after translation. Both reviewers' physical fixtures are outer
histories, not numerical full native Pell zeros.

A third reviewer completed the normalized-extension proof/source review
and a fresh default replay without findings after clarifying the product
versus SOS degree label. Its separate literal executor and manual lifts
checked192 complete factor/retained-residual/both-output identities,
96 signed and96 positive, across four programs and both interfaces.
Those include33 positive half-integral off-zero root lifts. Independent
degree-envelope checks passed all eight contexts. The source and receipt
are frozen after these reviews.
