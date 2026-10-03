# A paid six-label Rule110 scan queue in 73 operations

Six binary one-hot selector fields certify the exact three-state Rule110
scan controller, including its state transitions. Coupling this controller
to a fixed-width binary FIFO gives a complete finite-machine relation in
**73=36M+37A**, with19 equations and21 positive auxiliaries apart from its
nine positive parameters q,F0,...,F5,W,x. The input is the ordinary integer
2x; the terminal queue is zero and the terminal controller state is C.
Every one of the six transitions must occur.

This does not supply a universal representation theorem. The chosen terminal
condition is precisely reachability of an all-ones queue in state C, followed
by a forced erasing tail. No universality theorem for that reachability
condition, this input format, and this queue geometry has been proved.
The complete universal bound remains76.

The apparently simpler72-operation version ending in state A is empty for
every positive input. Thus a cleanup or acceptance convention cannot be
silently imported from the universality of the ordinary Rule110 cellular
automaton.

## 1. The six selectors and exact controller

Extend the [56-operation binary selector](native_controller_binary_selector56.md)
from four fields to six. Pack

    r=F0+qF1+q^2F2+q^3F3+q^4F4+q^5F5,
    F0+F1+F2+F3+F4+F5+1=q,
    s=2*odd_half+1, r+bound_beta=X=wq.                  (1)

The same43-operation core at scale q is retained. Horner packing costs10,
the checksum6, the odd quotient2, and the bound1: total62=31M+31A.
The proof of the four-field module extends directly. Before power recovery,
q>=7, r>=1+q+...+q^5, X>r, Y>=q, E>r+1 and a>2r+1, so every kernel
bootstrap inequality is stronger. Exact population count plus the checksum
then gives six one-hot binary words, with F0 odd. Conversely every such
positive partition has the same strictly positive kernel map. In particular
all six labels occur and t>=6 when q=2^t.

Use these transition labels:

| Label | Source state | Read | Append | Target state |
|---|---|---:|---:|---|
| 0 | A | 0 | 0 | A |
| 1 | A | 1 | 1 | B |
| 2 | B | 0 | 1 | A |
| 3 | B | 1 | 1 | C |
| 4 | C | 0 | 1 | A |
| 5 | C | 1 | 0 | C |

A remembers that the last read bit was0; B remembers01; C remembers11.
The table therefore computes Rule110 on each successive triple of read
bits, starting with an initial last bit0. This is an exact statement about
the scan transducer, not an identification of complete queue rounds with
standard synchronous cellular-automaton rows.

The indicator words for the source and target of states B and C are

    S_B=F2+F3, T_B=F1,
    S_C=F4+F5, T_C=F3+F5.

They are Boolean words because the selectors are one-hot. Initial state A
and terminal state C are exactly the two state-flow equations

    S_B=2*T_B, S_C+q=2*T_C.                            (2)

The first says that each B-source bit is the previous B-target bit, with
initial and terminal bits0. The second gives the same shift for C, with
initial bit0 and final target bit1. State A follows automatically because
the three source indicators and the three target indicators each sum to
q-1. In particular equations(2) do not merely test six edges between
preferred carry values: every position is an actual compatible transition.

Canceling one occurrence of F5 in the second equality reduces(2) to

    F2+F3=2F1, F4+q=2F3+F5.                            (3)

These cost2 and3 operations, respectively. Both directions of the bit-shift
argument are exact, including the final boundary bit.

## 2. FIFO, ordinary input and positive converse

Define read and append words

    R=F1+F3+F5, Aword=F1+F2+F3+F4, I=2x.

Supply positive width_beta and L and impose

    R=I+W*Aword, I+width_beta=W, q=W*L.                 (4)

After selector recovery, W is a power2^m and W>2x>=2, hence m>=2.
Both R and Aword are genuine length-t binary words. The exact transport
identity in(4) therefore proves a width-m binary FIFO run from integer2x
to zero. Its state sequence is the one proved by(2), starting at A and
ending at C. The forced first label0 agrees with I being even.

Conversely, take such a run, requiring that all six transitions occur.
Set Fi to its label indicator words, q=2^t, W=2^m,
width_beta=W-2x and L=q/W. The fields and width slack are positive.
Also t>m: some append1 occurs, and it must subsequently be read before
the terminal queue becomes zero. Thus L is a positive integer. Telescoping
proves(4), and the exact state indicators prove(2). The first transition is
label0 because the initial state is A and2x is even. Hence F0 is odd, and
the62 selector theorem provides every remaining positive coordinate.

The exact projection is therefore:

> There are m>=2 and t>m with W=2^m, q=2^t and2x<W, such that the
> deterministic table above has a t-step FIFO path from(2x,A) to(0,C),
> using all six labels, and Fi is exactly its i-th label word.

There is no uncharged binary dilation, block filter, arbitrary circuit
wiring, or unconstrained finite-controller subgraph in this statement.

## 3. Literal sharing and ledger

Sum the checksum fields in order1,3,2,4,5,0. Its intermediate prefixes
already include

    P13=F1+F3, Aword=F1+F3+F2+F4.

Consequently R=P13+F5 costs one extra addition, while Aword is free
register reuse. Append these eleven operations to the62 source:

    SB=F2+F3; TB2=2F1;
    TC2=2F3; rhsC=TC2+F5; lhsC=F4+q;
    R=P13+F5; I=2x; tail=W*Aword; transport=I+tail;
    width_bound=I+width_beta; divisor=W*L.

Compare SB=TB2, lhsC=rhsC, R=transport, width_bound=W, divisor=q.
The addition is5M+6A, giving73=36M+37A. The
[checker](native_controller_rule110_selector73.py) audits all19 independent
polynomials and the auxiliary-norm correction in the complete DAG.

## 4. The zero-queue/A endpoint is impossible

For terminal state A, replace the second equation in(3) by

    F4=2F3+F5.

This deletes lhsC's addition and gives a literal72=36M+36A source with the
same other equations. Its state indicators correctly encode an A-to-A
path. Nevertheless, no such path can both start at positive queue2x and
end with an empty queue.

Let k be the last read position containing1. It exists because I>0 and
R=I+W*Aword. A final state A means that this1 is followed by a read0.
Immediately after any read1 the controller is B or C; reading0 there
uses label2 or4 and appends1 at position k+1. But transport with I<W
says that every append1 at position j reappears as a read1 at position
j+m. This contradicts maximality of k.

The proof does not depend on all labels occurring and applies to every
positive initial queue less than W. A selected cyclic subgraph or a
padding argument cannot repair this endpoint.

## 5. Exact terminal-C meaning

At a terminal empty queue, the last m append bits are all0. To see this
arithmetically, R<q and R=I+W*Aword imply Aword<q/W=2^(t-m).
The only zero-output edges in the table are the isolated loops

    label0: A/read0 -> A, label5: C/read1 -> C.

No zero-output edge changes between these states. Since the final state
is C, all of the final m labels are5. Their read bits are all1, so the
queue and state m steps before termination were exactly(W-1,C).

Conversely, from(W-1,C), precisely m repetitions of label5 erase the
queue and retain C. Thus terminal-C emptying is equivalent to reaching
an all-ones queue in state C and then taking this forced tail. Under the
positive-selector interface, labels0 through4 must also have occurred
before that tail; the tail itself supplies label5.

This characterizes the actual accepting marker. It does not prove that
this marker corresponds to halting in a universal simulation, or that
ordinary2x is a suitable universal input encoding. In particular, the
known Rule110 local rule alone supplies neither assertion.

## 6. A paid preamble that visits every selector

A useful loading interface, derived independently in the input-bridge lane,
is the seven-label A-to-A path

    0,1,3,5,4,1,2.

Its low-first read bits are0111010, integer46; its append bits are0110111,
integer118. Replace I=2x by

    I=128x+46.                                         (5)

This uses one multiplication and one addition, one operation above the73
source. The complete literal variant is **74=36M+38A**, with the same19
equations and supplied-coordinate counts. Since I<W and x>0 force W>=256,
the first seven reads come from this prefix before any appended bit can
return. They force exactly the displayed path and return the state to A.
The queue at that point is exactly

    x+118*(W/128).                                      (6)

The divisibility in(6) follows from W being a power of two at least256;
no operation performs an unpaid division. Every selector has now occurred,
and the origin condition holds. Thus this preamble explicitly discharges
those two restrictions for the remainder of the run.

It does **not** load x into an otherwise zero queue: it retains the specified
high marker118. No universal input-normalization theorem for(6) is claimed.

## 7. An unconstrained terminal queue makes a75 variant trivial

Start instead from the72 version ending in state A. Keep the paid prefix(5),
supply a positive terminal queue T, and replace transport by

    R+q*T=I+W*Aword.                                   (7)

The extra product and addition cost2, so this literal source has
**75=37M+38A**. It accepts **every positive ordinary x**. This is a full
positive-witness statement, not merely a logical path that ignores the
arithmetic interface.

For any x>0 choose a power W=2^m strictly greater than2I and run exactly
m steps. Then q=W and L=1. The first full sweep reads precisely I, whose
top bit is0. Every controller state on read0 goes to A, so the sweep ends
in A. The first seven steps contain every transition by Section6. The
append word Aword is positive, since that prefix emits1. Take T=Aword;
the queue after a full sweep is exactly this word. Then R=I and(7) holds
identically. All six field words are positive, F0 is odd, width_beta=W-I
is positive, and the62 selector theorem supplies all positive Pell and
new-bound coordinates.

Hence allowing arbitrary positive terminal content fails to define a
nontrivial acceptance condition in this particular75 source. A terminal
marker must be specified and its connection to simulated halting proved.
The argument does not exclude different constrained terminal words or a
different finite controller.

## 8. A positive witness and finite evidence

For x=1, W=8, the following twelve labels form an admitted run:

    0,1,2,0,1,3,4,1,3,5,5,5.

It starts at queue2/stateA and ends at queue0/stateC; all six labels occur.
The final three steps are the forced tail from queue7/stateC. Its six
positive field words and all finite outer coordinates are included in the
[saved receipt](native_controller_rule110_selector73.json). The positive
Pell extension follows from the62 selector theorem, rather than numerically
materialized astronomical tuples.

The checker exhausts335,922 arbitrary one-hot label words through length7
and verifies that the two state-flow equations are equivalent to actual
A-to-A or A-to-C paths. Absent labels are allowed in that independent
flow test. It separately explores the entire deterministic queue graph
for every positive input2x<W at widths m=2 through10, tracking the set of
used labels. A repeated queue/state/used-label set closes the finite
search; there is no arbitrary step cutoff. Every admitted run is checked
against all finite outer equations and its forced all-ones erasing tail.
The checker also audits all19 source polynomials for the74 preamble and75
free-terminal variants, and checks100 concrete full-sweep witnesses for
the all-inputs construction of Section7.

These finite scans are not a classification over unbounded widths. They
do not establish universality or decidability of the terminal-C reachability
language. Run the checker without `--write` to reproduce the receipt.
Independent full proof, source, and default-replay review passed.
