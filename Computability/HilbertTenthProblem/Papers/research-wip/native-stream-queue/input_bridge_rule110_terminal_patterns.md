# Fixed terminal patterns in the exact Rule110 selector queue

The reviewed six-selector queue can require an arbitrary **fixed positive
terminal word P** in **74 operations**, or **75 with its paid all-selector
preamble**. The special word P=1 saves one multiplication. These are exact
finite-machine components with positive witnesses, not universal certificates.
The complete universal bound remains76.

Two cheap endpoint choices have precise limitations. With the paid preamble,
a power-of-two terminal word in state A accepts exactly the existing
empty-queue/state-C language. A fixed terminal word in state B bounds the
width and hence admits only finitely many ordinary inputs. Moreover, directly
using Cook's displayed spatial halting marker as the entire terminal queue
in state C gives an empty relation. The state-A version is nonempty, but
whole-word reachability differs from occurrence of that marker inside a
queue. No ordinary-input universal compiler or periodic-boundary conversion
is supplied here.

## 1. Exact source and cost

Retain the reviewed62-operation selector component and the six transitions
of [the exact Rule110 queue](native_controller_rule110_selector73.md). Reuse
its already-computed append word Aword and its paid read word R. Write
I=2x, or use the paid preamble I=128x+46. For a fixed positive numeral P,
replace the empty-queue transport equation by

    R + q*P = I + W*Aword.                              (1)

Keep I+width_beta=W and q=W*L. For final state A use the state equations

    F2+F3=2F1, F4=2F3+F5;                              (2)

for final C replace the second equation by F4+q=2F3+F5.
Equation(1) adds the literal instructions

    terminal_scaled=q*P; transport_left=R+terminal_scaled

to the72-operation state-A source, with a free comparison against the
already-computed I+W*Aword. At P=1 the product is omitted and q is reused.

| Final state and word | Input | Operations | M | A |
|---|---|---:|---:|---:|
| A, arbitrary fixed P>1 | 2x | 74 | 37 | 37 |
| A, arbitrary fixed P>1 | 128x+46 | 75 | 37 | 38 |
| A, P=1 | 128x+46 | 74 | 36 | 38 |
| C, arbitrary fixed P>1 | 2x | 75 | 37 | 38 |

Each source has19 equations and29 strictly positive witnesses besides x:
the eight other supplied parameters q,F0,...,F5,W and21 auxiliary
coordinates. P is a fixed numeral, not a varying witness or a function of x.
The [checker](input_bridge_rule110_terminal_patterns.py) independently
audits the complete schedules and their polynomial sources, including the
inherited auxiliary-norm correction, for the three instantiated sources
recorded in the receipt.

The exact projection is a binary width-m FIFO path of t>=m steps, from
(I,A) to(P,the stated final state), with W=2^m>I, q=2^t, all six labels
used, and the first label0. For the preamble input, its first seven labels
are exactly0,1,3,5,4,1,2 and already use all selectors.

No separate bound P<W is needed. Since R>=0, Aword<=q-1, and I<W,
equation(1) gives qP<I+Wq<W(q+1), and more directly

    qP = I+W*Aword-R <= I+W(q-1) < Wq.

Thus P<W. Telescoping proves the stated FIFO endpoint, because the read
and append words are genuine Boolean streams. Conversely every path in
this exact projection gives the Fi, q, W, positive width slack and L=q/W.
Its positive one-hot selector partition has F0 odd, so the reviewed62
theorem supplies all remaining strictly positive kernel coordinates. The
changed terminal equation does not alter that theorem.

## 2. Singleton words return to the existing acceptance condition

Fix W=2^m and P=2^j<W. A transition ending in state A has one of the forms

    A/read0/append0 -> A,
    B/read0/append1 -> A,
    C/read0/append1 -> A.

When the target queue is less than W/2, its last append bit is0. Therefore
its unique predecessor is the doubled queue in state A. Backtracking from
(P,A) forces m-1-j label0 steps back to(W/2,A), and one more step back to
(0,B) or(0,C). The first is impossible at positive time: every transition
into B appends1, so a queue in state B has high bit1. It is also not the
initial state A. Consequently the path previously visited(0,C).

Conversely, from(0,C), one label4 step gives(W/2,A), followed by m-1-j
label0 steps to(P,A). Both directions preserve the same width. The added
tail has m-j steps and does not require any conversion or new input code.

For the **paid-preamble sources**, this is an equivalence of full positive
certificates. The preamble finishes before any empty-C visit: W>=256 and
an A-to-C path has a positive append word, so emptying requires more than
m>=8 steps. Thus all six selectors are already present in the earlier
empty-C prefix. That prefix also has duration>m, as required by q=W*L.
Hence the74-operation P=1/state-A/preamble source has exactly the same
accepted ordinary inputs, width by width, as the already-reviewed74
empty-C/preamble source.

Without the preamble, positivity needs care. The final label4 in the added
tail may be the first occurrence of label4 in the whole run. For example,
initial queue10 at width16 first reaches(0,C) after the labels

    0,1,2,1,2,1,3,5,5,5,5,

which omit label4. The reverse argument still gives an empty-C path but
does not, by itself, give every positive selector in that prefix. No
unqualified equality of the two unprefixed positive-selector sources is
claimed.

## 3. Two necessary endpoint restrictions

If the final state is B, the final edge is label1, which appends1. Therefore
P>=W/2 and W<=2P. Since the initial word I<W, a fixed P allows only
finitely many ordinary inputs: for I=2x, necessarily x<P. Each remaining
width has a finite deterministic queue/state/used-label graph, so this
fixed-P/state-B family is decidable and cannot represent all r.e. sets.
Changing the state-flow boundary to B costs the same as a C boundary;
this necessary restriction is a machine statement, not an uncharged
additional source constraint.

There is also a simple forbidden-prefix condition for state C. Suppose
P's highest two binary digits are10, and let h be its bit length, so h>=2.
Backtracking from(P,C) through the m-h high zero append bits is forced:
the only edge into C with append0 is label5. The resulting target queue
is

    N=2^(m-h)*(P+1)-1

in state C. Its highest bit is1 and its next bit is0. Its predecessor
must therefore use label3 and end in state B with queue2N-W+1, whose
highest bit is0. But every edge entering B appends1. Thus no path of
m-h+2 or more steps reaches(P,C). Since every source path has t>=m and
h>=2, the complete fixed-P/state-C source is empty in this case.

## 4. A literal75 marker word and its exact limitation

Cook's primary construction uses occurrence of the spatial sequence
01101001101000 as a halting signal in a Rule110 orbit compiled from
periodic left and right backgrounds and a central encoded input. It does
not state that the entire finite tape becomes that word. See the opening
of [A Concrete View of Rule110 Computation, Section1](https://arxiv.org/pdf/0906.3248).

Read the displayed sequence in FIFO order, with its first bit at the unit
position. Its fixed integer value is P=1430. Its highest two binary bits
are10, so Section3 proves that the75-operation fixed-P/state-C source
with input2x is empty.

The **75-operation fixed-P/state-A source with I=128x+46 is nonempty**.
The receipt gives an exact positive outer map at

    x=10, I=1326, W=2048, t=87, q=2^87,
    terminal queue1430, terminal state A.

The path uses all six labels and the mandatory seven-step preamble. Its
fields satisfy every finite outer equation; the62 selector theorem gives
the complete positive kernel extension. Astronomical Pell coordinates are
not materialized in this finite check.

Nevertheless, marker occurrence cannot simply be replaced by this whole
terminal word, even in the same queue model with all selectors present.
For x=28 and W=2^21, at time176 the queue is183075 in state A. It contains
the displayed14-bit marker starting at bit7. All six labels have occurred,
the preamble is correct, and176>=21. The full prefix therefore has the
positive free-terminal source extension described in the reviewed queue
note. Yet this fixed-width deterministic orbit, exhausted through all3529
distinct(queue,state,used-label-mask) states before repetition, never
reaches queue1430/stateA with all selectors present.

This is a counterexample to the direct path/width implication from
substring occurrence to the chosen whole-word endpoint. It makes no claim
about another width for the same input, another detector, or another
compiled simulation. In addition to that detector issue, the source still
needs a proved transformation from varying ordinary x to the requisite
computation, fixed program numerals, and a correspondence between its FIFO
geometry and a universal boundary model. The75 count is not a new
universal bound.

## 5. Evidence and review scope

The author checker reproduces all source identities and counts. It checks
642 singleton/end-C comparisons on complete finite orbits for57 paid-
preamble inputs at widths8 through12, totaling16145 distinct orbit states.
It independently backtracks the impossible C marker at every width11
through30, checks the positive75 marker witness, and exhausts the3529-state
substring-separation orbit. These finite computations support the stated
examples; the all-width singleton and forbidden-prefix results are proved
above. The [saved receipt](input_bridge_rule110_terminal_patterns.json)
is reproduced by running the checker without `--write`.

Independent full proof, source, and default-replay review passed, including
the primary Cook citation and the positive-selector endpoint caveat.
