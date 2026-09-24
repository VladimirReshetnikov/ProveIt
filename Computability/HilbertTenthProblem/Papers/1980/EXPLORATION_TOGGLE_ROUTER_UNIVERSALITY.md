# Toggle/router models: three primary-source interface checks

The ternary three-addition cell has a close local match to Langton's ant.
The primary universality constructions inspected here do not turn that
match into a finite-blank-background universal verifier. This is a bounded
audit of three sources, not a claim that no stronger walking model exists.
No arithmetic frontier is changed.

## 1. Langton's ant: finite circuits and infinite universal hardware differ

[Gajardo, Moreira and Goles, *Complexity of Langton's Ant*](https://arxiv.org/pdf/nlin/0306022)
distinguish two results. A finite initial pattern realizes a finite Boolean
circuit, yielding P-hardness of visiting a designated cell. Their universal
simulation instead uses infinitely many circuit copies in a trapezoidal
array. A finite input of the simulated cellular automaton changes the input
row; the ant's hardware still has infinite support. The undecidable event
is occurrence of an encoded finite block, rather than the ant stopping.
These distinctions are explicit in Sections 3-4, PDF pages 3-4. The
[published version](https://www.sciencedirect.com/science/article/pii/S0166218X00003346)
states the same finite-support versus infinite-support distinction.

For a concrete local convention, name the two colors 0=right and 1=left.
The visited color flips, and the ant turns according to the old color:

| Old color | Incoming direction | New color | Outgoing direction |
|---|---|---|---|
| 0 | N | 1 | E |
| 0 | E | 1 | S |
| 0 | S | 1 | W |
| 0 | W | 1 | N |
| 1 | N | 0 | W |
| 1 | E | 0 | N |
| 1 | S | 0 | E |
| 1 | W | 0 | S |

The rotate/write/move convention and its RL identification are formalized
in the next source, Section 1; moving first is an equivalent time-origin
convention only after positions are adjusted consistently.

## 2. Nontrivial turmites: a periodic background, not a blank one

[Maldonado, Gajardo, Hellouin de Menibus and Moreira,
*Nontrivial Turmites are Turing-universal*](https://arxiv.org/pdf/1702.05547)
use a four-direction head and colors in Z/nZ. A rule word in {L,R}^n
determines the turn; the visited color increases by one modulo n, then the
head moves in its new direction. RL gives the preceding two-color table.

The input contract is stated explicitly on PDF page 2 and in Theorem 2.1:
for a fixed simulated machine there is an infinite periodic hardware
configuration, and a finite pattern depending on the input perturbs it.
Theorem 3.1, page 11, implements this hardware with any nontrivial turmite.
Its reference to finite initial configurations concerns the simulated
machine or cellular automaton. It does not remove the turmite's periodic
background. The separate VISIT theorem, page 12, includes a finite time
bound in the instance and proves P-completeness.

The walker has no halt transition. A simulated halt must therefore be
observed through its encoded computation, not through disappearance of
the head or cessation of movement. No particular cheap native halt-pattern
test is supplied by that universality statement.

## 3. Rotary elements: a different local table and an infinite tape circuit

[Morita, *A Simple Universal Logic Element and Cellular Automata for
Reversible Computing*](https://www.cs.auckland.ac.nz/~cristian/UMCreadings/revcomputCA.pdf)
defines a two-state, four-input/four-output rotary element. Table 1 on
printed page 104, checked visually, is:

| State | Input | New state | Output |
|---|---|---|---|
| H | n | V | w |
| H | e | H | w |
| H | s | V | e |
| H | w | H | e |
| V | n | V | s |
| V | e | H | n |
| V | s | V | n |
| V | w | H | s |

With no signal the state is unchanged; simultaneous inputs are outside the
element's defined domain. A parallel signal passes straight without changing the bar;
a perpendicular signal turns right and changes its orientation.

The direct reversible-Turing-machine realization has infinitely many tape
modules (printed page 109), with a finite control and an End port. The
paper separately points to P3/P4 cellular automata that realize counter
machines by finite configurations using additional position-marker and
wiring structures (pages 102 and 113). P3's displayed local alphabet has
81 states, not a single Boolean memory bit (page 112). This is a distinct
finite-support direction, not a finite implementation of the displayed
infinite tape circuit by our cell alone.

## 4. What matches our arithmetic, and what still has to be encoded

The following comparison is our deduction from the displayed tables.
For the increment-form cell

    C=D+E, A+E=B+D,

an active visit C=1 flips A. Its output is E when A was zero and D when
A was one. Interpreting E as a relative right turn and D as a relative
left turn therefore matches the ant's active local update exactly. The
inactive case leaves the bit unchanged. This still requires four directional
head channels, consistent two-dimensional displacement, single-head
conservation, boundaries, and an initial hardware pattern. Those requirements
are not counted by the three additions.

The rotary element is not the same active update. With north input, both
of its initial orientations finish in V, although their output ports differ.
Our active cell always flips its bit. Extra routing or a different state
encoding would have to be proved before transferring the RE universality
construction to it.

A fixed finite network of these finite-state elements with one signal has
only finitely many configurations. Its eventual arrival at an output port
is decidable by detecting repetition. Thus a finite circuit drawing alone
does not supply an unbounded machine; something must provide unbounded
storage or growing geometry. Morita's direct construction uses the infinite
tape array, while its cited finite-support CA construction uses richer
movable structures. This argument concerns fixed finite hardware, not a
certificate allowed to quantify over larger finite computation witnesses.

The periodic turmite construction remains potentially usable for an
existential finite history: a finite run visits only finitely many cells,
whose initial values could in principle be constrained to the periodic
hardware plus the finite input perturbation. However, proving that the
finite witness has the required infinite extension, encoding the input pattern
from the raw query, and identifying an actual simulated halt event are
precisely additional compiler obligations. Truncating or freely guessing
the hardware would not establish them.

This audit therefore identifies an exact local match but no newly verified
strong finite-blank-background universal input/halting interface. It does
not infer present-day impossibility or a general open-problem status from
the older papers' statements.

## 5. Reproducible scope

`../verification/explore_toggle_router_tables.py` checks the complete ant
and RE tables against their respective geometric rules, their local
bijectivity, the active-cell match, and the fixed-north-input mismatch.
The adjacent receipt is a finite table check, not a universality test.
The Morita table snapshot is retained at
`../../tmp/toggle_router_sources/morita2001-table.png`; the downloaded
primary PDF is beside it. All other source assertions above were checked
against the linked primary PDFs and the exact sections named above.
