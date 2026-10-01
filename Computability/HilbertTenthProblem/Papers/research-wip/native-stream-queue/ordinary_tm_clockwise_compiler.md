# A literal ordinary-Turing-machine to binary-clockwise compiler

Given a finite ordinary Turing-machine table, this packet constructs a
finite clockwise table, its complete binary block simulation, and exact
state/alphabet ledgers. The initial word is explicitly

    c(LEFT) c(w1) ... c(wn) c(RIGHT),

with the binary head before the first block in a fresh nonhalting state.
An optional finite prelude erases leading-zero padding and runs the
supplied machine on the positive integer's canonical binary spelling.
Both head directions, stationary moves, written blanks, extension at
either blank boundary, and rejecting undefined instructions are handled.

This is an effective table compiler. The examples are small test
machines, **not universal tables**. It materializes neither the eventual
tag production nor its enormous integer encodings and asserts no new
Diophantine operation bound. An ordinary universal machine with the
required raw-input semantics still has to be supplied before a numerical
universal instance can be derived.

## 1. Source contract and primary construction

The source has a finite state set, a tape alphabet `Gamma` of size `g`,
distinct nonblank input symbols zero and one, a blank symbol, a start
state and one accepting state. A rule is

\[
          (q,s)\longmapsto(d,\mathsf{direction},p),
       \qquad \mathsf{direction}\in\{L,R,S\}.
\]

The head initially reads the first bit of the nonempty input; all other
tape cells outside that word are blank. A designated rejecting state
or missing nonaccepting instruction is interpreted as nonacceptance.
The compiler redirects both to one total nonhalting sink, which copies
the read symbol and moves right forever. Only the accepting state is
allowed to halt. The raw API requires start different from accept;
the optional fresh input prelude also handles an original immediate
accepting start.

The primary [Neary–Woods Lemma2.1](https://mural.maynoothuniversity.ie/id/eprint/12416/1/Woods_FourSmall_2009.pdf)
uses two exterior markers and a rotating carry to simulate left moves
clockwise. Its displayed right-boundary rules and subsequent bi-tag
rule `e_x a_i -> a_j a_k e_y` place the head after a whole two-symbol
replacement. We use that convention explicitly. Our table expands the
carry checkpoints, provides total error behavior, allows stationary
moves, and stores written blanks as ordinary interior symbols.

The [source](ordinary_tm_clockwise_compiler.py) exposes
`compile_tm`, `compile_positive_tm`, `binary_compile`, and `ledger`.
All transition tables are ordinary finite dictionaries. No simulation
instruction, state or alphabet symbol is specified by an infinite
family depending on the input duration.

## 2. Tape representation and explicit clockwise rows

For each source symbol `s`, including blank, introduce a distinct
interior symbol `[s]`. Add `LEFT`, `RIGHT`, and a temporary marker `M`.
The clockwise alphabet therefore has exactly `g+3` symbols. Around the
circle, a valid checkpoint represents

\[
          \mathrm{LEFT}\ [s_l]\cdots[s_h]\ \mathrm{RIGHT}.
                                                               \tag{1}
\]

The two frames represent the first blank cell outside the finite
interval on their respective sides. All cells farther out are blank.
Interior `[blank]` is a normal stored symbol, so arbitrary ordinary
blank writes do not violate the invariant. The represented interval is
never contracted; it grows when an exterior cell is written.

Write a clockwise tape cut as `s v`, with the head reading `s`.
Replacing it by one or two symbols `w` gives the next cut `v w`.
In particular the next head is on the next **old** cell.

The main states are `run(q)`. Let the represented read symbol be `s`,
interpreting either frame as ordinary blank. Suppose the source rule
writes `d`, moves as shown, and enters `p`. Its dispatch rows are:

| Direction | Read position | Clockwise write | Next state |
|---|---|---|---|
|Right|interior|`[d]`|`run(p)`|
|Right|`LEFT`|`LEFT [d]`|`run(p)`|
|Right|`RIGHT`|`[d] RIGHT`|`right(p)`|
|Left|interior|`M`|`carry(p,[d])`|
|Left|`LEFT`|`LEFT M`|`carry(p,[d])`|
|Left|`RIGHT`|`M [d]`|`carry(p,RIGHT)`|
|Stay|interior|`M`|`stay(p,[d])`|
|Stay|`LEFT`|`LEFT M`|`stay(p,[d])`|
|Stay|`RIGHT`|`M RIGHT`|`stay(p,[d])`|

The supporting states have literal rules as follows.

* `right(p)` copies each symbol until it reads `RIGHT`, then dispatches
  the source instruction for state `p` on blank. The scan is needed
  because the preceding right-boundary extension left the head beyond
  the inserted pair, at the old left frame.
* `carry(p,s)` on a nonmarker `t` writes `s` and enters `carry(p,t)`.
  On marker `M`, it dispatches state `p` with represented current
  symbol `s`. Thus the previous tape symbol is carried in finite control.
* `stay(p,[d])` copies every nonmarker symbol. On `M`, it dispatches
  state `p` with current represented symbol `[d]`.

At a dispatch for the accepting state, write the represented current
symbol and enter the one clockwise halt. This restores a carried
marker before halting. If dispatch instead begins an ordinary step,
its first write replaces the marker exactly as it would replace that
represented symbol. No stationary clockwise move or free tape update
is hidden at a dispatch boundary.

A fresh entry state copies the initial `LEFT` and enters `run(start)`.
Malformed symbols in a phase that disallows them enter a defined
copying loop. Every nonhalting emitted state has a rule for every
clockwise symbol; the unique halt has none.

## 3. Why the moving head and both blank boundaries are correct

A checkpoint is any of the following: a `run(q)` state; a `right(q)`
state reading `RIGHT`; or a `carry(q,s)`/`stay(q,s)` state reading `M`.
At the last two kinds, replace `M` conceptually by the carried symbol
`s` to decode (1). This is only a description of a finite-state
configuration. Its next actual instruction performs the dispatch above.

For the ordinary interior left move, write the old head cut as
`s a1 ... a(N-1)`. The first clockwise row writes `M`, with `[d]`
carried. Successive carry rows shift the other symbols clockwise. At
the return to the marker the actual word and carried value are

\[
 M\,[d]\,a_1\cdots a_{N-2},\qquad
                   \text{carried value }a_{N-1}.
\]

The decoded head cut is therefore
`a(N-1) [d] a1 ... a(N-2)`: precisely the predecessor of the old
head, after writing `d`. The same calculation applied to the two
extended words `LEFT M` and `M [d]` gives the boundary rows in the
table. At `LEFT`, one new interior cell is inserted on the left and
the next represented head is the new exterior left blank. At `RIGHT`,
the newly written cell is inserted before the right frame and the
next represented head is its predecessor.

Right moves on an interior cell or the left boundary are immediate.
The right-boundary scan returns to the new `RIGHT`, which represents
the next unvisited blank, without modifying the intervening word.
The stay scan likewise returns to the written position; its carried
value is constant, so the other cells are unchanged. These arguments
also cover writing ordinary blank at either boundary.

Every scan encounters its unique marker or right frame after finitely
many steps. If the current circular tape has `N` cells, an ordinary
instruction reaches its next checkpoint in at most `N+1` clockwise
instructions. The accepting checkpoint takes one further real row to
enter halt. The decoded configuration at each checkpoint is exactly
the corresponding ordinary tape, source state and head position.
Consequently there is neither an extra accepting path nor a finite
simulation that becomes permanently trapped inside a valid scan.
Halting agrees in both directions, including an infinite source run.

## 4. A paid-in-the-machine leading-zero prelude

`compile_positive_tm` first adds a fresh ordinary start state. On zero
it writes blank and moves right in that state. On one it keeps one,
stays on that cell, and enters the original start. Reading blank or
another symbol during this scan enters a rejecting loop.

For `w=0^k v`, where `v` begins with one, after exactly `k+1` source
steps the tape is blank on those first `k` positions, the head reads
the first bit of `v`, and the old start state is active. Translating
the ordinary tape coordinates by `k` gives precisely the old machine's
canonical input `v`, including blank cells to its left. This proves
halting equivalence for every leading-zero padding of every positive
integer. The prelude actually erases padding; it does not merely move
the head past zeros that the source machine could later revisit.
All-zero words reach the first exterior blank and then loop.

Apply the clockwise compiler to this finite enlarged ordinary table.
Its initial circular word is exactly

\[
               \mathrm{LEFT}\,[w_1]\cdots[w_n]\,
               \mathrm{RIGHT},                         \tag{2}
\]

and its head is initially on the left frame in the fresh entry state.
The input symbols and two frames are ordered first in the clockwise
alphabet. The established
[binary block compiler](clockwise_dyadic_input_normalization.md)
then assigns them

\[
 c(0)=0^a,\quad c(1)=0^{a-1}1,\quad
 c(\mathrm{LEFT})=0\operatorname{bin}_{a-1}(2),\quad
 c(\mathrm{RIGHT})=0\operatorname{bin}_{a-1}(3),
\]

where `a` is the least power of two at least
`max(2,1+ceil(log2(g+3)))`. Thus the binary initial length is exactly
`an+2a`. For dyadic `n>=2`, its least-power-of-two counter is `2an`.
All the fixed-block word identities and strict input-block ordering
in the normalization packet apply with these exact codes.

In particular `3<=g<=5` gives `a=4,b=8` directly from the supplied
ordinary table. A separately assumed universal binary clockwise
recognizer on raw input is unnecessary for this route. This statement
does not provide the missing actual ordinary universal table itself.

## 5. Effective state and symbol ledgers

The source closes a finite set of named states under every instruction;
the returned table, not an asymptotic bound, determines its size `C`.
If `S` counts source states after rejecting-state identification,
including accept and the new nonhalting sink, a coarse bound is

\[
                         C\le 3+S(2g+4).
\]

The terms count the entry/error/halt states, `run` and `right` states,
`g+2` possible carried symbols, and `g` possible stationary payloads.
The actual emitted table has exactly `(C-1)(g+3)` instructions.

Let `E` be the number of distinct pairs `(clockwise write word,target
state)` among those instructions. The imported binary compiler has
the exact state count

\[
 Q_{\rm bin}=(C-1)2^{a-1}+(2a-1)E+2.                  \tag{3}
\]

For each nonhalting clockwise state there are `2^(a-1)` binary read
prefix states, including the empty prefix; after the first bit, valid
prefixes begin with zero. Each distinct output/target pair has `a`
seek positions and `a-1` emission positions. The final two states are
the binary trap and halt. These state classes have distinct tags.
The checker confirms (3) against the independently emitted binary
table, whose instruction count is `2(Q_bin-1)`.

The CTS metadata is consequently the concrete integer tuple

\[
 z=30Q_{\rm bin}+61,\qquad p=2z,\qquad\beta=10p.
\]

For example, the first illustrative four-state, three-symbol test
machine with the positive-input prelude has `C=23`, `E=97`, `a=4`,
and `Q_bin=857`, giving `z=25771`, `p=51542`, `beta=515420`.
This example is intentionally nonuniversal. Its exact metadata shows
how a supplied table propagates through the interfaces; it is not a
universal arithmetic cost.

The binary table can be serialized when needed. This packet stops
before creating CTS appendants, the fixed production `u`, or encoded
word numerals. Even a moderate `Q_bin` can make those later objects
very large. A future symbolic representation of fixed constants must
still charge every use of those constants in the arithmetic circuit.

## 6. Replay evidence and scope

The [receipt](ordinary_tm_clockwise_compiler.json) includes one complete
clockwise transition table, its hash, twelve source/binary ledgers,
and compact trace evidence. Tests compare 544 complete finite traces
against an ordinary sparse-tape interpreter, covering 10,441 source
instructions, 158,398 clockwise instructions, 189 left extensions,
7,527 right extensions, 8,091 blank writes and 725 stationary moves.
For the deterministic fixtures, every clockwise instruction is also
expanded through the actual binary table, including entry and final
halt cleanup. Ninety-six exact prelude checkpoints and eight all-zero
loops are checked separately.

The correctness claim is parametric in the finite supplied table;
finite traces supplement the proof rather than establish universality.
To use the construction for a universal arithmetic bound, instantiate
an ordinary recognizer with a proved raw positive-input/program
convention, compute its actual table ledgers, and complete the CTS/tag
and arithmetic compositions. None of those missing steps is inferred
from a universal-machine existence claim alone.

Root independently reviewed the full proof and source and passed a fresh
receipt replay; no findings. Native_controller's independent proof/source
and fresh-default review also passed. Its separate circular-array and
ordinary-table simulator checked 240 traces on 40 partial machines:
6,331 ordinary steps, 109,115 clockwise steps and 1,198,732 actual binary
microsteps, including 70 accepting traces, 124 left extensions, 4,087
right extensions and 554 stationary moves. That audit interprets the
finite emitted rows without the checker's checkpoint decoder, macro,
trace or source-totalization helpers.
