# Exact control quotients of the U9 and U15 binary clockwise tables

Removing graph-unreachable control states and identifying states with
identical transition behavior reduces the two emitted binary clockwise
tables as follows.

| Fixed table | Original states | Reachable states | Quotient states | Two-cell quotient instructions |
|---|---:|---:|---:|---:|
| U9 | 1968 | 1814 | **1611** | 64 |
| U15 | 3089 | 2895 | **2575** | 118 |

The quotient preserves the **complete circular tape and head trajectory,
including the exact halting step**, on every nonempty binary input tape.
It therefore preserves both established ordinary-input program slices.
This packet recomputes their actual cyclic-tag tables and tag metadata.
It does not compose a new Diophantine polynomial or assert a universal
operation bound, a smallest clockwise machine, or an optimal power chain.

The [source](binary_clockwise_control_quotient.py) and
[receipt](binary_clockwise_control_quotient.json) contain the actual
quotient rules and every reachable original state's class. The existing
[U9](neary_woods_u9_tag_metadata.md) and
[U15](neary_woods_u15_tag_metadata.md) packets are unchanged.

## 1. Reachability and the finite equivalence relation

Use each parent's complete binary transition table and its actual start
`read(run(u1),empty_prefix)`. This is the already proved interior program
cut, not the ordinary compiler's generic left-frame entry. Every
nonhalting state has exactly one instruction for each read bit. An
instruction writes a word of length one or two and then advances the
head past that word. There is one distinguished halt, with no outgoing
instructions.

First follow both possible outgoing transitions from the start, ignoring
which bit sequences are realizable on a particular tape. This computes a
safe graph overapproximation of all states any genuine run can visit.
Every actual run remains in it by induction. Deleting other states
cannot change a run from the designated start. For both actual tables,
the halt belongs to this graph-reachable set; the API checks this
condition explicitly.

Partition the retained states initially into the singleton halt and all
nonhalting states. For a current partition C, assign a nonhalting state q
the signature

\[
 \bigl((w(q,0),C(t(q,0))),\ (w(q,1),C(t(q,1)))\bigr),             \tag{1}
\]

where w is the complete written bit word and t the target state. Give
halt a separate signature. Repeatedly group states with equal signatures.
Each new equivalence refines the preceding one. The implementation checks
this refinement on every state, rather than assuming that integer class
names remain the same. A step with the same number of classes is therefore
stable. Finiteness ensures termination.

Equivalently, the r-th refinement remembers the halt distinction and the
literal output observations through r steps of arbitrary read sequences.
Every stable equivalence respecting halt and the two literal transitions
is contained in every finite refinement, by induction. The final relation
is thus the coarsest such control bisimulation. This is a statement about
the exact transition signatures (1); it is not a general minimum-machine
theorem under other notions of simulation or language equivalence.

Number the start class 1, the halt class Q, and the remaining classes in
the source's deterministic order. Distinct halt/nonhalt status is never
lost, so the halt class has exactly the original halt as its preimage.
For every original reachable row, the source checks

\[
 \bar\delta(\pi(q),b)=(w(q,b),\pi(t(q,b))).                       \tag{2}
\]

It checks that all rows used to define the same quotient instruction
agree and that every quotient state is reachable. No arbitrary choice
among inconsistent representatives is possible.

## 2. Exact tape actions and both directions of halting

Represent a nonempty circular tape by the finite bit word starting at
its head. If the current word is `bv` and the instruction writes w,
the next head-based word is exactly `vw`. Start the original and
quotient machines on the same word, with states q and pi(q).
Equation (2) gives the same w and related target states. Their next
words therefore agree exactly. Induction proves that at every finite
step their tapes agree and their control states are related.

The halt has singleton preimage, so one run halts precisely when the
other does, at the same step and with the same word. This proves both
directions, including immediate halting. If neither ever reaches halt,
the equality holds through every finite prefix of the two infinite runs.
All writes are nonempty, so the head-based tape representation never
becomes undefined.

The proof applies to singleton tapes, malformed logical block patterns,
and arbitrary reachable starting states as well as the designated start.
It uses no marker alignment, input-range condition, native arithmetic
typing, or assumption about an accepting run. In particular, merging
different internal read/seek/emit states does not require defining a new
logical tape decoder: the quotient has exactly the old physical bit
trajectory, which the parent compiler already interprets.

## 3. Original program frames and the new fixed tag tables

Neither tape symbols nor the parent's four-bit symbol code changes.
The physical input words and their head cuts are literally the old ones.
Only finite control states are mapped by pi. Therefore the existing
program-dependent overhead b_S and initial binary tape lengths remain

\[
 s_0=64n+b_S\quad(\mathrm{U9}),\qquad
 s_0=128n+b_S\quad(\mathrm{U15}).
\]

For the same sufficiently large dyadic durations, the exact least
initialization counters remain 128n and 256n respectively. The U9
pair `(3,1)/(1,3)`, its persistent boundary markers and nonempty-suffix
simulation contract, and the U15 pair `(2,1)/(1,2)` all remain the parent
conventions. No new claim about malformed bi-tag input is introduced.
All permitted leading-zero padding still represents the same ordinary x.

Use the quotient's actual numbered transition table in the unchanged
primary CTS assembler. Its assumptions are exactly a total deterministic
binary clockwise table, one halt, and writes of one or two bits, all of
which were checked above. Generic control rows run through i<Q,
counter-state copies include i=Q, the sole halt activation is h=30Q+20,
and unspecified appendants are empty. Thus the new CTS table is fully
specified, rather than inferred only from a state count.

Set `z=30Q+61`, `p=2z`, and let T2 count the actual two-bit quotient
instructions. The previously proved row and track formulas give

\[
 \begin{aligned}
 \Lambda&=(56Q+30)z-40+(6z+40)T_2,\\
 \beta&=10p,\\
 s&=\min\{j:j\ge11\max(p,\max_m|\alpha_m|)+3,
                    \ j\equiv1\pmod{\beta-1}\},\\
 b_u&=6ps+20p^2-2+10(\Lambda-p),\\
 E_u&=(\beta+1)b_u+\beta s,\\
 K&=(\beta-11)E_u+10(\beta+2).
 \end{aligned}                                                   \tag{3}
\]

Here K is the encoded length of each fixed CTS-bit block. The new exact
values, computed from the actual quotient rows, are:

| Quantity | U9 quotient | U15 quotient |
|---|---:|---:|
| z | 48391 | 77311 |
| p | 96782 | 154622 |
| T2 | 64 | 118 |
| Lambda | 4385678850 | 11205306398 |
| Maximum appendant length | 387168 | 618528 |
| beta | 967820 | 1546220 |
| s | 4839096 | 7731096 |
| Length of u | 4683373890720 | 11953975257120 |
| E_u | 2943356682932470110 | 12002700795007383030 |
| K | 2848607087952190974367210 | 18558683993547570722895490 |

The data blocks still have 64 or 128 physical binary cells. Replacing
each by its length-2z CTS cell and then by fixed encoded blocks gives

\[
 \begin{aligned}
 D_9&=128zK=17644409035916092600397268366080,\\
 D_{15}&=256zK=367306347065639997480389946211840.
 \end{aligned}                                                   \tag{4}
\]

The fixed counter block has encoded length zK, so the exact common-scale
relations are still `D9=128|e(MU)|` and `D15=256|e(MU)|`.
The new production is defined by the same interleaved-track recipe.
Its prefix bcb, final b, fixed-halt cleanup, length congruences and
equal-content bit blocks follow from that construction as before.
Consequently the original physical-bit ordering proves the same strict
positive DATA coefficient difference, after rebuilding the fixed frame
coefficients for this new production.

This is a language-preserving change of the fixed machine and tag word.
It is not an identity between old and new arithmetic polynomials or a
claim that old native witnesses can be reused. Any later arithmetic
composition must use the new constants and widths in (3)–(4).
Their plain binary exponent schedules would use 151 and 154
multiplications, respectively; no optimized schedule or composed
polynomial count is claimed here.

## 4. Actual source and bounded evidence

`quotient(binary)` implements the finite construction. Its domain checks
totality, one distinguished halt, output lengths, target membership,
distinct start/halt and graph reachability of halt. `build('u9')` and
`build('u15')` invoke the actual parent builders and recompute each full
sparse CTS table and track metadata without materializing u or `2^D`.

The receipt contains every quotient rule, encoded as
`state:read -> written_word:target`, and the complete map from the
original finite state names to quotient numbers. It separately lists
each deleted graph-unreachable state. These are explicit descriptions;
the recorded table hash is not offered as a substitute for the actual table.

The U9 refinement stabilizes after 24 rounds and the U15 refinement
after 37. Exact all-row audits check 3626 and 5788 retained original
instructions respectively. The total removal splits into 154 unreachable
and 203 merged states for U9, and 194 unreachable and 320 merged states
for U15. U9 has 64 two-cell rows after reachability and after quotienting;
U15 has 120 after reachability and 118 after quotienting.

Each machine also has 768 bounded circular-tape traces, comparing a
queue-based original executor with a head-word quotient executor.
These include arbitrary reachable states, singleton tapes and malformed
block patterns. Every transition entering halt is checked separately
with five suffixes, and the halted initial state is checked directly;
acceptance is not inferred from whether a random trace happens to halt.
The finite traces supplement the general induction of Section 2.
No numerical full Pell zero, universal production expansion, or new
universal arithmetic bound is part of this packet.

Root's independent proof/source review and fresh-default replay also passed.

Author writer and fresh receipt replay passed. Independent substrates
proof/source/fresh-default review passed without findings. Its separate
stack traversal and moving-head circular-array executor checked all
9414 retained rows and 768 further traces totaling 73632 steps, including
singleton tapes and malformed block patterns; the independently audited
rules and state map agree exactly with this final source.

```sh
/tmp/diophantine-research-venv/bin/python binary_clockwise_control_quotient.py
```
