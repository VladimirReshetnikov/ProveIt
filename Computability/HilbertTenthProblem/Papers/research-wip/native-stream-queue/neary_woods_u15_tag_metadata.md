# Exact U15-to-tag metadata and the ordinary-input word family

The published U15 machine yields one fixed binary clockwise table with
**3,089 states**, hence one fixed cyclic-tag program and one fixed binary
tag production. Their exact size metadata can be computed without
materializing the enormous production or its encoded integer values.
For the construction here the required ordinary-input recoder width is

\[
 D=911894954830740789802965708213760,
 \qquad \mu(D)=160.                                    \tag{1}
\]

The integer D has 110 bits. The claim does not require allocating an
integer with D bits. Below we prove the complete fixed-program input
word format, counter synchronization, positive coefficient signs and
length congruences needed by the
[compressed arithmetic interface](binary_tag_parameterized_compressed_compiler.md).
The actual universal polynomial/source instantiation is a separate
composition; this metadata packet states no new arithmetic operation bound.

## 1. One fixed machine, with the head at the published cut

Use the literal Table16 transcription and ordinary-input universality
proved in [the explicit U15 packet](neary_woods_explicit_universal_tm.md).
Its only missing instruction is `(u10,b)`; replace that event by a
stationary transition writing b and entering a fresh accepting state.
This follows the actual table, not the paper's inconsistent halting
sentence. No U9 machine or arbitrary singleton bi-tag input is used.

Rename stored `c,b` as `0,1`. Introduce an external blank `_`, with
`delta(q,_)=delta(q,0)` for every one of the 15 ordinary states. Writes
remain zero or one. Mapping `_` to zero is a step-by-step projection to
the original U15 tape: state, head location and acceptance are preserved,
including excursions beyond either end of its finite nonblank description.

Pass this finite table, without the positive-input prelude, through
the [ordinary-to-clockwise compiler](ordinary_tm_clockwise_compiler.md).
The prelude must not erase the encoded program. For the input cut below,
use the fixed clockwise start state `run(u1)` and the corresponding
fresh binary read state. The compiler's general checkpoint invariant
applies to any head cut of a valid represented tape, not only its default
entry at the left frame. The emitted total table is unchanged.

| Quantity | Exact value |
|---|---:|
|Ordinary states, including accepting halt|16|
|Ordinary symbols, including external blank|3|
|Clockwise states C|78|
|Clockwise symbols|6|
|Clockwise instructions|462|
|Distinct output-word/target pairs E|353|
|Binary block width a|4|
|Binary states Q|3,089|
|Binary instructions|6,176|
|Distinct two-cell clockwise output/target pairs|32|
|Two-cell binary instructions T2|128|

The exact check is `Q=(C-1)2^(a-1)+(2a-1)E+2`. Each distinct
two-cell clockwise output contributes one two-bit seek emission and
`a-1` two-bit marker emissions, so `T2=a*32=128`. All remaining binary
rows write one bit. Number the binary initial state1, the halt stateQ,
and the other states by a fixed order of their finite names.

## 2. Literal cyclic-tag appendants as sparse words

Set `z=30Q+61=92731` and `p=2z=185462`. The primary
[Neary–Woods tables and halt clause](https://dna.hamilton.ie/assets/dw/NearyWoodsBCRI-04-06.pdf)
specify the clockwise simulation. Our exact convention is: emit generic
control and transition rows only for nonhalting `i<Q`; emit counter
state-copy rows for every `i<=Q`; give `h=30Q+20` its single self-copying
halt appendant; leave every unassigned appendant empty. This convention
is sufficient on the valid machine slice and fixes otherwise irrelevant
halting-state rows unambiguously.

The [checker](neary_woods_u15_tag_metadata.py) represents a binary word
by its length and the positions of its ones. Concatenation translates
those positions exactly. It instantiates every prescribed row, rejects
any repeated index, and keeps all actual transition targets and write
bits. This is a complete finite CTS program description, not merely
an estimate based on the number of states.

Writing `Lambda=sum_m |alpha_m|`, direct row counting gives

\[
\begin{aligned}
 \Lambda&=(56Q+30)z-40+(6z+40)T_2,\\
 \text{total ones}&=25Q+21+3T_2,\\
 \text{nonempty appendants}&=23Q+22,\\
 \text{empty appendants}&=37Q+100.
\end{aligned}                                          \tag{2}
\]

For clarity, the length sum decomposes as follows. For each nonhalting
state, its twelve control rows total `28z` and its six passive rows
total `10z`. Its four transition rows total `16z` when both binary
instructions write one cell; every two-cell instruction adds `6z+40`.
The global fixed rows contribute `82z-40`, all counter state copies
contribute `2zQ`, and the halt row contributes `2z`. These disjoint
families give (2). The checker records each family's actual subtotal.

The maximum appendant length is `8z+40` when a two-cell instruction
exists, and `4z` otherwise. In this table the former is attained.
The exact resulting values are

| Quantity | Value |
|---|---:|
|Lambda|16,114,983,722|
|Total ones|77,630|
|Total zeros|16,114,906,092|
|Nonempty appendants|71,069|
|Empty appendants|114,393|
|Maximum appendant length|741,888|

In particular `alpha0` is nonempty, and both it and `alpha_h` have
length p. Defining unused generic control rows at the halt state would
give different metadata; they are deliberately not part of this table.

## 3. Exact tag-production and block lengths

Apply the [fixed halt bridge's literal tracks](binary_tag_fixed_halt_bridge.md)
to that exact CTS program. Put `beta=10p=1854620`, and choose the least
integer s satisfying

\[
 s\ge11\max(p,\max_m|\alpha_m|)+3,
 \qquad s\equiv1\pmod{\beta-1}.
\]

This gives `s=9273096`. The production u is defined by interleaving
the fixed tracks; no expanded copy is needed to define it. Its letter
counts are

\[
\begin{aligned}
 b_u&=6ps+20p^2-2+10(\Lambda-p),\\
 c_u&=\beta s-b_u.                                    \tag{3}
\end{aligned}
\]

Indeed six p tracks remain all b; the two garbage tracks per appendant
contribute `20p^2-2` b's; the active tracks contribute `10(Lambda-p)`.
The last formula accounts for the initial-track deletion and the single
b in the special halt track. Every binary appendant bit contributes
ten b's to its short object regardless of whether that bit is zero or
one, so only appendant lengths are needed in (3).

Let `e(b)=10^beta1,e(c)=1`, `E_u=|e(u)|`, and
`k=(-11) mod(beta-1)=beta-12`. For `B_i=phi_i u^k`, the two equal-content
CTS-bit blocks, their common encoded length K is

\[
 E_u=(\beta+1)b_u+\beta s,
 \qquad K=(\beta-11)E_u+10(\beta+2).                   \tag{4}
\]

The resulting exact integers are

| Quantity | Value |
|---|---:|
|b-count of u|11,167,912,633,590|
|c-count of u|6,030,156,669,930|
|Length of u|17,198,069,303,520|
|E_u|20,712,262,494,490,622,910|
|K|38,413,148,432,644,759,683,038,410|

Equations (2)–(4), the finite sparse table and the track definition
specify every character of u effectively. The formal production-offset
numeral `val(1 e(u without its last b) 10)` is therefore a fixed integer
with an exact definition. It is neither a new variable nor a runtime
encoding operation. This packet never claims to hash an expanded u
that it did not construct; its recorded hash is of the finite sparse
CTS description.

## 4. The exact program-dependent physical input

For an arbitrary r.e. set S, use the already proved U15 program slice:
choose a recognizer that decodes pairs `(2,1)` for ordinary bit zero,
`(1,2)` for bit one, ignores leading-zero padding, and halts exactly on S.
Rejecting and malformed cases loop. The effective clockwise/bi-tag
translation yields a fixed program word `P_S`, with `q_B` bi-tag
A-symbols and distinct right/left marker indices r,l.

The primary encoding has

\[
 A_i=(cb)^{8i-5}bb,\quad
 V_0=A_2A_1,\quad V_1=A_1A_2,\qquad |V_i|=32.
\]

For a length-n padded spelling w, the finite U15 tape is

\[
 P_S\ b\ \underline{c}\ (cb)^{8q_B}\,
 V_{w_1}\cdots V_{w_n}\ A_r A_l,
\]

with the initial head at the underlined c, in state u1. Insert the
ordinary compiler's two exterior frames, then cut the circle at that
head. The exact clockwise word is

\[
 \underbrace{c(cb)^{8q_B}}_{\text{fixed physical prefix}}
 V_{w_1}\cdots V_{w_n}
 \underbrace{A_r A_l\ \mathrm{RIGHT}\ \mathrm{LEFT}\ P_S b}
             _{\text{fixed physical middle}}.           \tag{5}
\]

Apply the four-bit block code to every symbol in (5), with
`c->0000`, `b->0001`, `LEFT->0010`, `RIGHT->0011`. The binary
clockwise initial head is at its first block, in the fixed read state
for `run(u1)`. Its tape length is

\[
 s_0=128n+b_S,\qquad
 b_S=4\bigl(|P_S|+16(q_B+r+l)-12\bigr)>0.              \tag{6}
\]

Take the fixed positive program bound `N_S=ceil(b_S/128)`. For any
dyadic `n>N_S`, the exact least power of two at least s0 is
`c0=256n`: we have `128n<s0<=256n`, and `128n` is dyadic.
Every positive x admits arbitrarily large such padded durations with
`x<2^n`. The interpretation of (5) is invariant under all of them.
The inherited machine ledger's generic `initial_length_a=4,b=8`
describes its raw-bit constructor, not this U15 program frame. The
actual ordinary-input coefficient and overhead are exactly (6).

The initial bi-tag configuration lies on the established clockwise
simulation slice, containing the two permanent boundary markers and
at least four paired input symbols. No arbitrary bi-tag dataword
universality or different initial head convention is assumed here.

## 5. Tag word contracts and positive program coefficients

Let `Bcal` map each CTS bit i to the fixed b,c word B_i. Let
`tau(0)=01 0^(2z-2)`, `tau(1)=001 0^(2z-3)`, and `mu=10^(z-1)`.
Write `Pphys`, `Vphys_i`, `Mphys` for the binary block encodings of
the prefix, data blocks and middle in (5). The complete tag word is

    PREFIX DATA_w1 ... DATA_wn MIDDLE MU^(256n) TAIL,

where the following are literal fixed b,c words for each program slice:

\[
\begin{aligned}
 \mathrm{PREFIX}&=u^{[1]}\,\mathcal B(S_1\tau(P_{\rm phys})),\\
 \mathrm{DATA}_i&=\mathcal B(\tau(V_{{\rm phys},i})),\\
 \mathrm{MIDDLE}&=\mathcal B(\tau(M_{\rm phys})),\\
 \mathrm{MU}&=\mathcal B(\mu),\qquad\mathrm{TAIL}=u.
\end{aligned}                                          \tag{7}
\]

Here S1 is the fixed state1 CTS object, and `u^[1]` deletes u's first
letter as in the fixed halt bridge. The two data words have equal
b/c contents because they contain the same number `256z` of the
equal-content B_i blocks. Their encoded width and the counter width are

\[
 D=256zK,\quad t=|e(\mathrm{MU})|=zK,\quad D=256t,
 \quad |e(\mathrm{MU}^{256n})|=Dn.                     \tag{8}
\]

This proves the shared-scale relation, not just an inequality between
two independently supplied lengths. Substitution in (8) gives (1);
`bit_length(D)=110`, `popcount(D)=52`, hence the specified binary
power chain has `mu(D)=110+52-2=160` multiplications.

The length of every B_i is zero modulo `beta-1`, while the combined
fixed `u^[1]` and final u contribute one. Consequently

\[
 |\mathrm{PREFIX}|+|\mathrm{MIDDLE}|+|\mathrm{TAIL}|
       \equiv1\pmod{\beta-1},
 \qquad |\mathrm{DATA}_0|+256|\mathrm{MU}|
       \equiv0\pmod{\beta-1}.
\]

The word ends in b and contains the full final u, so its initial
length exceeds beta. On this valid machine slice the fixed halt
bridge proves halting exactly when the machine accepts; every such
halt reaches singleton b. Thus the nonempty tag-history predicate
applies without adding a singleton initial-word branch.

Finally `V_1>V_0` when `b>c`: after their first common three `cb`
pairs, `A1` contributes b while `A2` continues with c. The four-bit
physical code preserves this order. The normalization packet proves
that `e(B0)>e(B1)` and that the subsequent tau encoding reverses this
comparison once more; their composite on physical bits is order
preserving. Hence the two final binary data values satisfy `0<v0<v1`.
The shared loader's four fixed coefficients A,B,T,E are therefore
strictly positive, including its data-difference coefficient B.

For each S this effectively specifies the five positive program
values `A_S,B_S,T_S,E_S,N_S`. The exact boundary integer uses the
usual sentinel and `E(u)=e(u without its final b)10^beta` for the
terminal block. These are the coefficients and convention of the
compressed compiler. Every valid specialization represents the
intended accepting inputs. Arbitrary positive coefficient tuples need
not encode programs, and no typing of all parameter tuples is required
for this valid-slice universality statement.

## 6. Executable evidence

The [receipt](neary_woods_u15_tag_metadata.json) records the actual
finite machine ledger, sparse-table hash, every row-family subtotal,
track counts, D and its exact binary-chain length. Thirty-six smaller
complete tables check all row templates, length/one counts and both
write arities. Thirty-two independently materialized small track
constructions verify (3)–(4).

Sixteen small literal CTS runs simulate a complete clockwise step to
the first genuine accepting activation, including counter doubling.
Their decoder permits counter objects between tape objects after a
step, as the primary simulation does; it verifies the ordered tape
content and exact counter count rather than incorrectly requiring
the initial contiguous layout. Twenty-four actual published U15
program frames check (5)–(6), head placement, padded data, code order
and the minimal counter. These are word/transition fixtures, not
additional universal machines or complete numerical native Pell zeros.

Root independently reviewed the complete proof/source and passed a fresh
default replay, including all physical-input frame fixtures. The actual
interior head cut, input coefficient and overhead, minimal counter,
block ordering, positive program coefficients and congruences passed;
no findings.

Native_controller's full proof/source/fresh-default review also passed.
Its independent literal CTS enumeration confirmed all row and population
formulas, and 24 additional two/three-step runs (1,690,092 CTS steps)
verified the source tape and unique halt activation with the allowed
passive pending suffix. Two runs explicitly retain marked slash/prime
counter objects at that cut, as permitted by the fixed halt proof;
no unjustified canonical-counter assertion is used. No findings.
