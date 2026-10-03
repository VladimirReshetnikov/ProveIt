# Exact U9-to-tag metadata and a shorter ordinary-input block

The fixed Neary–Woods U9,3 table compiles to **1,968 binary clockwise
states**. Choosing actual input symbols 1 and 3 gives equal 16-symbol
physical input blocks, hence 64 binary cells per padded input bit. The
resulting fixed tag input width is

\[
 D=47946621298704238734708993009920.
\]

Its binary power schedule has 154 multiplications. The source supplies
and verifies a **127-multiplication addition chain** for the same D.
This packet proves the fixed table and complete ordinary-input word
contracts. It does not instantiate a new universal polynomial or claim
a whole-polynomial operation count. No tag production or integer with D
bits is materialized.

## 1. The exact fixed machine

Use Table 4 of Neary and Woods,
[Four Small Universal Turing Machines](https://mural.maynoothuniversity.ie/id/eprint/12416/1/Woods_FourSmall_2009.pdf),
with the visual transcription preserved in the
[explicit-machine source](neary_woods_explicit_universal_tm.py).
Definition 3.1 and Tables 1–3 specify the program, data and head position.
The blank is c, the start is u1, and the sole missing instruction is
`(u5,b)`. Replace it by a stationary transition writing b and entering a
fresh accepting halt. Rename `c,b,delta` as `_,0,1`, respectively. This
is an exact symbol renaming, including the external blank, with no extra
read-symbol convention.

Compile this ten-state, three-symbol table using the
[ordinary-to-clockwise compiler](ordinary_tm_clockwise_compiler.md).
No leading-zero prelude is applied to this encoded program tape. Start
at `run(u1)` and its binary read state at the original U9 head cut.
The complete table includes the compiler's ordinary entry and other
states; changing the initial cut does not prune or change any transition.
Number the binary start 1 and accepting halt Q.

| Quantity | Value |
|---|---:|
|Ordinary states, including halt|10|
|Ordinary symbols|3|
|Clockwise states C|49|
|Clockwise symbols|6|
|Clockwise instructions|288|
|Distinct clockwise output/target pairs E|226|
|Binary block width a|4|
|Binary states Q|1,968|
|Binary instructions|3,934|
|Distinct two-cell clockwise output/target pairs|18|
|Two-cell binary instructions T2|72|

The exact count is `Q=(C-1)2^(a-1)+(2a-1)E+2`. Each two-cell
clockwise output/target pair contributes a two-bit seek emission and
three two-bit marker emissions, so `T2=4*18`. The source checks all 27
renamed ordinary instructions, including the halt adapter.

## 2. Program slices and the U9 boundary caveat

For each r.e. set S of positive integers choose a semidecider whose
actual input symbols are numbered 1 and 3: the pair `(3,1)` encodes bit
zero and `(1,3)` encodes bit one. It decodes pairs, ignores leading zero
bits, and halts exactly on members of S. Malformed encodings and rejected
inputs loop. Symbol 2 can be unused or internal; relabeling and adding a
spare symbol are effective finite changes to this represented program.
The recognizer can satisfy the primary Lemma 2.1 convention that the
external blank is neither an input symbol nor a written symbol.

Apply that lemma and the primary bi-tag construction. Number the two
input symbols a1,a3 and the right and left boundary symbols ar,al,
which are distinct from the input symbols. The genuine initial bi-tag
word is

\[
 e_1\,\operatorname{pair}_{1,3}(w)\,a_r a_l.             \tag{1}
\]

This is a change in the represented recognizer's input convention, not
an arbitrary substitution into a fixed bi-tag program. Every length-n
zero-padded spelling of the same positive integer is valid for that
recognizer. For n at least 2, (1) has at least six A symbols. The two
boundary symbols persist, passive steps preserve the number of A's,
and active steps replace one A by one or two. Thus the number never
drops below six.

There is a recorded defect at a different boundary: the literal U9 table
on one specific singleton-A bi-tag word escapes along the right blank
ray instead of halting. The source repeats its finite escape certificate.
We do not claim the primary paper's unrestricted arbitrary-bi-tag
statement, or repair it by finite testing. We use its simulation on the
clockwise-machine slice above. In particular, an active step always has
an undeleted A symbol after its consumed pair; the nonempty remaining
word and its delimiter are available to the printed copy-and-restore
argument. When an E symbol reaches the left, at least six A symbols
remain to its right. This excludes the singleton boundary used by the
counterexample. The four finite accepting simulations below supplement
the imported step simulation; they do not establish universality by
experiment.

## 3. Exact physical cut, padding and counter

For U9 the encoded ordinary symbol and its separator are

\[
 A_i=b^{4i-1}\delta,
 \qquad V_0=A_3A_1,\qquad V_1=A_1A_3.                  \tag{2}
\]

Both V blocks have 16 symbols: fourteen b's and two deltas. For the
fixed bi-tag program word P_S and its A-alphabet size q_B, the primary
initial tape is

\[
 P_S\ \underline{b^{4q_B}}\ V_{w_1}\cdots V_{w_n}\ A_rA_l,
\]

where the underline marks the first b as the initial head cell.
There is no G word or extra trailing b as in the U15 encoding.
Insert the ordinary compiler's two exterior frames and cut the circle
at that same cell. The resulting physical clockwise word is exactly

\[
 \underbrace{b^{4q_B}}_{\text{prefix}}
 V_{w_1}\cdots V_{w_n}
 \underbrace{A_rA_l\,\mathrm{RIGHT}\,\mathrm{LEFT}\,P_S}
             _{\text{middle}}.                         \tag{3}
\]

The binary block codes are b=0000, delta=0001, LEFT=0010, RIGHT=0011
and c=0100. Consequently each binary data block has length 64, with
62 zeros and two ones. At the first differing position V1 has delta
and V0 has b, so its binary code is strictly greater.

The binary clockwise tape length is

\[
 s_0=64n+b_S,\qquad
 b_S=4\bigl(|P_S|+4(q_B+r+l)+2\bigr)>0.                \tag{4}
\]

Set `N_S=ceil(b_S/64)`. For dyadic n>N_S we have
`64n<s0<128n`, and 64n is dyadic. Hence the least power of two at
least s0 is exactly **128n**. Every ordinary positive x has arbitrarily
large dyadic padded durations satisfying this condition and x<2^n.
The machine interpretation is invariant under all such padding.
The generic compiler ledger's raw-bit fields a=4,b=8 describe its
other constructor; the actual program frame here is (4).

## 4. Exact cyclic-tag and tag metadata

Use the unchanged sparse primary-row assembler from the
[U15 metadata packet](neary_woods_u15_tag_metadata.md). Its convention
emits generic control/transition rows only for nonhalting i<Q, state-copy
rows for all i<=Q, the separate accepting self-copy at h=30Q+20, and
empty appendants elsewhere. These choices specify one exact table.
All assigned indices are checked for collisions. Here

\[
 z=30Q+61=59101,\quad p=2z=118202,\quad \beta=10p=1182020.
\]

With T2=72, the exact row formulas from that packet give

\[
 \Lambda=(56Q+30)z-40+(6z+40)T_2,
 \quad \text{ones}=25Q+21+3T_2.
\]

| Quantity | Value |
|---|---:|
|Sum of appendant lengths Lambda|6,540,710,510|
|Total ones|49,437|
|Nonempty appendants|45,286|
|Empty appendants|72,916|
|Maximum appendant length|472,848|

Apply the [fixed halt bridge](binary_tag_fixed_halt_bridge.md).
Choose the least s at least `11*max(p,max|alpha|)+3` with
`s=1 mod(beta-1)`. For this exact table the resulting values are

| Quantity | Value |
|---|---:|
|Track length s|5,910,096|
|b-count in u|4,536,351,183,510|
|c-count in u|2,449,500,490,410|
|Length of u|6,985,851,673,920|
|E_u, encoded length of u|5,362,069,348,135,347,630|
|K, encoded length of either CTS-bit block|6,338,014,228,120,114,128,608,890|

These follow from

\[
 b_u=6ps+20p^2-2+10(\Lambda-p),\quad c_u=\beta s-b_u,
 \quad E_u=(\beta+1)b_u+\beta s,
 \quad K=(\beta-11)E_u+10(\beta+2).
\]

The actual appendants, sparse ones, transition targets and per-family
subtotals are computed; these are not estimates obtained by discarding
the machine's transitions. The fixed tracks define every letter of u
without constructing that word in memory.

## 5. Complete symbolic input word and positive coefficients

Let Bcal replace each CTS bit i by the fixed b,c block B_i from the halt
bridge. Put `tau(0)=01 0^(2z-2)`, `tau(1)=001 0^(2z-3)`, and
`mu=10^(z-1)`. Let Pphys, Vphys_i, Mphys be the binary encodings of
(3). Then set

\[
\begin{aligned}
 \mathrm{PREFIX}&=u^{[1]}\,\mathcal B(S_1\tau(P_{\rm phys})),\\
 \mathrm{DATA}_i&=\mathcal B(\tau(V_{{\rm phys},i})),\\
 \mathrm{MIDDLE}&=\mathcal B(\tau(M_{\rm phys})),\\
 \mathrm{MU}&=\mathcal B(\mu),\qquad \mathrm{TAIL}=u.
\end{aligned}
\]

The complete tag input is

    PREFIX DATA_w1 ... DATA_wn MIDDLE MU^(128n) TAIL.

Its halting is equivalent to x in S on every allowed padding. Each
DATA contains 128z fixed CTS-bit blocks, while MU contains z. Thus,
writing t=zK for the encoded MU length,

\[
 D=128zK=128t=47946621298704238734708993009920.          \tag{5}
\]

The data words have equal b/c populations. Each B_i has length zero
modulo beta-1; the fixed `u^[1]` and final u give total fixed-frame
length one modulo beta-1. Hence the full input has length one modulo
beta-1, and its variable data-plus-counter contribution has length zero
modulo beta-1. It contains the final u, ends in b, and has length at
least beta, so the nonempty-history tag predicate applies.

The existing strict ordering proof applies without alteration: u starts
bcb, so `e(B0)>e(B1)`; tau reverses the bit comparison once more. Thus
the composite physical-bit encoding preserves order. Since Vphys1 is
greater than Vphys0 in Section 3, the encoded DATA values satisfy
`0<v0<v1<2^D`. This supplies the positive coefficient difference needed
by the compressed loader. Its other coefficients are positive fixed
frame/repunit expressions. They are effective program values; arbitrary
positive parameter tuples need not describe such valid programs.
The exact binary boundary uses its usual sentinel and the terminal block
`E(u)=e(u without its final b)10^beta`, as in that compiler's interface.

All input-format contracts for a future application of the
[compressed composer](binary_tag_parameterized_compressed_compiler.md)
are now specified. The source here does not compose that arithmetic DAG,
identify its program-bound coordinate with E, or certify its final degree.

## 6. Power schedule and verification scope

D has 106 bits and population 50, so its binary-method count is154.
The literal increasing exponent list in the source instead has127
entries. Each entry is checked to be a sum of two earlier exponents
(starting from1), and the last is exactly D. This proves a127-product
circuit for q^D over arbitrary integers q. The list came from a bounded
factor/window search; no shortest-chain assertion is made. In particular

\[
 D=2^8\cdot5\cdot37458297889612686511491400789.
\]

The checker independently resolves every addition step and tests64 signed
or unsigned modular bases. It also checks all27 source instructions,
all45,286 assigned CTS rows,48 complete physical program frames (each
program/input at two padding lengths), four literal U9 accepting runs
with both output arities and one or two active steps, and the known
singleton-A escape certificate. The latter five simulations use the
original published table. They are finite regression evidence; the
program-slice theorem uses the source simulation and invariants above.
The [receipt](neary_woods_u9_tag_metadata.json) records exact counts and
small examples, never a digest purporting to represent an expanded u.

Author writer and fresh-default replay passed. Native_controller's
independent full proof/source/fresh-default review passed without findings,
including a direct check of the primary three-cycle argument on the
nonempty-suffix slice. Its separate36 program/input frames, with
q=5,6,8 and h=2,3,4, checked full physical tape/head reconstruction,
equal data populations, strict ordering and the exact minimal counter.
Root's fresh-default replay and independent review of the primary
nonempty-suffix argument also passed.
No whole-polynomial operation bound is inferred from this review.
