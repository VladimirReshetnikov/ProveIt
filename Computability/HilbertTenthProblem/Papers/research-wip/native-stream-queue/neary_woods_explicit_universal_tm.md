# An explicit universal TM table with a paid ordinary-input bridge

The 29-instruction Neary–Woods machine `U15,2` gives a concrete universal
polynomial with **1,072 operations = 445M + 627A**, **162 positive
existential coordinates**, and three positive program parameters. The
certificate has **992 operations = 418M + 574A** and 27 comparisons.
Its degree is 485,982. Keeping the initial affine-history value as one
additional positive coordinate gives **1,075 operations**, 163 witnesses,
28 comparisons and degree **9,100**. These are complete alternative
constructions, substantially larger than the existing universal 75/88
bounds.

The transition table, alphabet, cleanup rules and tile table are all
explicit. A selected language still determines three fixed integers
describing its initial tape frame. This is the usual universal-polynomial
parameter interface: the integers are free program parameters of one
polynomial, and become constants when representing a particular r.e. set.
There is no uncharged input encoding or selected-word certificate.

## 1. Exact source contract and table

The primary source is Neary and Woods,
[Four Small Universal Turing Machines (2009)](https://mural.maynoothuniversity.ie/id/eprint/12416/1/Woods_FourSmall_2009.pdf),
especially Sections 2–3, Tables 1–4 and 16. It gives ordinary one-tape
machines with finite nonblank configurations. The blank is `c`, the start
state is `u1`, and `U15,2` starts on the final `c` of `G=bc`, with its encoded
bi-tag program to the left. The published simulation is imported on the
clockwise-TM configurations produced in Section 2. The source file
transcribes Table 16 and, for comparison, Table 4. The final paragraph of
Section 3.5 contains a halting-symbol typo: Table 16's missing entry is
`(u10,b)`, whereas the paragraph names `(u10,c)`. The latter entry is
defined. Direct encoded halting runs agree with the table.

In the following compact transcription, a token is `write direction
next-state`; `—` means no instruction. The row `c` is the blank row.

| State | Read c | Read b |
|---|---|---|
| u1 | c R u2 | b R u1 |
| u2 | b R u3 | b R u1 |
| u3 | c L u7 | c L u5 |
| u4 | c L u6 | b L u5 |
| u5 | b R u1 | b L u4 |
| u6 | b L u4 | b L u4 |
| u7 | c L u8 | b L u7 |
| u8 | b L u9 | b L u7 |
| u9 | c R u1 | b L u10 |
| u10 | b L u11 | — |
| u11 | c R u12 | b R u14 |
| u12 | c R u13 | b R u12 |
| u13 | c L u2 | b R u12 |
| u14 | c L u3 | c R u15 |
| u15 | c R u14 | b R u14 |

The compiler renames `c` to `_`, replaces the sole missing instruction
by `(u10,b) -> (halt,b,S)`, and supplies the two-sided accepting cleanup.
All original instructions are moves, so the existing bounded-tape rewriting
compiler gives

\[
 29(2+1)+1+2\cdot2=92
\]

rewrite rules. Its alphabet consists of two tape symbols, three delimiters,
15 ordinary states and `halt`: 21 symbols, requiring width `d=5`.
The full-copy construction has 113 tiles. The default needs only the five
copy tiles for tape symbols and delimiters, giving **97 fixed tiles**.
The table and tiles do not depend on the represented language. No infinite
periodic background is used.

To justify the deletion, every well-formed configuration contains exactly
one control-state symbol, and every transition or cleanup rule consumes
that symbol. The contexts copied around the rule therefore contain no
state. Every accepting computation still produces a tile word using only
the retained copies. Conversely, the restricted tile set is a subset of
the original set, so the original GPCP soundness theorem applies. A
zero-step derivation would need to copy the state, but it is irrelevant:
initial `u1` and terminal `halt` are distinct. This argument concerns the
valid program slices; deleting state copies need not preserve the relation
on arbitrary malformed program-parameter tuples.

## 2. Equal-length input blocks and universality

Let `S` be an arbitrary r.e. subset of the positive integers. Choose a
one-tape recognizer `M_S` with the following explicit input convention:

* the two input tape symbols are numbered 1 and 2;
* input bit 0 is the pair `(2,1)` and bit 1 is `(1,2)`;
* the finite sequence of decoded bits may have any number of leading zeros;
* the machine halts exactly when the represented positive integer is in `S`.

Such a recognizer first scans and decodes the pairs, ignores leading zeros,
then simulates any recognizer of `S`. Rejecting or malformed inputs may loop.
It can have one halting state and never write the external blank: newly
visited blank cells are represented internally using an extra nonblank
symbol. These are finite changes to the represented program, not operations
performed by the Diophantine input circuit.

Apply the primary source's effective `M -> C_M -> B_M` constructions. Choose
the numbering so that the two input tape symbols correspond to `a1,a2`.
With the cut at the initial head, the initial bi-tag dataword is

\[
 e_1\;\operatorname{pair}(w)\;a_{\rm right}\;a_{\rm left}.
\]

This is a genuine encoded clockwise-TM configuration: the final two letters
are the right and left blank-boundary markers. The clockwise simulation
retains both, and a bi-tag active step replaces one `A` letter by one or two
`A` letters. With `n>=2` input bits, the initial word has at least six `A` letters,
and every subsequent computation keeps at least six.
The pair substitution takes place in `M_S`'s **actual input convention**;
it is not an arbitrary modification of a fixed bi-tag grammar.

For `U15,2`, an ordinary `a_i` and its following separator have the word

\[
 A_i=(cb)^{8i-5}bb.
\]

Hence `|A1|=8`, `|A2|=24`, and both bit blocks

\[
 B_0=A_2A_1,\qquad B_1=A_1A_2
\]

have exactly **32 tape symbols**, independently of the size of `M_S` or
`B_M`. Everything else is fixed for `S`. With `q_B=|A|`, the finite initial
configuration, including the position of the state symbol, is

\[
 [\;\langle B_M\rangle\;b\;u_1\;c\;(cb)^{8q_B}
 \;B_{w_1}\cdots B_{w_n}
 \;A_{\rm right}A_{\rm left}\;].
\]

The state precedes the final `c` of `G=bc`, exactly as required. The symbols
`(cb)^(8q_B)` encode `e1` and are fixed prefix material. On every allowed
zero-padded binary word for `x`, this configuration halts exactly when
`x in S`. The halting adapter and cleanup then reach `[halt]`.

The optional `U9,3` comparison uses `A_i=b^(4i-1)delta`, lengths 4 and 8,
12-symbol bit blocks, and symbol width 4. Its input dilation width is 48.
The default `U15,2` uses **dilation width 160 = 32·5**, distinct from the
tile alphabet width 5. Mixing up these two widths would invalidate the
construction.

## 3. Literal ordinary-input boundary

Encode tape/grammar symbols in base `2^d`, with `c` represented by digit 0
and `b` by digit 1. The source includes the remaining fixed symbol codes.
Write `val_d(w)` for the base value and
`code_d(w)=2^(d|w|)+val_d(w)` for its positive sentinel code.
Let

\[
 k=32d=160,\quad c_0=\operatorname{val}_d(B_0),\quad
 c_1=\operatorname{val}_d(B_1).
\]

The chosen pair order gives `0<c0<c1<2^k`: at their first differing tape
position, `B1` has `b` and `B0` has `c`.

The complete generic-width recoder supplies

\[
 q=2^n,\quad n\ge2,\quad 0<x<q,\quad Q=q^k,
 \quad z=\sum_{j<n}\operatorname{bit}_j(x)2^{kj}.
\]

Introduce one positive `R` and pay two gates and one comparison:

\[
 (2^k-1)R+1=Q.
\]

It forces the exact positive block repunit. Three further gates compute

\[
 D=c_0R+(c_1-c_0)z.
\]

For the length-`n` padded binary representation `w` of `x`, this is precisely
`val_d(B_w1...B_wn)`. In particular `0<D<Q`. The formula includes each
leading zero **block**, so no deletion of initial tape cells is implicit.

Supply three positive program parameters

\[
 p=\operatorname{code}_d(\text{prefix}),\quad
 a=2^{d|\text{suffix}|},\quad b=\operatorname{val}_d(\text{suffix}).
\]

Here prefix is everything before the variable blocks in Section 2;
suffix is `A_right A_left ] #`. Its final `#` makes `b>0`. Four paid gates
compute the complete initial bottom value

\[
 V_i=a(pQ+D)+b.
\]

The fixed terminal word is `# [ halt ]`, costing the same two final framing
gates as in the parent compiler. The variable affine-pair history starts at
`(1,Vi)` and ends at `(Uf,Vf)` with the terminal framing equality.

Before imposing any comparison, `R,z,p,a,b` are positive and `c1-c0>0`.
Consequently the computed `D` and `Vi` are positive even before recoder or
history typing. The native positive-coordinate projections therefore remain
valid. Every nonnegative or fixed numeral multiplication shown above is a
literal paid gate.

For arbitrary positive program parameters the polynomial still defines a
precise arithmetic relation; it is not asserted that these parameters
describe a valid initial configuration. For each `S`, the effective
construction in Section 2 supplies one valid positive triple `(p_S,a_S,b_S)`.
The resulting **single fixed polynomial** satisfies

\[
 x\in S\iff \exists y_1,\ldots,y_{162}>0:
 F(x,p_S,a_S,b_S,y_1,\ldots,y_{162})=0.
\]

The parameters are not existential witnesses. They are fixed when choosing
the represented set.

## 4. Complete histories, projection and cost

The file imports the literal fixed-width rewriting/GPCP construction from
[the complete fixed-program compiler](gpcp_complete_fixed_program.md),
and the complete selected-word arithmetic from
[the uniform affine-pair history](pcp_uniform_affine_pair_history.md).
The mixed-width composition changes only the initial frame and the width
used for the input recoder. Tiles and their affine maps use `d`, whereas
the recoder uses `k`.

Fresh-delimiter GPCP equivalence converts a valid initial configuration's
rewriting derivation to one common finite tile word and conversely.
The selected raw history comes from the paid
[slope-class/factored planner](gpcp_slope_class_compiler.md). Equal slopes
share selected products; the original tile selectors retain their order
and meaning. All candidate costs are actual literal DAG costs, and the
per-tile schedules remain available as fallbacks. The history compiler
types the word, its digit ranges, selectors and duration internally. Thus iteration, zero-padding, word selection and tape
boundaries are all paid. Genuine finite runs admit positive native extensions
by the imported full converses; the finite tests do not materialize their
astronomical Pell coordinates.

The same three-core projection as
[the complete unit compiler](gpcp_complete_fixed_program_units.md) is used
without alteration. Its nine sign-safe norms and one checksum are combined;
the other checksum is a separate comparison. The new repunit comparison
remains an outer residual. The final polynomial is

\[
 F=U\left(1+\sum r_i^2\right)-1,
\]

with exactly the same positive zero set as all retained comparisons.

If `H` denotes the selected raw history cost and `ell(k)` the binary-chain
length used to compute `q^k`, the raw certificate cost is
`H+139+ell(k)`: the previous six framing gates plus the five new block gates.
The unit projection adds nine multiplications. With computed `Vi`, the
result is

\[
 C=H+148+\ell(k),\quad E=27,\quad W=s+g+60,
 \quad\operatorname{cost}(F)=H+228+\ell(k).
\]

Here `g` is the actual selected-product count, equal to `2s` for the old
per-tile history and 5 for both selected slope-class histories.
Supplying `Vi` retains the certificate cost, adds one witness and one
comparison, and adds three final-polynomial gates. The four free variables
are `x,p,a,b` in every row below.

| Table / history | Vi | Certificate | Polynomial | Positive witnesses | Degree |
|---|---|---:|---:|---:|---:|
| U15,2, no state copies, slope classes | computed | 992 | **1072** | 162 | 485982 |
| U15,2, no state copies, slope classes | supplied | 992 | 1075 | 163 | **9100** |
| U15,2, all copies, slope classes | computed | 1073 | 1153 | 178 | 559006 |
| U15,2, all copies, slope classes | supplied | 1073 | 1156 | 179 | 9996 |
| U15,2, all copies, old contiguous | computed | 2198 | 2278 | 399 | 1567650 |
| U9,3, no state copies, slope classes | computed | 1111 | 1191 | 182 | 180670 |
| U9,3, no state copies, slope classes | supplied | 1111 | 1194 | 183 | 8092 |
| U9,3, all copies, slope classes | computed | 1166 | 1246 | 192 | 194950 |
| U9,3, all copies, slope classes | supplied | 1166 | 1249 | 193 | 8652 |
| U9,3, all copies, old contiguous | computed | 2450 | 2530 | 441 | 550522 |

For the default, `s=97`, `g=5`, `H=836`, `ell(160)=8`, and the history
scale exponent is `N=106`. For the U9,3 default, `s=117`, `g=5`, `H=957`,
`ell(48)=6`, and `N=126`. Both explicit compiler tables and the complete
default arithmetic DAG are saved in the receipt. Sixteen compact ledgers
also retain all-copy and old per-tile alternatives. The candidate planner
changes the proof's internal arithmetic schedule, not the actual fixed
transition table.

## 5. Exact degrees

All free parameters and positive witnesses have degree one. With `v=k+2`,
the history length degree is `nu=k+3` for computed `Vi`, since both prefix
and suffix scale are program parameters, and `nu=2` for supplied `Vi`.
Put `d_H=N nu`. The three norm blocks and their retained comparison degrees
give

\[
 \deg F=14+19v+20d_H-6\nu+84+8\max(d_H,v).
\]

This is an attained degree, not just a circuit upper bound. The checker
uses the exact cancellation identity for each main Pell norm from the unit
parent, propagates homogeneous degrees through every literal gate, and
evaluates a nonzero leading unit coefficient times a positive sum of leading
outer-residual squares. The added repunit residual has degree `k`, below
the displayed outer maximum. The body and positive-frame assertions are
checked independently of this degree audit.

## 6. Reproduction and finite boundaries

Run:

```sh
/tmp/diophantine-research-venv/bin/python neary_woods_explicit_universal_tm.py
```

The receipt audits both literal transition tables, every instruction in
24 independently generated finite contexts (including both tape-extension
directions), all sixteen arithmetic ledgers and exact-degree evaluations,
signed whole-polynomial projection identities, equal-block framing, and
the exact published initial cut for padded inputs. Published encoded
halting examples exercise both active-production arities, passive rotations
and a halt already present. These finite checks supplement the simulation
and arithmetic proofs; they do not themselves prove universality.

One deliberately retained negative boundary is outside our initialization
class: the U9,3 encoding of the two-symbol bi-tag word `e1 a1`, with
`e1 ai -> ai e2`, reaches `u1` beyond its last nonblank cell. Its `c -> bRu1`
rule then gives an infinite rightward ray. The receipt certifies that ray
finitely rather than by a timeout. The same example halts in U15,2. No
claim of correctness on arbitrary one-`A` bi-tag words is needed here;
the imported clockwise-TM slice retains both boundary markers throughout.

The exact named tables close the previous numerical-table gap for this
route. The substantially larger bound is useful as a fully instantiated
comparison, not as a reduction of the current 88-operation universal
polynomial.

Author receipt generation, independent full proof/source review and fresh
default replay, and root proof/source review pass without findings. The
independent reviewer visually transcribed both primary tables, separately
checked eight nontrivial encoded simulations with two active states, and
confirmed the U9,3 blank-ray boundary. Additional independent checks cover
384 complete cleanup derivations with randomized erasure order and 64
program-frame identities with varying bi-tag alphabets and padded inputs.
The source and receipt are frozen after these reviews.
