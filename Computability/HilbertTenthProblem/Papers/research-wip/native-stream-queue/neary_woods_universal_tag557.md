# An explicit universal polynomial through a fixed binary tag system

The fixed U15-to-clockwise-to-tag construction gives a universal
polynomial evaluable in **557=351M+206A operations**, with **69 positive
existential witnesses** and five positive program parameters besides
the ordinary positive input x. Its certificate uses483=326M+157A
operations and25 comparisons. The total degree is at most

    496070855427922989652813345268287100.

This reduces the explicit alternative machine construction from
[805 operations](gpcp_normalized_strong_compiler.md) by248 operations
and from125 to69 witnesses. The separate best established universal
polynomial bound remains [87 operations](complete75_normalized_strong87.md).
The805 construction remains a much lower-degree alternative. No minimum
or Lean-formalized result is claimed.

The [source](neary_woods_universal_tag557.py) and
[receipt](neary_woods_universal_tag557.json) retain the whole557-gate
schedule, every parameter and witness, the25 comparisons, and exact
finite recipes for all enormous fixed numerals. The polynomial uses
only addition, subtraction and multiplication. Fixed-numeral operands
are constants of that polynomial; their uses are charged.

## 1. One fixed universal machine and its actual binary table

Use the29-instruction
[Neary-Woods U15 table and ordinary-input theorem](neary_woods_explicit_universal_tm.md).
Its sole missing instruction is adapted to one accepting state. Rename
physical c,b to0,1. Add a distinct external blank whose transition in
each nonaccepting state equals the transition on0. Mapping that blank
back to0 preserves the original tape, head and state computation.

The [ordinary clockwise compiler](ordinary_tm_clockwise_compiler.md)
then gives78 states over six symbols,462 instructions and353 distinct
output/target pairs. The binary code width is4, and its actual expanded
table has

    Q_machine = 77*8+7*353+2 = 3089 states,
    6176 instructions, of which128 write two cells.

Enter this binary table at `read(run(u1),empty_prefix)`, the actual
interior tape cut. This is not the generic compiler's left-frame ENTRY
state. Number this start state1, the other nonhalting states in the
source's deterministic order, and the unique halt state3089. All
nonhalting instruction pairs are defined. Unreachable extra states
are harmless and are fully counted.

The [U15 tag metadata packet](neary_woods_u15_tag_metadata.md) specifies
the complete sparse cyclic-tag table and the fixed track production.
It gives

| Fixed quantity | Value |
|---|---:|
| z=30Q_machine+61 | 92731 |
| cyclic-tag appendants p=2z | 185462 |
| deletion beta=10p | 1854620 |
| maximum appendant length | 741888 |
| total appendant length | 16114983722 |
| common track length s | 9273096 |
| number of b letters in u | 11167912633590 |
| number of c letters in u | 6030156669930 |
| encoded bit-block length K | 38413148432644759683038410 |

The convention matters: generic nonhalt control rows are emitted only
for i<Q_machine, all-state counter-copy rows include the halt state,
the halt activation has its sole prescribed self-copying appendant,
and all unused rows are empty. This is the table for which the
[fixed halt bridge](binary_tag_fixed_halt_bridge.md) was proved.

The finite sparse appendants and interleaving rule define every letter
of u. The source's `production_letter` implements exact random access
to this word and agrees with the older materialized track constructor
on small fixtures. For the actual table it verifies the prefix bcb,
final b, and required length congruence. Its fixed large tile offset is
unambiguously

    d = val(1 e(u without its last b) 10),
    e(b)=10^beta1, e(c)=1.

The complete integer is not stored in binary. This is an effective
definition of one fixed coefficient, with no dependence on x, program
parameters or existential coordinates. Table and finite source hashes
identify the descriptions; no hash of an unexpanded word is claimed.

## 2. An effective program tuple for every positive r.e. set

For an arbitrary recursively enumerable positive set S, the frozen U15
input theorem supplies a finite encoded program that recognizes S on
every leading-zero-padded spelling w of x. Its two bit words are

    A_i=(cb)^(8i-5)bb,
    B_0=A_2 A_1, B_1=A_1 A_2,

both of physical length32, with B_1>B_0 under c=0,b=1. At the actual
head, the clockwise finite tape is the rotation

    c (cb)^(8q_B) B_w1 ... B_wn A_right A_left RIGHT LEFT <program> b.

The last two frames are the new clockwise compiler's logical tape
frames. The original U15 state marker, rewriting brackets and GPCP
delimiter are not physical tape symbols. The start is run(u1) before
the initial c, so the original head position is preserved exactly.

After the4-bit block code, each ordinary input bit occupies128 binary
tape cells. The whole binary tape has length128n+b_S, where b_S is
strictly positive and fixed for S. More explicitly, with i_right and
i_left the bi-tag frame indices,

    b_S=4*(|program|+16(q_B+i_right+i_left)-12).

Set N_S=ceil(b_S/128)>0 and require n>N_S. The paid dyadic-duration
recoder then gives a power-of-two n>=2 with x<2^n and

    128n < 128n+b_S < 256n.

Thus the exact least power of two at least the initial tape length is
**256n**. This discharges the primary cyclic-tag simulation's precise
counter contract; an arbitrary oversized counter is not substituted.
Every positive x admits arbitrarily long dyadic padded spellings, so
the bound removes no accepting input.

Let tau(0)=01*0^(2z-2), tau(1)=001*0^(2z-3), mu=10^(z-1), and let
the fixed halt bridge replace each cyclic-tag bit i by its fixed
equal-content tag block T_i. With G_i=e(T_i), both G_i have length K.
The resulting binary tag endpoint is exactly

    e(PREFIX) e(DATA_w1) ... e(DATA_wn) e(MIDDLE)
    e(MU)^(256n) E(u),

where PREFIX incorporates u without its first b, the fixed start-state
word and the fixed physical prefix; MIDDLE incorporates the remaining
physical tape through the program's trailing b; MU is the image of mu.
All program dependence is confined to the fixed frame words. The actual
tag TAIL is u. These definitions retain the full initial tape cut.

Every physical input bit block contains128 binary cells; each tau cell
has2z bits. Therefore the recoder width is the fixed integer

    D=256zK=911894954830740789802965708213760.

The encoded counter block has length zK, so D=256|e(MU)|. This is
exactly the common-scale relation required by the shared-counter loader.
The fixed frame has length1 modulo beta-1, each DATA/MU contribution
has length0 there, and the full word ends b. It has at least beta
letters. The four-tile history therefore needs no initially halted
singleton branch.

The coefficient ordering is strict. The fixed u prefix bcb gives
G_0>G_1; tau(0)>tau(1) reverses that order on physical tape bits.
The ordered0/1 block code and B_1>B_0 then give
val(e(DATA_1))>val(e(DATA_0)). Thus all four loader coefficients
A_S,B_S,T_S,E_S are positive. Their exact fixed-word formulas are in
the [shared-counter loader](binary_tag_shared_counter_loader.md).
The effective positive program tuple is

    (A_S, B_S, T_S, E_S, N_S).

## 3. The full polynomial equivalence

Apply the [compressed complete compiler](binary_tag_parameterized_compressed_compiler.md)
at the fixed D,beta,u above, exposing those five program ports. Its
duration is computed as N_S+positive_gap; this costs one addition.
The four coefficient parameters occupy already charged loader operands.
The computed history input is positive even before any comparison.

At a positive polynomial zero, the safe unit-product argument restores
every retained comparison and all three raw native kernels. The
dyadic recoder gives the genuine padded input, the loader gives its
exact framed tag word, and the selected four-tile history proves actual
tag halting. The unique-halt/parity-cleanup theorem then implies
acceptance of the fixed binary clockwise table. Its finite compilation
and U15 input theorem imply x belongs to S. Each implication is on the
valid program slice above; no assumption about malformed parameter
tuples is used.

Conversely, if x belongs to S, choose a dyadic n>N_S large enough to
pad x. Its U15 run and both finite machine simulations halt. The fixed
tag bridge halts at the singleton b, giving a nonempty tile history.
The complete recoder and history converses supply their independent
positive native witnesses and the exact loader repunit. The canonical
three-core reconstruction changes only fifteen auxiliary fields, so
it preserves the duration, program boundary and history checksums.
It supplies a positive zero of the normalized polynomial.

Consequently one fixed integer polynomial F satisfies, for every such S,

    x in S iff there exist y_1,...,y_69>0 such that
    F(x,A_S,B_S,T_S,E_S,N_S,y_1,...,y_69)=0.

All five program coordinates are fixed when choosing S; they are not
existentially quantified as part of the69 witnesses.

## 4. Actual source cost, alternatives and verification

D has110 bits and52 set bits. Its literal binary power chain therefore
costs110+52-2=160 multiplications. The source-derived ledgers are

| Form | Certificate | Comparisons | Positive witnesses | Polynomial |
|---|---:|---:|---:|---:|
| raw SOS | 468 | 56 | 88 | 635 |
| native units | 477 | 28 | 69 | 560 |
| three normalized strong witnesses | 483 | 25 | 69 | **557** |

The normalized split is351M+206A. Its degree bound544D+1660 includes
the free program coordinates. The unit and raw degree bounds are
342D+1042 and132D+412. These are upper bounds, not exact-degree claims.
The exact fixed numeral recipes, every topological dependency and all
557 operations are audited without expanding a numeral with D bits.

The application receipt checks the full finite source counts, the fixed
table/track constants, random-access production letters against small
literal tracks, and21 exact counter-boundary fixtures. Its proof imports
the separately reviewed whole-output/symbolic arithmetic checks and
machine simulations from the component packets. Those checks do not
materialize an astronomical full Pell zero or an accepting run of every
program. The general equivalence above supplies those existence claims.

Two independent final proof/source/fresh-receipt reviews passed with
no findings. One independently checked17,898 letters of the actual
giant production using forward track addresses and summed all185,462
semantic/garbage track contributions to the exact b/c counts and K.
The other reviewed the physical cut, bound, signs and finite coefficient
recipe alongside24 additional multistep CTS traces totaling1,690,092
literal steps, including marked passive counter suffixes at halt.
