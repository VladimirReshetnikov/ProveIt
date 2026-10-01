# An explicit U9 tag polynomial in 524 arithmetic operations

The fixed U9,3 machine and its complete input format give a universal
polynomial using **524=318M+206A operations**,69 positive existential
witnesses and four positive program parameters besides the ordinary
positive input x. Its certificate costs **450=293M+157A operations**
and25 comparisons. The total degree is at most

    26082961986495105871681692197398140.

This saves four multiplications over the
[528-operation U15 construction](neary_woods_universal_tag_chain.md)
and lowers its degree bound. The separate best established universal
polynomial bound remains [87 operations](complete75_normalized_strong87.md).
Neither exact degree nor an optimal exponent chain is claimed.

The [source](neary_woods_universal_u9_tag_chain.py) and
[receipt](neary_woods_universal_u9_tag_chain.json) retain the complete
524-gate DAG, every parameter and positive witness, all25 comparisons,
the127-step exponent certificate, the actual finite table hashes and
exact recipes for every huge fixed numeral. No such numeral is an extra
variable or an uncharged runtime arithmetic operation.

## 1. The actual fixed machine and coefficient recipe

Use the full [U9 metadata and input-format theorem](neary_woods_u9_tag_metadata.md).
It starts from the literal Table4 of Neary and Woods, with26 defined
instructions and sole missing instruction `(u5,b)`. A stationary
accepting adapter gives27 instructions. Rename physical `c,b,delta`
to the ordinary tape symbols `_,0,1`; this is an exact symbol renaming,
including the original blank, not an added read-symbol assumption.

The ordinary-to-clockwise compiler emits49 states,288 instructions
and226 distinct output/target pairs over six symbols. Its four-bit
block compiler therefore has

    Q_machine=(49-1)*8+7*226+2=1968 states,
    3934 instructions, of which72 write two cells.

The fixed binary start is `read(run(u1),empty_prefix)` at the published
interior head cut. Number it1, the remaining nonhalting states by the
specified finite-name order, and the accepting halt1968. The source
hashes that actual finite binary table. No source state is silently
pruned when changing from the generic left-frame entry to this cut.

The sparse cyclic-tag row constructor and fixed-halt tracks are unchanged.
Generic control and transition rows use only nonhalting states; counter
state-copy rows include the accepting state; its distinguished halt
appendant is specified separately; unassigned appendants are empty.
The resulting exact metadata is

| Fixed quantity | Value |
|---|---:|
| z=30Q_machine+61 |59101|
| Cyclic-tag appendants p=2z |118202|
| Deletion beta=10p |1182020|
| Sum of appendant lengths |6540710510|
| Maximum appendant length |472848|
| Common track length s |5910096|
| b letters in u |4536351183510|
| c letters in u |2449500490410|
| Encoded length E_u |5362069348135347630|
| Encoded CTS-bit block length K |6338014228120114128608890|

The complete sparse table determines each letter of u by the fixed
interleaving rule. The imported `production_letter(table,counts,index)`
provides exact random access for this U9 table, with no U15-specific
constant in its rule. It verifies that u begins bcb, ends b and has
length one modulo beta-1. Thus the production offset

    d=val(1 e(u without its last b) 10),
    e(b)=10^beta1, e(c)=1

is one completely specified fixed integer. The source records the
actual sparse-table hash and its exact coefficient recipe; it does not
claim to hash an expanded production. All eleven fixed-numeral roles of
the compressed compiler are specialized to this D,beta,u.

## 2. Program slices, the exact head cut and counter

For each r.e. set S of positive integers choose a recognizer whose actual
input symbols are numbered1 and3, with `(3,1)` encoding bit zero and
`(1,3)` encoding bit one. It decodes the pairs, ignores leading-zero
padding and halts exactly on S. The internal or spare symbol2 and the
remaining program alphabet are fixed when selecting S. The primary
ordinary-to-clockwise-to-bi-tag construction then gives one finite
encoded bi-tag program P_S with two permanent boundary symbols a_r,a_l,
distinct from the two input symbols.

The genuine initial bi-tag word is

    e_1 pair(w_1)...pair(w_n) a_r a_l.

For n>=2 it has at least six A symbols. Passive rules preserve their
number, and active rules replace one A by one or two, so this property
persists. This valid clockwise-machine slice is essential: the known
singleton-A U9 escape case lies outside it. We import the proved
simulation on this slice, not an unrestricted arbitrary-bi-tag claim.

For the U9 physical code,

    A_i=b^(4i-1) delta,
    V_0=A_3 A_1, V_1=A_1 A_3.

Each V block has16 physical symbols, fourteen b's and two deltas. The
original head reads the first b of the e1 encoding `b^(4q_B)` immediately
after P_S. Insert the ordinary compiler's exterior frames and rotate
the circle to that same head. The exact physical clockwise input is

    b^(4q_B) V_w1 ... V_wn A_r A_l RIGHT LEFT P_S.

There is no U15 G word, extra trailing b or included state symbol.
The binary block codes are b=0000,delta=0001,LEFT=0010,RIGHT=0011
and c=0100. Hence every ordinary input bit occupies64 binary cells,
and the entire binary tape has length

    s0=64n+b_S,
    b_S=4*(|P_S|+4*(q_B+r+l)+2)>0.

The four loader coefficients A_S,B_S,T_S,E_S are computed from the
fixed encoded prefix, middle and tail, as in the
[shared-counter loader](binary_tag_shared_counter_loader.md).
In particular E_S is exactly the sentinel integer of their concatenation
with the variable data and counter omitted. PREFIX and MIDDLE already
encode all b_S fixed binary tape cells through nonempty blocks. Thus

    E_S >= fixed encoded length >= b_S >= ceil(b_S/64).

Use the existing E parameter as the duration bound:

    n=E_S+positive_gap.

The one charged addition and the witness count are unchanged. The
recoder forces n to be dyadic and at least2. Therefore

    64n < 64n+b_S < 128n,

and the exact least power of two at least s0 is **128n**. An arbitrary
larger counter is never substituted. Every positive x has arbitrarily
large dyadic padded spellings satisfying both n>E_S and `x<2^n`; the
fixed recognizer accepts the same x under all of them.

## 3. The shared data/counter scale and complete positive equivalence

Let tau(0)=01*0^(2z-2), tau(1)=001*0^(2z-3), and mu=10^(z-1).
Replace each CTS bit i by its fixed halt-bridge block T_i. Their encoded
words e(T_i) have equal length K and equal physical b/c populations.
The full tag input is exactly

    PREFIX DATA_w1 ... DATA_wn MIDDLE MU^(128n) TAIL,

where PREFIX includes u without its first b, the initial state object
and the physical prefix; MIDDLE encodes the rest of the physical tape
through P_S; MU encodes mu; and TAIL is u. In the binary endpoint the
last block is E(u), using the inherited terminal convention.

Each DATA contains64*2z=128z CTS-bit blocks, while MU contains z.
The recoder width is consequently the fixed integer

    D=128zK=47946621298704238734708993009920,
    D=128*|e(MU)|.

The data and counter therefore share precisely the same scale `2^(Dn)`.
The fixed physical tag frame has length one modulo beta-1, every variable
contribution has length zero there, and the input ends b with length
at least beta. The complete four-tile predicate needs only its nonempty
history branch.

The encoded-data difference is strictly positive. The prefix bcb of u
gives e(T_0)>e(T_1), and tau reverses the comparison once more, so their
composition preserves order on physical binary cells. V1 first differs
from V0 by delta versus b; their four-bit codes preserve this order.
Thus `0<val(e(DATA_0))<val(e(DATA_1))<2^D`. This proves positivity of
B_S; A_S,T_S,E_S are positive fixed-frame/repunit expressions. The
computed history input is consequently positive before native typing.

Apply the complete compressed arithmetic compiler at these fixed
D,beta,u, retaining its independent recoder and history geometries.
The existing safe product finalizer and three normalized strong norms
restore every raw comparison at a positive zero. The joined recoder
then supplies the actual duration and padded input; the paid loader
supplies the exact tag word above; the independent selected history
proves its actual halting. The fixed-halt theorem, finite clockwise
compilation and valid U9 program-slice theorem imply `x in S`.

Conversely, if `x in S`, choose a sufficiently large dyadic n>E_S.
All finite simulations halt, and tag cleanup reaches singleton b.
The complete recoder and nonempty-history converses supply their
independent positive witnesses and the loader's positive repunit.
Canonical reconstruction changes only fifteen auxiliary coordinates,
preserving the input, duration, boundary and independent history
checksum. It produces a zero of the normalized polynomial.

Thus one fixed integer polynomial F satisfies, for every such S,

    x in S iff there exist y_1,...,y_69>0 such that
    F(x,A_S,B_S,T_S,E_S,y_1,...,y_69)=0.

The four effective program values are fixed per r.e. set, not additional
existential witnesses. Malformed positive parameter tuples need not
encode programs. No such assertion is needed for universality.

## 4. The exact exponent chain and actual source counts

D has106 bits and50 set bits. Its binary schedule would use154
multiplications. The metadata source supplies127 strictly increasing
exponent triples; each exponent is the sum of two earlier ones, starting
at1. Its structure is

    D=2^8 *5*37458297889612686511491400789,

with116 multiplications for the large factor, three for multiplication
of the exponent by5 and eight final doublings. The inherited chain
checker also verifies that every paid node is an ancestor of D.
Induction proves `Q=q^D` for every integer q without any division.
The list is explicit and verified, not asserted shortest.

The source calls the reviewed `rewrite_raw` with the actual U9 width and
this chain. It checks the complete binary-power prefix and every private
consumer before replacing it. It aliases the old program-bound operand
to E, then applies both unit transformations to the actual new raw DAG.
All existing critical-register guards pass. No U15 width, source ledger
or coefficient value is reused as a U9 value.

For each of the three finalizers, the resulting polynomial is exactly
the corresponding compressed U9 polynomial after the substitution
`program_bound=program_E`. This follows over the integers by exponent
induction and substitution through the retained DAG, even away from its
zeros. Only the same-input existence theorem in Sections2–3 uses the
positive domains and the possibility of longer padding; it does not
claim a bijection with every old witness tuple at a smaller bound.

| Form | Certificate operations | Comparisons | Positive witnesses | Polynomial operations |
|---|---:|---:|---:|---:|
| raw SOS |435|56|88|602|
| native units |444|28|69|527|
| three normalized strong witnesses |450|25|69|**524**|

The normalized splits are293M+157A for the certificate and318M+206A
for the polynomial. The optional five-parameter interface has exactly
the same arithmetic counts. The source derives all counts directly;
it does not call the U15 ledger with its hardcoded D and131-chain cost.

The degree propagation on this actual DAG gives the same general bounds
`132D+412`, `342D+1042`, `544D+1660` for the three forms. The last is
26082961986495105871681692197398140. It includes all four degree-one
program coordinates, the supplied positive witnesses and the ordinary
input. The main-norm cancellation uses the existing guarded source
identity. No expanded leading coefficient is evaluated, and the stated
bounds are not promoted to exact degrees.

## 5. Executable evidence and scope

The receipt contains the actual machine and sparse-table metadata, all
fixed-numeral definitions, the complete127-step chain and524-gate source,
and all six ledgers covering three finalizers and two program interfaces.
Ninety-six modular bases independently check every chain node, including
negative and zero bases and composite moduli. The complete old/new DAGs
agree on768 assignments,384 signed, with every fixed Numeral assigned
one consistent residue. Every shared register and final output is
compared. These checks supplement the integer exponent proof.

The source independently addresses actual production tracks by their
forward definitions and compares those letters with the imported
random-access routine. It also checks96 exact sentinel/counter bounds
without constructing a word of length n or the integer2^n. The metadata
packet separately checks actual published U9 frames and simulations,
including its excluded singleton escape. None of these cases is claimed
to be a materialized astronomical Pell zero or an expanded universal
production.

```sh
python3 neary_woods_universal_u9_tag_chain.py
```

Author writer and fresh-default replay passed. Root's independent full
proof/source review and fresh replay passed without findings. Substrates'
independent full proof/source review and fresh replay also passed without
findings. Its separate literal integer executor checked288 exact complete
DAG/output identities across all three forms and both bound interfaces,
with q in {-1,0,1} and arbitrary signed fixed-Numeral values; every shared
register agreed. The underlying U9 metadata and valid-input theorem also
completed independent root and Native_controller proof/source/default
reviews before this universal application was frozen.
