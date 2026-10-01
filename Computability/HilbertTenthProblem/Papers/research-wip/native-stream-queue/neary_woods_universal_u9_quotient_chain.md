# A 519-operation U9 polynomial from an exact control quotient

The explicit U9 tag construction now uses **519=313M+206A polynomial
operations**,69 positive witnesses and four positive program parameters
besides the ordinary positive input. Its certificate has
**445=288M+157A operations and25 comparisons**. Its total degree is at most

    10022392728476764537286933476599420.

This improves the [524-operation U9 application](neary_woods_universal_u9_tag_chain.md)
by five multiplications and lowers its degree bound. The separate best
established universal polynomial bound remains
[87 operations](complete75_normalized_strong87.md).
The construction makes no minimum-machine, shortest-chain or exact-degree
claim.

The changes are an exact quotient of the binary machine's control states,
14 unreachable copying states and an explicit122-multiplication schedule
for the resulting fixed input width. Every cyclic-tag appendant and fixed
coefficient is rebuilt from that actual table. The
[source](neary_woods_universal_u9_quotient_chain.py) and
[receipt](neary_woods_universal_u9_quotient_chain.json) retain all3248
padded binary instructions and the complete519-gate polynomial source.

## 1. Exact control simulation before rebuilding the tag program

The [control-quotient theorem](binary_clockwise_control_quotient.md)
starts with the actual1968-state binary compiler for the published U9
machine. Of these states1814 are graph-reachable from the specified
interior start. Stable output/target partition refinement gives1611
classes, with start label1 and the distinguished accepting halt1611.
For every reachable original state and each read bit, its quotient row
writes the identical one- or two-bit word and enters the mapped target.
The accepting halt is a singleton class.

Thus the complete circular tape and head cut agree after every actual
binary step, not just at simulated macro boundaries. Halting agrees in
both directions on every nonempty circular tape. This theorem does not
use or change the original physical block code or input program frame.
The quotient has64 two-cell instructions.

Now let `h0=1611` and `h=1625`. Define the label injection

    ell(q)=q for q<h0, ell(h0)=h.

For each quotient row `(q,b)->(w,t)`, retain the row with target ell(t).
For every j from1611 through1624 add the two rows

    (j,0)->(0,j), (j,1)->(1,j).

These14 new states are total one-cell copying loops. No retained row
targets them, so none is reachable from start1. The only accepting state
is the relocated halt1625, which has no outgoing row. The source checks
all3220 retained rows, all28 added rows and the exact reachable set
`{1,...,1610,1625}`. It also checks that the two-cell count remains64.

An induction on actual transitions gives the same tape and head cut at
state ell(q), and q=h0 exactly when ell(q)=h. This proves a literal
step-preserving simulation of the quotient in the padded table, including
the final halting event. The unreachable loops introduce no new accepting
computation. Their purpose is to select a fixed tag width with a shorter
verified multiplication schedule; their definitions and effects are paid
through the rebuilt fixed table and coefficient uses below.

## 2. The actual new fixed constants and power schedule

Run the same complete sparse cyclic-tag assembler on all1625 states,
including the unreachable copying rows. Then build the fixed-halt tag
tracks from those actual appendants. The source does not merely substitute
Q into size estimates; it reconstructs every assigned appendant, checks
index collisions and records the exact sparse-table hash.

| Fixed quantity | Value |
|---|---:|
| Binary states Q |1625|
| Two-cell binary instructions |64|
| z=30Q+61 |48811|
| Cyclic-tag appendants p=2z |97622|
| Accepting activation index |48770|
| Deletion beta=10p |976220|
| Sum of appendant lengths |4462011274|
| Maximum appendant length |390528|
| Common track length s |4881096|
| b letters in u |3094234356470|
| c letters in u |1670789180650|
| Encoded length E_u |3020661322731036990|
| Encoded CTS-bit block length K |2948796769201942898733130|

The generic literal track rule still defines every letter of u, which
begins bcb, ends b and has length one modulo beta-1. The large offset
`val(1 e(u without its last b) 10)` and all other fixed-numeral operands
therefore have exact finite recipes for this new table. No expanded u
or integer with D bits is allocated.

The U9 physical input still has64 binary cells per ordinary bit, so

    D=128zK=18423516044994052458248039479040
     =2^8 *21653*1729*1922292548371540351195.

The source lists122 strictly increasing triples `(e,a,b)` with e=a+b
and both a,b already available from the initial exponent1. Every paid
node is an ancestor of the final D. Emit one multiplication per triple;
induction gives exactly q^D for every integer q. All exponent additions
and the final target are checked. This schedule was found by a bounded
factor/window search; it is not claimed shortest.

Both machine transformations preserve actual binary steps, but the fixed
cyclic-tag system and its enormous numeral values differ from those of
the524 parent. We therefore rebuild those coefficients instead of claiming
that the old and new universal polynomials are identical.

## 3. The ordinary-input and positive-program contracts

The original [U9 input-format theorem](neary_woods_u9_tag_metadata.md)
is unchanged. For each positive r.e. set S, choose its represented
recognizer on pairs `(3,1)` for zero and `(1,3)` for one, with leading
zero padding ignored. In the original physical code

    A_i=b^(4i-1)delta, V_0=A_3 A_1, V_1=A_1 A_3.

The genuine clockwise/bi-tag slice has at least six A symbols at every
stage. The known singleton-A escape remains excluded. The physical
head cut is

    b^(4q_B) V_w1 ... V_wn A_r A_l RIGHT LEFT P_S.

The control quotient and padding do not modify this tape, its codes,
its actual head or its start state. Its binary length is still

    64n+b_S, b_S=4*(|P_S|+4*(q_B+r+l)+2)>0.

The new fixed tag blocks encode those same physical cells using the new
z,K,u. Their DATA width is128zK=D, while their MU width is zK.
Consequently the counter block repeated128n times has exactly the same
binary length Dn as the data. The fixed frame is one modulo beta-1,
all variable contributions are zero there, and the input ends b and has
length at least beta. The same nonempty four-tile history theorem applies.

The two input values have strict positive order. The new u still begins
bcb, so the fixed-halt block comparison and tau comparison reverse order
twice. The physical four-bit code and V_1>V_0 then imply
`val(e(DATA_1))>val(e(DATA_0))>0`. Thus the four program coefficients
A_S,B_S,T_S,E_S of the shared-counter loader are all positive, and its
computed history input is positive before native typing.

As in the524 application, E_S is the sentinel of the fixed encoded
PREFIX MIDDLE TAIL, with variable data and counter omitted. These fixed
blocks encode all b_S physical frame cells via nonempty words. Therefore
E_S>=b_S. The paid recoder duration is

    n=E_S+positive_gap.

Its dyadic-duration theorem gives n>=2 and n>E_S>=ceil(b_S/64).
Hence `64n<64n+b_S<128n`, and the exact minimal initialization counter
is128n. Arbitrarily long dyadic padding supplies such a duration for
every positive x. The program semantics are invariant under that padding.

At a positive polynomial zero the safe unit finalizer and three normalized
strong norms restore all raw native comparisons. The joined recoder,
exact boundary loader and independent selected history yield a genuine
halting tag computation. The fixed-halt bridge, padded-table simulation,
control quotient and original U9 program theorem imply `x in S`.
Conversely an accepted x has a sufficiently long dyadic padded spelling;
the same finite simulations and component converses supply all positive
witnesses. The fifteen-coordinate canonical auxiliary reconstruction
preserves every outer boundary and history checksum.

Thus one fixed integer polynomial F satisfies

    x in S iff there exist y_1,...,y_69>0 such that
    F(x,A_S,B_S,T_S,E_S,y_1,...,y_69)=0.

The four effective program coordinates are fixed per r.e. set, rather
than added existential witnesses. No program interpretation is asserted
for arbitrary malformed positive parameter tuples.

## 4. The literal arithmetic and degree audit

Instantiate the complete compressed compiler at the new D,beta,u.
Replace its old binary-power prefix by the122-step schedule only after
checking every private consumer and the public Q interface. Alias the
old duration-bound program coordinate to E. Apply the existing unit
and normalized-strong rewrites afresh to that actual raw source;
all critical consumer guards pass.

For the compressed compiler at these new fixed constants, each resulting
DAG is exactly the old polynomial after `program_bound=program_E`:
exponent induction and substitution prove this over arbitrary integers.
That identity is distinct from the same-language simulation between
machines and their different fixed coefficient recipes in Sections1–3.

| Form | Certificate operations | Comparisons | Positive witnesses | Polynomial operations |
|---|---:|---:|---:|---:|
| raw SOS |430|56|88|597|
| native units |439|28|69|522|
| three normalized strong witnesses |445|25|69|**519**|

The normalized polynomial is313M+206A, and its certificate is288M+157A.
The optional five-parameter interface has identical operation counts.
The actual DAG passes the inherited degree propagation, including the
guarded main-norm cancellation. Its upper bounds are `132D+412`,
`342D+1042` and `544D+1660`; the last is
10022392728476764537286933476599420. These include all free program
coordinates and remain upper bounds, not exact-degree claims.

## 5. Executable evidence

The receipt emits the complete3248-row padded binary table, the relocated
halt and unreachable labels, exact CTS/track metadata, all122 exponent
steps, six finalizer/interface ledgers and the519-gate polynomial DAG.
The padding proof is checked against every retained transition and
supplemented by384 actual circular-tape traces and explicit terminal-row
cases. The quotient packet independently checks the original-to-quotient
map and its complete moving-head simulation.

Ninety-six modular power cases independently verify every chain node,
including negative and zero bases and composite moduli. The full arithmetic
DAGs agree on768 assignments,384 signed, with one consistent residue for
each fixed Numeral. Every shared register and final output is checked.
Twenty-one exact counter-bound cases supplement the sentinel argument.
These are source and machine checks, not materialized native Pell zeros
or expanded universal words.

```sh
python3 neary_woods_universal_u9_quotient_chain.py
```

Author writer and fresh-default replay passed. Root's independent full
proof/source review and fresh replay passed without findings.
Native_controller's independent full proof/source/fresh-default review
also passed; its separate integer executor checked144 complete DAG/output
identities across all three forms and both bound interfaces, at q in
{-1,0,1} with signed coordinates and fixed-Numeral assignments. It also
independently checked every3248 padded transition row. Substrates completed
a further bounded source/prose review without findings and did not repeat
the already recorded replay. No complete numerical Pell zero is claimed
by any of these finite arithmetic checks.
