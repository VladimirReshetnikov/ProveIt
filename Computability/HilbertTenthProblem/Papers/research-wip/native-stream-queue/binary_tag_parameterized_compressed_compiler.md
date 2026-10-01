# A complete tag compiler with compressed fixed numerals and program parameters

For a fixed binary tag system satisfying the hypotheses below, this
compiler costs **397+mu(D)** polynomial operations, uses **69 positive
existential witnesses**, and has five positive program parameters besides
the ordinary positive input x. Here
`mu(D)=floor(log2 D)+popcount(D)-1`. The total polynomial degree is at
most **544D+1660**. A numerical universal machine application is a separate
obligation; this packet supplies its complete arithmetic interface.

The [source](binary_tag_parameterized_compressed_compiler.py) and
[receipt](binary_tag_parameterized_compressed_compiler.json) contain the
actual finite gate schedule. Huge fixed integers are named numeral atoms
with exact definitions. They are degree-zero constants, not extra
variables, exponentiation gates, or oracles depending on x or witnesses.
All multiplications by them remain charged. This representation avoids
allocating integers with more than D bits when D itself is enormous.

## 1. Exact family represented

Fix beta>=2 and a production u over b,c, ending in b, with
`|u|=1 mod(beta-1)`. Put `e(b)=10^beta1`, `e(c)=1`, and

    L = |e(u)|-beta+1,
    d = val(1 e(u without its last b) 10).

Require L>=beta+3 and D>=3. The four affine tile maps are exactly

    (2, 1, 2^L, d),
    (2^(beta+2), 2^(beta+1)+1, 8, 6),
    (2^(beta+2), 2^(beta+1)+1, 2, 0),
    (2, 1, 2, 0).

Use the [complete fixed-word-family theorem](binary_tag_complete_dyadic_compiler.md)
with a program-dependent fixed PREFIX and MIDDLE and fixed DATA0, DATA1,
MU, TAIL. Each program slice must satisfy that theorem's equal-content,
width, congruence and final-b conditions. In particular D=m|e(MU)| and
both data blocks have encoded width D. Require strict positive data
ordering, so the loader coefficient B is positive.

For this program's binary block constants, compute A,B,T,E by the
[shared-counter loader formulas](binary_tag_shared_counter_loader.md).
Take a positive bound N. Specialize the five program parameters to

    program_A=A, program_B=B, program_T=T, program_E=E, program_bound=N.

The polynomial has a positive zero exactly when there is a dyadic n>N
with x<2^n for which the tag system halts on

    PREFIX DATA_w1 ... DATA_wn MIDDLE MU^(m*n) TAIL,
    where w=bin_n(x).

This statement is about each valid program slice. Arbitrary positive
parameter choices still define a polynomial predicate; no claim is made
that every such tuple encodes a machine. A universal representation only
needs an effective valid tuple for every recursively enumerable set.

## 2. The bound costs one addition

Replace the recoder's positive duration coordinate everywhere by

    program_duration_bound = program_bound + program_duration_gap,

where the gap is a new positive coordinate replacing the old duration.
This adds one gate and no comparison or witness. Positivity holds before
any native typing. At any old zero with n>N the inverse is gap=n-N>0;
every new positive tuple restores a positive old duration. Thus this is
an exact positive-coordinate projection, not an uncharged inequality.

The computed history input is

    Vi=(program_A*r+program_B*z)*Q+program_T*r+program_E,
    (2^D-1)*r=Q-1.

It is positive on every positive tuple. The four coefficient ports
replace fixed literal operands in existing gates, so they add no gates.
The dyadic recoder, exact word loader, nonempty tile-history theorem and
independent input/history durations therefore compose exactly as in the
parent theorem. Requiring n>N does not affect universality for a machine
whose interpretation is invariant under arbitrarily long zero padding.

The raw SOS version is complete. Its three native-unit projections and
three strong-witness normalizations retain the same zero projection:
the source checks all literal native prerequisites and the dependency
audit for the fifteen reconstructed auxiliary fields. The duration sum
and all coefficient parameters are independent of those fields. The
history checksum remains a separate comparison, and the unit product
contains only one unrestricted checksum.

## 3. A literal history without expanding u

Fix the slope-class history with baseline2 on both coordinates. Its
upper exceptional group is tiles1,2; its lower exceptional groups are
tile0 and tile1. Thus there are three selected products and scale
exponent11. No search over gigantic coefficients is needed.

Write t=2^beta and R=2^L. The grouped transport schedule computes

    nextU = 2HU+(4t-2)ZUhat+(2t+1)(S1hat+S2hat)
            +S0hat+S3hat-(8t+2),
    nextV = 2HV+(R-2)ZV0hat+d*S0hat
            +6(S1hat+ZV1hat)-(R+d+10).

Subtracting1 from every selector/selected-product hat gives precisely
the four affine maps above. These are polynomial identities in t,R,d
and the history variables; the receipt checks both symbolically.
They justify the seven audited fixed-operand replacements in the
existing 161-gate history schedule. The rest of that history is literal
and unchanged, including every range, selection, product and native gate.

Since the lower tile word has length L and starts in1,
`2^(L-1)<=d<2^L`. Its final10 in fact gives d<=2^L-2.
The sufficient history radix is exactly `K=2^(L+1)`: it exceeds every
affine slope-plus-offset and the fixed tile-count bound. For the upper
map, `2^(beta+2)+2^(beta+1)+1<2^(L+1)` follows from L>=beta+3.
The lower large map gives `1+2^L+d<=2^(L+1)-1`. Consequently this fixed
dyadic radix satisfies the complete history theorem, even without
executing the old numerical coefficient planner.

The eleven named fixed numerals are:

| Role | Exact integer |
|---|---|
| recoder radix | 2^(D-1) |
| loader repunit divisor | 2^D-1 |
| terminal scale and offset | 2^(beta+1), 2^beta |
| history radix | 2^(L+1) |
| upper and lower slope differences | 2^(beta+2)-2, 2^L-2 |
| production offset | val(1 e(u without its last b) 10) |
| upper tile offset | 2^(beta+1)+1 |
| upper transport constant | 2^(beta+3)+2 |
| lower transport constant | 2^L+d+10 |

An application must define the fixed word u effectively, for example by
a finite machine table and interleaved-track construction. Its enormous
integer d is then an exact fixed numeral. The receipt never hashes an
unmaterialized word as if it had been expanded; it hashes finite source
descriptions with named numeral operands.

## 4. Counts and degree bounds

Every returned ledger is counted from its actual topological source,
including the repeated-squaring chain for Q=q^D. The chain has exactly
mu(D) multiplications. The resulting costs are:

| Form | Certificate operations | Comparisons | Positive witnesses | Polynomial operations |
|---|---:|---:|---:|---:|
| raw SOS | 308+mu(D) | 56 | 88 | 475+mu(D) |
| native units | 317+mu(D) | 28 | 69 | 400+mu(D) |
| normalized native units | 323+mu(D) | 25 | 69 | 397+mu(D) |

There are six free positive coordinates including x. For the normalized
polynomial, the multiplication/addition split is
`(191+mu(D))M+206A`. Constant definitions are external descriptions of
fixed numerals in the stipulated arithmetic model; their uses in the
polynomial are charged in the table.

The coefficient parameters have degree1. Thus Vi has degree at most
D+2, the history length register has degree at most nu=D+3, and its
native scale has degree at most d0=11nu. The recoder's AND scale has
degree at most v=2D+2. Auditing the main-norm cancellation as a literal
polynomial identity gives degree bounds

    raw:        132D+412,
    units:      342D+1042,
    normalized: 544D+1660.

For the normalized form the unit degree bound is
`30+35v+2D+36d0-6nu+142`, and the maximum remaining residual degree
is bounded by `max(3v+D+1,4d0-3nu+1)`. Source propagation checks these
closed formulas. This packet deliberately claims bounds, not exact
degrees or a numerically evaluated leading coefficient for enormous D.

## 5. Validation and limits

The writer and fresh replay check two exact symbolic transport identities,
288 complete output identities against the independent literal compiler
(144 signed), twelve source ledgers, and24 literal valid-parameter input
frames. A separate exponent of110 bits exercises the full source and
its actual operation count without constructing 2^D. The final schedule
and every fixed-numeral definition are retained in the receipt.

These checks supplement the general positive-equivalence argument.
They do not materialize full native Pell zero tuples, prove a global
minimum, or supply Lean verification. A numerical universal bound must
also discharge the fixed-machine, actual-u, word-format and padding-bound
obligations above.

Independent final proof/source/fresh-receipt review passed. It checked
the K threshold, numeral domains, duration projection, positive program
ports and all three native interfaces. An additional216 complete
specialized residual/output identities (108 signed) covered beta5,6,8
with distinct bcb-prefixed productions;18 literal frames used bound3
and durations4 or8. No findings remained.
