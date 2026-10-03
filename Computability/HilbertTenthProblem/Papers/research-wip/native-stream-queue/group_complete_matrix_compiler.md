# A complete generic matrix-membership arithmetic compiler

For a supplied fixed finite macro table, the signed-shear matrix route
now has a complete positive Diophantine certificate. Its ordinary input
is the positive integer x. For fixed positive compiler numerals alpha
and beta, put r=alpha*x+beta and

    L_r = [[1+r, 1], [-r^2, 1-r]].

The certificate is solvable exactly when a word in the fixed macro
language has matrix product `diag(L_r,L_r)`. When the macro codes include
each subgroup generator and its inverse, this is exactly membership in
that fixed subgroup of `SL2(Z) x SL2(Z)`.

For the padded table parameters m,h,p defined below, its literal cost is

    7m+3h+p+273 = (3m+2h+128)M + (4m+h+p+145)A,

with **60 equations** and **m+87 strictly positive existential
witnesses**. Its literal single sum-of-squares polynomial costs

    7m+3h+p+452 = (3m+2h+188)M + (4m+h+p+264)A.

The polynomial has exact total degree **max(112,12m+16)** in x and
the supplied existential coordinates, with all compiler numerals fixed.

No geometry, Boolean selector, selected-source product, state-range,
controller or endpoint condition remains external to this composition.
The numerically instantiated universal subgroup alphabet is not supplied
here. These are exact compiler formulas in the size of a given table,
not a new numerical universal bound or an improvement on88 operations.

## 1. Fixed data, supplied coordinates and literal aliases

Each nonidentity physical letter is one of the eight signed unit shears
on a chosen coordinate of two two-dimensional vectors. Letter0 is the
identity. A code is a nonempty word over letters1,...,8. Retain the
action convention of the [four-register packet](group_four_register_history.md):
successive letters multiply on the left, so the product of a physical
word `s_0,...,s_(t-1)` is `s_(t-1)...s_0`.

Construct the hub-to-hub table for

    (0 | code_1 | ... | code_k)*

as in the [paid regular controller](group_regular_macro_controller.md).
Remove empty identity codes, retain the hub identity loop, and duplicate
that loop to make the edge count m=2^h>=2. Interior vertices have distinct
fixed codes below m. For the number k_i of edges carrying physical
letter i+1, define the fixed projection cost

    p=sum_(i:k_i>=2) k_i <=m.

The table, all vertex codes and their sums, alpha and beta are fixed
integer compiler data. Their runtime multiplications remain charged.
Only x is a supplied relation argument; it is never replaced by a word
encoding. Everything else supplied to the circuit is a positive
existential coordinate.

The24 shared coordinates are

    q_geom, P, J, history_bound,
    H0,H1,H2,H3,
    Shat0,...,Shat7, Zhat0,...,Zhat7.

The history source computes `D=q_geom^2` and `B=8D`; B is not an extra
supplied coordinate or an extra comparison. The four component interfaces
are joined by these exact aliases:

| Component | Local interface | Global interface |
|---|---|---|
| Canonical history47 | q,P,H_i | q_geom,P,H_i |
| Canonical history47 | S_i+,S_i-,Z_i+,Z_i- | Shat_(2i),Shat_(2i+1),Zhat_(2i),Zhat_(2i+1) |
| Prescribed exclusive batch119 | B,P,history_i | B,P,H_i |
| Prescribed exclusive batch119 | Shat_i,Zhat_i | Shat_i,Zhat_i |
| Regular macro controller | B,P,J,Shat_i | B,P,J,Shat_i |
| Linked geometry47 | q,B,J | q_geom,B,J |

Every other register and auxiliary is prefixed by its component name.
In particular the selection kernel scale and the controller subset-kernel
scale are distinct computed integers; neither is identified with q_geom.
The three Pell cores have completely disjoint supplied coordinates.
Computed differences and endpoints can be signed away from zeros.

The [source](group_complete_matrix_compiler.py) performs literal name
substitution in the four reviewed schedules, preserving every gate and
comparison. It places the history schedule first, so its computed B is
available before the other blocks. This evaluation order does not impose
an order on the soundness arguments below.

## 2. The four paid blocks and their geometry dependency

Include precisely the following sources:

1. [Canonical history47](group_four_register_canonical_history47.md),
   including the positive scalar bound
   `H0+H1+H2+H3+history_bound=P` and the ordinary affine input loader.
2. The **prescribed-scale exclusive119** source of
   [shared-checksum selection](native_binary_masked_selection63.md).
   It retains its own paid kernel scale `16P^8` and the scalar bound
   `sum_i Zhat_i+selection_bound=P+1`.
3. The complete [regular macro controller](group_regular_macro_controller.md),
   including its subset kernel, paid radix margin, repunit equation,
   hatted edge checksum, state adjacency and eight selector ports.
4. The **shared-B47** version of
   [linked binary geometry](group_linked_binary_geometry47.md).
   Its native index is the shared J, its scale is q_geom, and its paid
   bound is `B+index_beta=J`. Its other two added conditions make its
   odd quotient strict and give `J+bound_beta=X_geometry`.

The geometry component proves, using only B=8q_geom^2 and its own
positive equations,

    J>B, J odd, q_geom=2^popcount(J).                  (1)

It does not first assume that B or P is dyadic. This is the essential
bootstrap: (1) makes q_geom a power of two, and the computed B is
therefore a power of two as well.

Independently, the prescribed selection source's complete scalar
projection makes P a power of two. Invoking this scalar projection
does not require any cellwise interpretation of the histories or
selectors. Its whole input concatenations are nonnegative from the
declared positive hats and histories. Its computed fourth truth field
is at least8, so its native positive domain is valid. All power typing
has now been paid, before any controller digit theorem is used.

The controller's repunit comparison is

    (B-1)J+1=P.                                       (2)

Because B and P are powers of two and J is positive, (2) implies, for
an integer t>=1,

    P=B^t, J=1+B+...+B^(t-1).

For example, reduce the exponent of P modulo the positive exponent
of B in divisibility `B-1 | P-1`; the smaller remainder `2^r-1` must
vanish. Distinct powers of the dyadic B have distinct binary positions,
so `popcount(J)=t`. Condition J>B excludes t=1. Thus the composed
equations recover the full linked geometry

    t>=2, q_geom=2^t, B=8*4^t, P=B^t.                 (3)

This order avoids using a duration to establish the same duration's
height bound. In particular the imported selection and controller
Pell scales do not determine the matrix duration by an unproved alias.

## 3. Soundness after recovering the geometry

The controller's positive margin gives B>m. Its complete theorem now
applies with both dyadic parameters established. It proves that the
eight values `S_i=Shat_i-1` are Boolean radix-B words of the common
length t, with at most one active letter per position, and that their
physical word follows a hub-to-hub path in the actual fixed table.
All-zero physical selectors represent its identity step. The state
flow equation enforces chronological adjacency and both endpoints;
it does not merely balance counts of edges.

The history scalar comparison gives `0<H_i<P`. Hence the proposed
histories have unique canonical length-t radix-B expansions with
digits in `{0,...,B-1}`. These digits need not yet be positive or small.
At this stage the selection source's paid output bound gives

    sum_i (Zhat_i-1)<=P-8,

so every output lane is below P. Its complete binary AND relation,
together with the now established dyadic cell geometry, bounded
histories and Boolean selectors, proves the exact digitwise products

    Z_i=sum_j s_i(j) X_(floor(i/2) xor 1)(j) B^j.       (4)

This soundness direction requires no half-radix history margin. Such a
margin is a completeness condition for the single output bound and
will be obtained from actual histories below. There is consequently
no circular use of a state-range conclusion to justify (4).

All hypotheses of canonical history47 are now established, including
q_geom>=2^t and t>=2. Its simultaneous first-mismatch induction recovers
every candidate history digit as the actual shifted vector coordinate
under the physical shear word. The actual bound is

    0<X_i(j)<2q_geom^2=B/4,

also at the terminal position. The four recurrence equations then
force both final vectors to be `L_r(q_geom,1)`. Even if a computed
endpoint was signed on arbitrary inputs, it is positive after its
shift on this zero set.

The one-vector lemma recovers the entire final matrix of each block:
every product entry has absolute value at most2^(t-1)=q_geom/2;
the action on `(q_geom,1)` first fixes the top-right entry to1 and
top-left entry to1+r, and determinant one fixes the second row.
The fixed regular controller has already enforced the macro language.
Thus the circuit's positive zero represents precisely the claimed
macro product `diag(L_r,L_r)`.

## 4. Strictly positive completeness for every accepted input

Conversely suppose some word in the fixed macro language has product
`diag(L_r,L_r)` for the given ordinary x. Choose an edge parse. Append
hub identity steps until its duration t satisfies

    t>=2 and 8*4^t>m.

This is always possible for a fixed finite table and preserves the
matrix product. Set q_geom=2^t, B=8q_geom^2, P=B^t and J to the
length-t radix-B repunit. Then J>B and (1)--(3) hold. The linked
geometry theorem supplies all19 of its strictly positive auxiliary
coordinates at exactly this q_geom and J.

Follow the actual word from `(q_geom,1,q_geom,1)` and shift each
coordinate by D=q_geom^2. Its positive values lie below B/4. Pack
them to obtain H_i, and pack the actual physical selectors and selected
source digits to obtain Shat and Zhat. Every whole history is positive
because its initial digit is positive, while all hats are positive
even for entirely unused letters.

At each position, the sum of the four genuine state digits is less
than B. Therefore `sum_i H_i<P`, making
`history_bound=P-sum_i H_i` strictly positive. At most one of the eight
physical selectors is active at a position, and its selected digit is
less than B/4. In particular `sum_i Z_i<P/2`. Since P>=16, the
exclusive selection witness

    selection_bound=P-sum_i Z_i-7

is strictly positive. The prescribed119 theorem supplies its entire
positive Pell extension at the actual scale16P^8; no letter is
required to occur. All four history equations hold by telescoping.

The chosen edge parse supplies each hatted edge indicator, including
positive hats for every unused edge. Set its radix margin to B-m>0.
The regular-controller converse supplies its positive subset partition
and full native kernel extension. The geometry, selection and controller
core coordinates are disjoint, so these three positive extensions can
be chosen simultaneously without changing any shared interface value.
Every comparison in the composed source is now satisfied.

This converse is parametric for arbitrarily long words. None of its
Pell extensions is inferred from a finite fixture or restricted to
a particular choice of canonical auxiliary coordinates in another
component.

## 5. Exact operation, comparison and witness counts

The composition introduces no additional gate: all shared aliases are
literal source substitution, and B is computed exactly once.

| Block | M | A | Equations | Additional positive coordinates |
|---|---:|---:|---:|---:|
| Canonical history, including ordinary loader |15|32|5|24 shared coordinates, including J |
| Prescribed exclusive selection |57|62|17|23 |
| Regular macro controller |3m+2h+30|4m+h+p+30|25|m+21, excluding shared J |
| Shared-B linked geometry |26|21|13|19 |
| **Total** | **3m+2h+128** | **4m+h+p+145** | **60** | **m+87** |

The shared count includes q_geom,P,J and the21 positive history fields;
it does not include computed B or D. The selection count is its22
positive AND auxiliaries plus its global bound witness. The controller
count is its original m+22 auxiliaries with shared J counted only once.
The geometry's original native index r is J, so its19-coordinate list
contains no additional index witness. The sole ordinary relation input
x is excluded from these existential counts.

The source separately constructs all60 residual subtractions,60 squares
and59 summation additions. This adds60M+119A=179 operations and yields
one integer polynomial. Over the stated positive integer domain its
zeros are exactly the solutions of the60 comparisons. Constants0 and1
used by the source are fixed numerals; every multiplication by a
numeral and every square is included in the ledger.

These counts are for the displayed straightforward composition. They
are neither an optimum over equivalent circuits nor a claim that the
three native kernels cannot share further arithmetic.

Its degree is exact as well. Direct degree propagation through the
actual DAG bounds the history residuals by5 and the linked-geometry
residuals by14. The selection block has a unique highest residual of
degree56, its first Pell norm. Its highest form is

    w_selection^2*s_selection^4*k_selection^2*(16P^8)^6.

The controller's computed scale has highest form `8J*P^(m-1)`, of
degree m. Its unique highest residual, again its first Pell norm, has
degree6m+8 and highest form

    w_controller^2*s_controller^4*k_controller^2
      *(8J*P^(m-1))^6.

Every other residual has smaller degree than the larger of these two.
The complete SOS therefore has exact degree max(112,12m+16): its
highest form is the square of the selection expression for m<8, the
square of the controller expression for m>8, and their sum for m=8.
These nonzero squares cannot cancel. In this degree calculation all
supplied coordinates, including P,J and each kernel's independent
auxiliary index, retain degree one. No equation on the zero set is
substituted into a polynomial to assign it an artificially lower degree.

## 6. Relation to the fixed universal subgroup theorem

The [group-commutator construction](group_commutator_universal_substrate.md)
provides an effective fixed finitely generated subgroup for a fixed
universal c.e. set. Its program parameter affects only two fixed
positive numerals in r=alpha*x+beta. Each of its fixed integral matrix
generators and inverses admits a finite signed-unit-shear code by the
Euclidean construction already proved in the four-register packet.
Applying this compiler to that finite list gives a complete universal
positive Diophantine representation with the ordinary input x.

The present artifact therefore closes the mathematical and arithmetic
interfaces of that route. It does not transcribe the universal group's
finite presentation, compute its particular matrix alphabet, or report
that alphabet's m,h,p. The exact operation and witness formulas become
numerical only after that fixed table is supplied. The small tables in
the receipt are audits of the compiler, with no universality assertion.

## 7. Executable audit and its limits

The [receipt](group_complete_matrix_compiler.json) contains actual full
DAGs, comparison lists, positive coordinate lists, alias maps and
component boundaries for three fixed tables, including the all-idle
table. Each source checks topological availability and uniqueness of
every computed register. In total768 arbitrary assignments, including
192 signed off-zero cases, compare all60 residuals with independently
expanded component formulas and verify the complete sum of squares.
The exact generic ledgers are asserted for every generated table.
Additional weighted and offset polynomial evaluations at m=2,4,8,16
verify the complete output degree and highest coefficient, including
the two-component tie at m=8, against the propagated DAG bounds.

Four additional target-word fixtures use a fixed generator code and
its inverse, with identity padding and cancellation pairs. They build
the shared positive histories, selectors, selected fields, edge parse,
repunit and scale values and verify every common outer interface.
Their three Pell cores contain explicit placeholders: these fixtures
are not advertised as full zeros. The existence of the full strictly
positive core extensions is the uniform theorem used in Section4.

Run the checker without arguments to compare the deterministic receipt;
`--write` regenerates it. No unbounded subgroup-membership decision
procedure is inferred from these finite checks.

Three independent full proof/source/default reviews passed without
findings. They checked the geometry-first dependency order, positive
computed subset fields, canonical lane decoding, simultaneous history
recovery and endpoint faithfulness, and the three independent positive
Pell extensions. They also verified every alias, the m+87 witness count,
all 60 comparisons, both operation ledgers and the exact degree scope.
One review separately replayed the four original component sources on
512 random-table assignments, including 128 signed assignments, matching
all 2,048 component register sets and the full residual lists. Another
checked 384 assignments across 12 separately generated macro tables with
independently written interface maps. Independent weighted degree checks
at m=2,8,16 recovered the stated leading forms, including both
contributions at m=8. These identity audits retain the explicit
distinction between positive outer fixtures and complete Pell zeros.
