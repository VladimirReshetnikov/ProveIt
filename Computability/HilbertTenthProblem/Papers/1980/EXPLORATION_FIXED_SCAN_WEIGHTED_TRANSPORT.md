# Shared weights inside complete fixed-space scan blocks

This conditional lemma simplifies the weighted transport of the
[fixed-space raw queue](EXPLORATION_FIXED_SPACE_RAW_QUEUE.md). Within a
block of complete legal work-machine scans, each weighted append-coordinate
word is one common scalar times its unweighted append-coordinate word.
The two length words are also determined by that scalar and the first-cell
and delimiter markers. The length transport equation then follows from
the ordinary row-head geometry and one marker boundary identity.

This is a statement about synchronized, complete scan blocks. It does not
replace the weighted fields of the entire raw queue run, and it does not
provide a controller or a complete arithmetic history certificate.

## 1. Exact phase assumptions and packed words

Fix ell>=1, L0=3^ell, and put

    b=2ell+2,  w=3L0^2,  Wfull=3w.

A work scan begins and ends with b queue symbols: 2ell+1 tape cells and #.
The initial tape has exactly one marked cell. Take m consecutive complete
legal scans, with no loader steps, drain steps, reject-loop steps, boundary
overflow or unfinished scan inside the block. A legal scan may enter an
accepting or rejecting work state at its final delimiter; such a scan can
be the last scan of the block. Let h=mb be the number of queue transitions.
Number them from 0 to h-1. Empty blocks m=0 are allowed separately.

Use radix R, for example the verified R=243L0^2, and define

    q=R^h,       H=sum_(j<h) R^j,
    First=sum_(k<m) R^(kb),
    Last=sum_(k<m) R^(kb+b-1).

First and Last refer to the first tape cell and delimiter of the SAME
scans, respectively. They are not independent masks whose meaning is
assumed after the fact.

At queue transition j, let N_ij be content coordinate i, d_ij its head
trit, U_ij the coordinate value of the appended word, a_j its symbol length,
and W_j the source queue length marker. Write

    X_i=sum N_ij R^j,   D_i=sum d_ij R^j,   A_i=sum U_ij R^j,
    Weighted_i=sum U_ij W_j R^j,
    Z=sum W_j R^j,      T=sum 3^(a_j) W_j R^j.               (1)

Let I_i and F_i be the content coordinates before and after the whole
block. Its initial and final length markers are both 3w. Neither endpoint
is required to be zero. All these are conditional nonnegative words; no
positive-variable adapters are implicit.

## 2. A first-cell exception with zero append value

Every complete legal scan has exactly the following shape:

| Source step | Source length marker | Append length |
|---|---:|---:|
| First tape cell | 3w | 0 |
| Other tape cells | w | 1 |
| Delimiter | w | 2 |

At the first tape cell the one-cell-delay control has no predecessor, so
it appends nothing. A legal left move cannot occur there; it would be a
boundary rejection excluded by the hypotheses. All other data transitions
emit one held predecessor. The delimiter emits the held final cell and #.

Consequently U_ij=0 at every first-cell step. Multiplying that zero by 3w
or by w gives the same result. At every other step the source length is
already w. Coefficient by coefficient, therefore,

    Weighted_0=w A_0,  Weighted_1=w A_1.                       (2)

The other two coefficient identities are

    Z=w(H+2 First),       T=3w(H+2 Last).                      (3)

For T, a first-cell step has 3^0*3w=3w; an ordinary data step has 3^1*w=3w;
and a delimiter has 3^2*w=9w. This proves (3) without multiplying arbitrary
packed words to simulate a coefficientwise product.

Given the scalar w and the five unweighted words A0,A1,H,First,Last, the
following straight-line schedule materializes all four words in (2)-(3):

| Register | Operation |
|---|---|
| Weighted0 | w*A0 |
| Weighted1 | w*A1 |
| first_twice | First+First |
| zbase | H+first_twice |
| Z | w*zbase |
| last_twice | Last+Last |
| tbase | H+last_twice |
| full_length | 3*w |
| T | full_length*tbase |

This is exactly nine operations, five multiplications and four additions.
It is a materialization subtotal, with its inputs already supplied in the
stated roles. Constructing w=3L0^2 costs one more multiplication if L0^2 is
already available from the fixed-space initialization; it is not hidden in
the nine. No assertion is made that nine is an optimal schedule or that
these supplied words have been certified at zero cost.

## 3. Content transport with arbitrary block endpoints

The scalar queue identities are

    3N_i,(j+1)=N_ij-d_ij+U_ij W_j,
    3W_(j+1)=3^(a_j) W_j.

Multiply each by R^j and sum. The shifted content sum is
(X_i-I_i+qF_i)/R. Hence the two exact packed content equations after (2) are

    R(X_i-D_i+w A_i)=3(X_i-I_i+qF_i),   i=0,1.                (4)

The term qF_i is essential: unlike an accepting drain history, this block
ends with the full tape and delimiter. Dropping it would be a different
endpoint contract. The source checker verifies the off-shell correction

    old_content_i-new_content_i=R(Weighted_i-w A_i).

Thus (4) is exactly the original telescoped source under (2).

The corresponding length residual is

    Length=R T-3(Z-3w+3wq).                                  (5)

Define two independent polynomial residuals

    Geometry=(R-1)H-(q-1),
    Boundary=R Last-First-(q-1).

Substitution of (3) gives the exact polynomial identity

    Length=3w(Geometry+2 Boundary).                           (6)

Every actual complete block has Geometry=0. Also

    R Last=First+q-1:                                        (7)

multiplying each delimiter marker by R moves it to the next scan's first
row; all interior first markers cancel, leaving the final endpoint q and
removing the initial endpoint 1. Equivalently, (7) follows by summing the
geometric progression of complete scans. This proves the length transport
from the two synchronized marker/geometry equations.

Conversely, after (3), w>0 and Geometry=0 make Length=0 equivalent to
Boundary=0. This equivalence concerns those equations, not the realization
of actual scans. Formula (6) also holds for m=0: all packed words and
markers vanish, q=1, and I_i=F_i.

## 4. What synchronization still has to establish

The boundary equation alone does not specify complete scans of length b.
For example, with h=4 and any R>=3, the Boolean marker words

    First=1+R,   Last=1+R^3

satisfy (7). They describe consecutive intervals of lengths one and three,
not a single four-step interval. A future controller certificate must tie
First to the actual empty-predecessor scan state and Last to its actual
delimiter, and ensure that the same fixed tape interval is traversed in
every pass. Independently certifying both words as Boolean would not do
this. The unweighted append coordinates A_i and head words D_i must also
come from those same table rows and valid seven-symbol alphabet pairs.

The shared factor in (2) must not be extended over the raw loader. A concrete
example is x=2, ell=1. The initial queue is plain2,#, with source length
marker 9. Its first output is marked1,plain0, so its first append-coordinate
value is 1. The weighted value is 9, whereas w*A would give w=27. The source
checker includes actual loader examples of this failure. Drain steps have
zero append values but varying source lengths, so the length formulas (3)
do not apply to them either.

Partial scans likewise have different endpoints and marker corrections.
Splitting a full computation into loading, complete scans and draining
requires verified phase order and matching coordinate endpoints. Those
obligations, all power/row geometry, all positive adapters and any complete
cost remain outside this conditional result. In particular, eliminating
(5) through (6) is only useful once (3), Geometry and Boundary have actually
been established by the surrounding certificate.

## 5. Executable evidence

`../verification/explore_fixed_scan_weighted_transport.py` checks the nine
actual arithmetic instructions, both independent content source corrections
and the complete polynomial identity (6). It then imports the frozen bounded
queue compiler and constructs scan blocks from actual runs, including the
normalizer. Each row records both content coordinates, both head trits, both
append values, source length, output length and the exact first/delimiter
control events. No weighted word is assumed to be an ordinary product.

The author receipt has 72 runs and 288 tested blocks, including 72 empty
blocks. The underlying runs supply 1,230 complete scans and 7,722 distinct
queue rows; overlapping prefix/suffix/full blocks check 10,314 rows. Every
block verifies (2)-(7), both endpoints, the constant scan length and the
phase table. It also checks 216 deliberately altered first-marker words,
48 actual loader failures of the common-weight formula and three examples
where the boundary equation holds without the claimed scan lengths.

The largest tested time power has 5,580 bits. The exact finite checks support
the general coefficient and telescoping proofs; they do not establish an
arbitrary-witness controller or any full universal bound. Author and
independent root/binary_encoding complete proof/source audits and fresh
checker runs PASS, with no findings. Review metadata alone was added after
those runs. The three files are frozen for publication, which is separate.
