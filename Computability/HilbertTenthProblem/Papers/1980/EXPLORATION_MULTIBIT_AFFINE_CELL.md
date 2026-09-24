# A fixed-coefficient local compiler for multi-bit state cells

This note proves that the Boolean state bits at one site can be packed
into a single integer cell, and their separately weighted affine terms
can be extracted by **one fixed-coefficient product per neighboring
site**. The irrelevant cross terms are nonnegative and carry-free. A
mask tests only the desired coefficient block. Dummy bit positions
balance the two mask weights and cannot substitute for genuine state
bits.

The result is a local compiler lemma and a conditional aligned-word
composition lemma. It does not supply a power/size bootstrap, a cyclic
neighbor interface, positive transport quotients, a marked acceptance
condition, or a universal raw-input compiler. No improved complete
universal operation count is claimed. All constants depend on the fixed
finite relation and may be very large; fixed numerals have no construction
cost in the requested complexity measure.

The [checker](../verification/explore_multibit_affine_cell.py) imports the
[generic Boolean affine compiler](../verification/explore_boolean_affine_mask.py).
The [receipt](../verification/explore_multibit_affine_cell.json) records
exact finite checks of state bits, dummy bits, ordinary polynomial
coefficients, packed composition, mask weights, and parity.

## 1. Relation, clause padding, and positive coefficients

Fix `g>=1` sites and `k>=1` genuine state bits per site. Let

    Rlocal subset {0,1}^{gk}

be a fixed relation that excludes the all-zero tuple. The order of the
sites and state bits is fixed. Choose a power of two `A>=2` with
`A/2>gk-1`. List the forbidden tuples with zero last. If their number is
less than `k`, append enough repeated copies of the forbidden zero tuple
to make the list length `m>=k`. Repetition changes no truth condition.
The final forbidden tuple remains zero.

For forbidden tuples `p_0,...,p_(m-1)`, the generic compiler gives

    phi(z)=A^m+sum_{j=0}^{m-1} A^j (dist(z,p_j)-1)
          =c0+sum_{s=0}^{g-1} sum_{i=0}^{k-1} c_si z_si,
    mu=sum_{j=0}^{m-1} (A/2) A^j.                        (1)

Its standard least-negative-clause proof, unchanged by repetition,
establishes for Boolean inputs

    phi(z)>0,   phi(z) AND mu=0 iff z in Rlocal.          (2)

Each variable coefficient is positive because its contribution from the
last, zero tuple exceeds the absolute sum of all earlier contributions:

    c_si>=A^(m-1)-sum_{j<m-1} A^j>=1.

Also `c0>=A^m-sum_{j<m} A^j>=1`. The mask `mu` has exactly `m` set bits,
one in each clause digit. All these quantities are fixed constants.

## 2. A single scalar code for a state and its dummy bits

Define the total nonnegative coefficient bound

    Tmass=2c0+2m sum_{s,i} c_si.

Choose a power of two `R=2^t>=4` such that

    R>=max(Tmass,2mu)+2.                                 (3)

The symbol `R` in this section is an inner radix, distinct from the
relation `Rlocal`. Put

    p=k-1, H=k+m-2,
    B=R^(H+1)=2^d, d=t(H+1).

For a site, let `z_0,...,z_(k-1)` be its genuine state bits, and let
`z_k,...,z_(m-1)` be arbitrary dummy bits. Encode the whole cell by

    Ccell=2 sum_{j=0}^{m-1} z_j R^j.                     (4)

The positions are consecutive inner-radix exponents. No Sidon-set or
distinct-differences hypothesis is needed. The factor two makes the cell
even. Its allowed binary positions are exactly

    1, 1+t, ..., 1+t(m-1).

They are distinct and lie below `d`, since `m>=k>=1` and `t>=2`.
Moreover, `0<=Ccell<B`, because its inner-radix digits are zero or two
and its degree is at most `m-1<=H`.

The state mask is the fixed numeral

    MC=(B-1)-2 sum_{j=0}^{m-1} R^j.                      (5)

It is the binary complement within the cell of those `m` allowed bit
positions. Therefore, for an arbitrary integer `0<=Ccell<B`,

    Ccell AND MC=0

is equivalent to exactly the encoding (4) with Boolean state and dummy
bits. It has `popcount(MC)=d-m` and `MC` is odd. Dummy bits do not alter
the positions or interpretation of the first `k` state bits.

## 3. The fixed products and the isolated target block

For each site `s`, form the fixed coefficient

    Ds=sum_{i=0}^{k-1} c_si R^(p-i),

and the fixed positive guard `G0=2c0 R^p`. For encoded neighboring cells
`C_0,...,C_(g-1)`, set

    Fcell=G0+sum_s Ds C_s.                               (6)

View this as an ordinary polynomial in `R`. A product term from state
coefficient `c_si` and encoded bit `z_sj` has nonnegative coefficient
`2c_si z_sj` and degree `p+j-i`. Its degree lies between zero and `H`.
The sum of all coefficients is at most `Tmass`, because there are at
most `m` encoded bits multiplying each `c_si`. Thus every coefficient
lies in `[0,R-2]` by (3). No inner-radix carry occurs, even when many
off-diagonal terms have the same degree.

At the target degree `p`, a product contributes exactly when `j=i`.
The actual normalized target digit is therefore

    2c0+2 sum_{s,i<k} c_si z_si=2phi(state bits).         (7)

Every dummy index `j>=k` satisfies `p+j-i>=k>p` for `i<k`, so it only
contributes above the target block. The genuine off-diagonal terms may
lie below or above it. They cannot carry into it or out of it because
of the global nonnegative coefficient bound. This is why ordinary
consecutive positions suffice.

The same degree and coefficient estimates give

    0<Fcell<=(R-2) sum_{e=0}^H R^e<=B-2.                (8)

Let the field mask be

    MF=2mu R^p.                                         (9)

Condition (3) keeps `2mu` inside one inner-radix digit, and `p<=H`
keeps the mask inside the cell. It has exactly `m` set bits. It tests
only (7); hence

    Fcell AND MF=0 iff the projected genuine state tuple is in Rlocal.

The factor two shifts both the affine value and its mask by one binary
place and preserves the Boolean test. In particular, `MF` is even.

## 4. State validity cannot be supplied by dummy bits

The semantics of a cell is its first `k` bits. Dummies are ignored by
that projection and by the target digit (7). Every genuine tuple has
an encoding, for example with all dummy bits zero, and every choice of
dummy bits gives exactly the same truth value for that genuine tuple.

For a finite alphabet, first choose an injective coding

    Enc: Alphabet -> {0,1}^k

and define `Rlocal` to include the validity requirement that each site
belongs to `Enc(Alphabet)`, as well as the intended local constraint.
If the all-zero bit pattern is not a valid state code, a cell with zero
genuine bits and nonzero dummy bits still projects to that invalid code
and is rejected. It does not become a new alphabet symbol.

Exclusion of the all-zero *whole tuple* is the hypothesis needed for
positive coefficients. Exclusion of the all-zero *individual state* is
a separate optional alphabet convention and must actually be included
in `Rlocal` if desired. The compiler does not silently add it. If every
alphabet code is nonzero, every genuine state cell is automatically
nonzero even when all dummy bits are zero.

## 5. Conditional aligned-word composition and mask balance

Suppose the word geometry `q=B^N`, `N>=1`, and
`J=(q-1)/(B-1)` has already been established. Supply `g` aligned words

    C_s=sum_{v=0}^{N-1} C_sv B^v

whose cells satisfy the state mask. Distributivity and (8) give the exact
ordinary integer equality

    Fword=G0 J+sum_s Ds C_s
         =sum_{v=0}^{N-1} Fcell_v B^v,
    0<Fword<q.                                          (10)

There is no carry between cells. Consequently

    Fword AND (MF J)=0

is equivalent to the desired local relation at every aligned cell.
For supplied neighboring words and repunit, the displayed formation of
`Fword` costs at most `(g+1)M+gA`: one fixed-coefficient product per site,
one guard product, and `g` additions. This arithmetic count is independent
of the number of state bits and the alphabet size. Forming those supplied
neighbor words and enforcing the masks is not included in it.

The two local mask weights satisfy the exact identity

    popcount(MC)+popcount(MF)=(d-m)+m=d.                 (11)

Thus, conditionally on the required fields and geometry, put

    S=C+qFword, M=J(MC+qMF), Lambda=q^2,
    r=(Lambda-S)(Lambda-1)+M.

Both field masks are smaller than `B`, so their repeated and concatenated
blocks are disjoint and `popcount(M)=dN`. The inverse-packing threshold is

    log2(Lambda)+popcount(M)=2dN+dN=3dN=log2(q^3).

Also `C` is even, `q` is even, and `M` is odd. The resulting index `r` is
odd. These identities fit the mask-weight and parity conditions of the
existing inverse-packing kernel construction. They do not by themselves
prove its pre-power field bounds, its positive kernel extension, or the
neighbor and acceptance interfaces for a newly chosen machine.

In particular, arbitrary untyped integers cannot be substituted for the
cells in Sections 3--5. The polynomial coefficient bounds depend on the
Boolean bit positions supplied by the state mask. Any integrated system
must establish geometry, field bounds, and typing in a sound order.

## 6. Bounded exact verification

The checker covers every zero-forbidden Boolean relation of arity one,
two, or three and every decomposition of its arity into equal site
blocks. This gives **274 compilations and 2,116 genuine state assignments**.
It exhausts the dummy bits whenever there are at most seven, and otherwise
uses zero, all-one, every singleton, and reproducible random dummy
patterns. In total it checks **33,674 state/dummy cell combinations**.
Nine compilations exercise repetition of a forbidden clause to make
`m>=k`.

For each checked cell tuple it constructs the ordinary polynomial
coefficients separately, verifies the coefficient mass and no-carry
bounds, compares the target digit with `2phi`, checks the scalar truth
condition, and verifies cell masks and parity.

A separate two-site example uses the three genuine states `01,10,11`
with a constraint that the two states differ. Both zero and all-one
dummy fillings are tested on every four-bit genuine assignment,
including invalid zero states. Two hundred packed word cases at lengths
one through five check exact affine composition, mask equivalence, the
mask-weight identity, odd parity, and the conditional inverse-packing
threshold. Running without `--write` recomputes the saved JSON receipt
exactly. The proofs above, rather than the finite examples, cover
arbitrary fixed relations, state widths, and word lengths.

Independent scoped mathematical/source review confirms the coefficient
mass bound, the isolated target block, repeated-clause padding, projected
state validity, and the exact mask balance. A fresh independent default
run reproduces the saved receipt. The review does not extend this local
lemma to an integrated machine certificate.
