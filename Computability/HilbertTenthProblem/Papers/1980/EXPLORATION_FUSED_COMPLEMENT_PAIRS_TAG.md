# Folding the remaining packing-only complements

Review status: author and two independent complete proof/source reviews and
fresh verification runs passed without findings. The construction and
arithmetic are frozen. The separate 109 predecessor is unchanged.

This exact successor to `EXPLORATION_FUSED_MARKER_PAIR_TAG.md` costs
**107 operations = 55 multiplications + 52 additions/subtractions**, with
the same **34 positive existential unknowns and 21 equations**. It has
identical positive source solutions, packed value and kernel witnesses.
The fixed binary appendant must still have length a>=2, and the input is
still a specified Boolean ternary encoding of a binary word. The count
does not include an ordinary numerical-input compiler or assert universality.

## 1. Two derived registers are used only by the packing

The109 schedule computes

    Nbar=Nsum-N,
    Ebar=prefix_scale-E, where prefix_scale=cH.

Each register is used only in the packing. Both corresponding source
comparisons and positive adapters were already eliminated in reviewed
predecessors. The geometry and power computations already supply
qm1=q-1 and q2=q*q.

The conceptual ten-field order remains

    Gstar, Q, S0, S1, M0, M1, Ebar, E, Nbar, N,            (1)

with M0=L-M1 as in109. The top two fields have the exact identity

    Nbar+qN=Nsum+(q-1)N.                                  (2)

Replace the old multiplication qN and addition of Nbar by the multiplication
qm1*N and addition of Nsum. Both pairs cost one multiplication and one
addition. Delete the now-unused subtraction defining Nbar: this saves one
addition/subtraction.

Call this already computed top pair T. The next two fields satisfy

    Ebar+q(E+qT)=cH+(q-1)E+q^2 T.                         (3)

Replace the four old Horner operations by

    prefix_scaled=qm1*E,
    prefix_pair=prefix_scale+prefix_scaled,
    content_shifted=q2*T,
    joined=prefix_pair+content_shifted.

Both versions cost two multiplications and two additions. Delete the
now-unused subtraction defining Ebar: this saves another addition/subtraction.
The cH multiplication is retained and already paid; no scaled-head product
or coefficient calculation is being omitted.

Together the changes save exactly two additions/subtractions and change
no other operation count. M0, Ebar and Nbar are now proof abbreviations
only; none occurs as a runtime register or instruction operand. All ten
conceptual mask fields in(1) remain present in the identical packed integer.

## 2. No new soundness or positivity assumption

Equations(2)--(3) are polynomial identities for arbitrary integers, including
negative formal complements. They do not require the word bounds or mask
conclusions that the110/111 proofs later establish. The supplied coordinates,
positive domains and all ten outer equations are unchanged. The eleven
kernel equations, scale, r and betaP are also unchanged.

In particular this is not an omission of either the prefix or content
complement mask. The exact packed polynomial still equals the ten-field
packing(1), with the same possibly signed intermediate expressions. The
reviewed proof still establishes positive P before the kernel, recovers the
low six fields, bounds N and E, and excludes negative Ebar and Nbar in
their actual normalized chunks. Factoring the expression that computes P
does not weaken that proof or change its ordering.

Every supplied positive tuple satisfies the107 DAG exactly when it satisfies
the109 DAG. The correspondence is the identity on all supplied coordinates.
Every packed field, P, r, betaP and all seventeen positive Pell auxiliaries
has the same value. Some internal products used to form the pairs have
different values, which are not compared or asserted to be preserved.

Thus complete positive encoded-word halting equivalence transfers with
precisely the existing a>=2 contract. No new width choice, field bound,
first-selector condition, parity adapter or kernel converse is needed.
The earlier zero-field cases and formal continuations after a first genuine
halt remain admissible. The one-symbol appendant case remains outside this
source theorem, as stated in110.

## 3. Complete source and fresh verification

`../verification/explore_fused_complement_pairs_tag.py` constructs all107
instructions and checks the complete ten outer and eleven kernel source
residuals, including the unchanged norm-source correction at combined
index18. It independently compares the actual top pair, prefix pair,
marker join, full packing, index expression and bound with109. All three
removed register names are checked to be absent from the runtime DAG.

The bounded identity regression checks26,880 joint regroupings, including
84 distinct negative content-pair cases and16,800 negative prefix cases.
It includes a nonpower q and signed higher blocks. This is evidence for
the unrestricted algebraic identities, not a claim of full source solutions
in those arbitrary ranges.

Fresh canonical construction evaluates both actual107 and109 prefixes on
776 halting histories with2,006 source rows. Every history checks all ten
outer comparisons in each version, all ten conceptual mask fields, and
the exact native index valuation. All776 packed values and indices are
preserved;514 indices are even and262 odd. The zero conceptual-field
counts are M0:48, Ebar:62, Nbar:6. The earlier three-formal-row example
with a genuine halt after one step is retained. The400 runs reaching the
finite exploration cutoff remain unclassified.

The huge Pell auxiliaries are not materialized; their complete positive
existence and exact preservation follow from the reviewed predecessor.
This is a concrete two-operation improvement for the displayed certificate,
not an optimality claim or an improvement to the separate universal
numerical-input frontier.
