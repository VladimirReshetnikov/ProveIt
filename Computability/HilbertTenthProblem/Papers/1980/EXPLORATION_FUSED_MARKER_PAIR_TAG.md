# Folding the derived marker into its two remaining uses

Review status: author and two independent complete proof/source reviews and
fresh verification runs passed without findings. The construction and
arithmetic are frozen. The frozen 110 predecessor is unchanged.

This exact arithmetic successor to
`EXPLORATION_IMPLICIT_UNSELECTED_MARKER_TAG.md` costs **109 operations =
55 multiplications + 54 additions/subtractions**, with the same **34 positive
existential unknowns and 21 equations**. Its source solutions are identical
to110. In particular, the fixed nonzero appendant still has length a>=2,
and the input remains a specified Boolean ternary encoding of a binary
word. No new input or universal computation claim is made.

## 1. The two uses of the derived marker

The110 schedule computes M0=L-M1. Apart from its definition, this register
is used only in the length output and at its position in the packing. With
B=3^(a-1), the length computation is

    l_append=B*M1,
    l_output=M0+l_append.

Replace it by

    l_append=(B-1)*M1,
    l_output=L+l_append.                                  (1)

The fixed numeral B-1 is free under the same counting convention as B.
Both versions cost one multiplication and one addition. Their outputs
agree as polynomial identities when M0=L-M1, even before any source or
sign condition is used.

For the packing, retain the conceptual field order

    Gstar, Q, S0, S1, M0, M1, Ebar, E, Nbar, N.            (2)

Let Rest denote the Horner value of the last four fields, beginning with
Ebar. The old two marker stages produce

    M0+q*(M1+q*Rest).

The geometry and power computations already supply qm1=q-1 and q2=q*q.
Replace the four operations of those stages by the following four:

    marker_scaled=qm1*M1,
    marker_pair=L+marker_scaled,
    higher_scaled=q2*Rest,
    joined=marker_pair+higher_scaled.                     (3)

Indeed

    (L-M1)+q*(M1+q*Rest)
      =L+(q-1)*M1+q^2*Rest.                              (4)

Both packing implementations cost two multiplications and two additions.
After(1) and(3), no instruction refers to M0. Delete its single subtraction
M0=L-M1. This is the entire saving: one addition/subtraction, with no
change to the multiplication, unknown or equation counts. The field M0
in(2) is now solely the proof abbreviation L-M1; the verifier does not
compute an extra runtime register for it.

## 2. Exact source and positive solution equivalence

Identities(1) and(4) are unrestricted integer polynomial identities. They
do not depend on Boolean digits, positivity of M0, a power-of-three q,
or the eventual source equations. The registers qm1 and q2 are actual
earlier computations of q-1 and q^2, so their use introduces no extra
equation assumption or residual correction.

Every supplied positive coordinate is unchanged. All ten outer source
polynomials and eleven kernel source polynomials are exactly the110
polynomials. The length output, packed integer P, index equation, scale
and packed upper bound have identical values. Some internal products,
such as l_append, change; no equality of those unused internal values is
claimed or needed.

The110 proof therefore transfers directly. In particular it interprets the
conceptual M0=L-M1 as possibly signed before the mask, proves the positive
combined pair L+(q-1)M1, and then recovers M0>=0 from the low blocks.
This source reorganization does not delete that mask or weaken its proof.

Conversely, the same supplied tuple satisfies either DAG exactly when it
satisfies the other. The packed word, r, betaP and all seventeen positive
Pell auxiliaries are unchanged. The positive solution correspondence is
the identity on every supplied coordinate, rather than a reconstruction
requiring new kernel witnesses. All zero-marker and post-first-halt cases
already covered by110 remain covered here.

The a>=2 theorem restriction is also unchanged. The separate elementary
one-symbol appendant classification in110 is not an assertion that this
source system is valid outside its proved contract.

## 3. Exact checker and fresh numerical evidence

`../verification/explore_fused_marker_pair_tag.py` constructs the complete
109-instruction schedule, including every positive adapter and all geometry,
packing, bound and44-operation kernel instructions. It verifies all21
source residuals by exact symbolic expansion, including the unchanged norm
correction at combined index18. It independently compares the complete
length output, marker join, full packing, index expression and bound with
the actual110 DAG. The runtime instruction list is checked to contain no
M0 definition or operand.

The bounded identity regression covers1,344 cases, including504 with
negative conceptual M0, a nonpower q and signed Rest. Its scope is the
unrestricted algebraic identity, not complete source satisfiability.

Fresh canonical construction evaluates both actual prefixes on776 halting
histories with2,006 source rows. Every example checks all ten outer
comparisons in each version, every conceptual field, and the exact native
index valuation. All776 indices are preserved;514 are even and262 odd.
There are48 zero conceptual M0 words. The admitted three-formal-row example
with an earlier genuine halt is retained. The400 exploration-cutoff runs
remain unclassified.

Enormous Pell auxiliary values are not materialized: the complete110
positive converse and their exact preservation prove their existence.
This is a concrete arithmetic saving, not an optimality assertion or a
change to the separate universal numerical-input frontier.
