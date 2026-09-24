# Reusing the selected-marker double in the lowest packing fields

Review status: author and two independent complete proof/source reviews and
fresh verification runs passed without findings. The construction and
arithmetic are frozen. The frozen 107 predecessor is unchanged.

This exact successor to `EXPLORATION_FUSED_COMPLEMENT_PAIRS_TAG.md` costs
**106 operations = 54 multiplications + 52 additions/subtractions**, with
the same **34 positive existential unknowns and 21 equations**. It preserves
every positive source solution, packed integer and kernel witness of107.
The fixed binary appendant still has length a>=2 and the input is a specified
Boolean ternary encoding of a binary word. No ordinary numerical-input or
universal operation bound is asserted.

## 1. The shared value already required by the marker equation

The107 schedule already computes

    twice_Q=2Q,
    M1=twice_Q+S1.

These instructions remain necessary in the new schedule and are fully
counted. Reusing twice_Q in the packing does not introduce a new assumption
or duplicate its multiplication. The geometry and power chains likewise
already compute qm1=q-1, q2=q*q and q4=q2*q2.

The conceptual low four fields are

    Gstar=Q+AH+S0, Q, S0=H-S1, S1.

Let Rest be the already computed Horner value of the remaining six fields,
beginning with the conceptual M0. The exact full packing identity is

    Gstar+qQ+q^2 S0+q^3 S1+q^4 Rest
      =H(A+q^2+1)+(q-1)(Q+q^2 S1)+(twice_Q-S1)+q^4 Rest.  (1)

To check it directly, the coefficients of Q, S1 and H are respectively
q+1, q^3-q^2-1 and A+q^2+1 on both sides. Identity(1) is valid for
arbitrary integer inputs when twice_Q=2Q, including negative formal S0 or
Gstar. It does not presuppose any mask or power conclusion.

## 2. Complete arithmetic saving

Replace the four low Horner stages and their four preparatory instructions

    padding=AH, G=Q+padding, S0=H-S1, Gstar=G+S0

by the following eleven instructions:

    head_coefficient0=A+q2,
    head_coefficient=head_coefficient0+1,
    head_term=H*head_coefficient,
    selector_scaled=q2*S1,
    selector_inner=Q+selector_scaled,
    selector_term=qm1*selector_inner,
    selector_residual=twice_Q-S1,
    upper_shifted=q4*Rest,
    low_join0=head_term+selector_term,
    low_join1=low_join0+selector_residual,
    P=low_join1+upper_shifted.                             (2)

The old group costs five multiplications and seven additions/subtractions:
one multiplication and three additions for the four preparatory values,
then four multiplications and four additions for the low Horner stages.
The new group(2) costs four multiplications and seven additions/subtractions.
It therefore saves exactly **one multiplication**, giving106=54M+52A.

The existing twice_Q, qm1, q2 and q4 are each computed once in the complete
schedule. No cost for a newly formed coefficient is omitted: A+q2+1 uses
both additions displayed in(2). After the replacement, padding, G, S0 and
Gstar have no remaining instruction uses and are not runtime registers.
The same is already true of M0, Ebar and Nbar by107. Their conceptual mask
fields remain in the identical packed polynomial.

The intermediate selector_residual may be negative. Only supplied
existential coordinates are constrained to be positive, and the polynomial
evaluation convention permits signed intermediate registers. No domain
constraint has been silently added to(2).

## 3. Exact positive solution correspondence

The conceptual field order remains

    Gstar, Q, S0, S1, M0, M1, Ebar, E, Nbar, N,

where M0=L-M1, Ebar=cH-E and Nbar=Nsum-N. The ten outer source
polynomials are identical to107, and the eleven44-operation kernel source
polynomials are also unchanged. Identity(1) preserves the packed integer
P for every supplied integer tuple, before imposing those equations.

Consequently the existing proof of positive P before the kernel transfers
unchanged, including its potentially signed low fields. The later sequential
recovery of conceptual Gstar, S0 and M0 remains valid. The bounds on N and
E and the recovery of their complements are likewise unaffected. This is
an evaluation change, not a deletion of any of the ten masks or a weakening
of a field bound.

The correspondence between positive107 and106 solutions is the identity
on all34 supplied coordinates. P, r, betaP, scale and all seventeen Pell
auxiliaries are identical. No fresh-index argument, positive-coordinate
adapter, extra width condition or parity promise is needed. The fixed a>=2
contract, first-halt semantics and permitted formal continuations after
a genuine halt are exactly those already proved for107.

## 4. Exact source and fresh numerical evidence

`../verification/explore_shared_marker_low_packing.py` constructs the entire
106-instruction DAG and checks all ten outer and eleven kernel residuals
by symbolic expansion, including the unchanged norm-source correction at
combined index18. It independently expands(1), compares the actual full
packing and index with107, counts the new low group as4M+7A, verifies
that twice_Q is computed exactly once, and checks that every removed name
is absent as both an instruction result and operand.

The bounded identity regression covers2,520 arbitrary coefficient tuples,
including1,620 negative S0 cases,240 negative Gstar cases and864 negative
selector_residual cases. It includes a nonpower q and signed Rest. These
are unrestricted algebraic checks rather than claimed complete source
solutions.

Fresh canonical construction evaluates both actual106 and107 prefixes
on776 halting histories with2,006 source rows. Each checks all ten outer
comparisons in both versions, every conceptual Boolean field, and the exact
native index valuation. All776 indices are preserved;514 are even and262
odd. Zero conceptual-field counts are S0:48, M0:48, Ebar:62 and Nbar:6.
The400 runs reaching the finite exploration cutoff remain unclassified.

The existing three-formal-row example with a true halt after one step is
also retained. Its selector_residual is negative, so the regression contains
an actual admitted full outer tuple exercising the signed intermediate in
(2), not only arbitrary algebraic examples.

Enormous Pell auxiliary values are not materialized. Their positive
existence and exact preservation follow from the reviewed107 converse.
The result is a concrete one-multiplication saving, not an optimality claim
or a change to the separate universal numerical-input frontier.
