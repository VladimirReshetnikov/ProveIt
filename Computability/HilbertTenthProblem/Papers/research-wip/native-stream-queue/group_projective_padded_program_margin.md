# Fixed padded program numerals supply the table margin

For fixed positive compiler numerals satisfying

    alpha+beta+1>=m,                              (1)

the [scalar-projection compiler](group_projective_scalar_projections.md)
can delete one more addition. Its ordinary positive input remains x;
no runtime padding or extra input witness is introduced. All comparison
and witness counts, and every exact polynomial degree, are unchanged.

Condition (1) is compatible with a single fixed universal alphabet.
Section 4 gives an explicit padded enumeration, builds its alphabet
once, and then selects a suitable fixed program index. This is a
particular choice of universal enumeration, not an assertion that
arbitrarily large equivalent indices exist in the earlier unspecified
enumeration.

Write epsilon=1 for the optional controller-mask reuse, which requires
m>=8, and chi=1 when P is computed rather than supplied. With the
inherited m=2^h, paid port cost p and sparse-flow cost f, the new
certificate costs

    C=3m+3h+p+185+f-3min(h,3)-epsilon.              (2)

The complete ledgers are

| Computed native fields | Equations | Positive witnesses | SOS polynomial |
|---|---:|---:|---:|
|a,d,k,s|18-chi|m+34-chi|C+53-3chi|
|a,c,d,k,r,s|16-chi|m+32-chi|C+47-3chi|

Thus the polynomial base constants, before subtracting epsilon, are
238/235 for the four-field variant and232/229 for the six-field variant,
where each pair means supplied/computed P. Relative to the immediate
parent every variant saves exactly one addition, in both its comparison
certificate and its single polynomial. The parameters in these formulas
describe a supplied fixed table; no numerical universal alphabet is
instantiated and the separate75/88 bounds are unchanged.

## 1. The redundant table-height addition

The general scalar-projection source pays

    u=alpha*x+(beta+1),
    height_sum=u+height_slack,
    D=height_sum+m.                               (3)

The first line has the same paid two-gate affine prefix as before.
The extra addition of m ensures B=8D>m after removal of the positive
radix-margin coordinate and its comparison.

Under (1), positivity of x and height_slack already gives

    u>=alpha+beta+1>=m,
    D=u+height_slack>u>=m,
    B=8D>m.                                      (4)

Delete height_sum and replace the final gate in (3) by
`D=u+height_slack`. All other source gates and comparisons are retained.
The boundary again has five gates: the affine input's multiplication
and addition, followed by D, C0=D-1 and Iodd=C0+u. The same range
coefficient D+C0=2D-1 remains shared.

Condition (1) is checked on fixed compiler data before producing the
circuit. It is not an uncharged comparison of varying witnesses. The
source rejects the specialization if (1) fails. It continues to charge
the multiplication alpha*x and all other fixed-numeral products.

## 2. Positive soundness and completeness

The scalar restoration proof remains valid with (4) in place of the
stronger D>u+m. The computed repunit is

    J=sum_e(Ehat_e-1)>=0.

The retained history equation gives P>=5. The repunit comparison
P=(B-1)J+1, or its defining identity when chi=1, therefore forces
J>0 before any native typing theorem is invoked. The omitted positive
radix slack is B-m>0 by (4). When P is computed, B>1 and J>=0 give
P>=1 even before the comparisons hold.

There is a particularly direct positive extension to the
[unit-product compiler](group_projective_unit_product.md): retain
height_slack unchanged, restore J by its computed value, restore the
radix slack as B-m, and restore P by its computed value if necessary.
That parent's definition is exactly D=u+height_slack. Hence all three
omitted scalar equations are identities and every retained residual
agrees on this extension. All restored coordinates are strictly positive
on the new zero set by the preceding scalar argument. Its full typing,
controller, selected-source, range and history theorem now applies with
the same ordinary input.

Conversely, a positive zero of this unit-product parent already has the
forced values of J, the radix slack and P. Erase the corresponding
coordinates. Under condition (1), the resulting source computes precisely
the same D and every other register, so it is a new positive zero.
Thus, for these fixed numerals, erasure and restoration are inverse
on the complete positive solution sets of the unit-product parent.

Equivalently, completeness can be read directly from an accepted macro
word: choose a sufficiently large dyadic D with D>u and
D>1+max|signed state|. Put height_slack=D-u>0. The fixed-numeral margin
ensures B>m, so the usual genuine histories, hats, positive bounds and
one full native extension supply the new tuple. No particular duration
or additional congruence for D is imposed.

The generic relation remains paired action on (1,u) ending at e2 in
both blocks. For a compatible fixed reflected universal alphabet the
same ordinary universal input predicate follows, as in the parent.

## 3. Exact signed identity and degree preservation

To compare with the immediate general scalar-projection parent, use

    height_slack_general=height_slack_special-m.    (5)

Then its D from (3) equals the new D from (4). Every retained computed
register, every residual and the whole SOS polynomial are identical
under (5), on arbitrary integer assignments. Only the obsolete
height_sum register disappears.

The restored coordinate in (5) can be nonpositive even when every
specialized supplied coordinate is positive. Therefore (5) is not
claimed as a positive solution bijection with the immediate parent.
Positive soundness uses the direct unit-product extension in Section 2;
both compilers' completeness also follows from their respective free
large-D choices.

Translation of one supplied coordinate by a fixed constant leaves the
entire highest homogeneous part unchanged. The parent's exact degrees
and leading forms therefore persist without a fresh expanded polynomial
calculation. Put L=m+18 for epsilon=0 and L=2m+10 for epsilon=1, and
nu=1+chi. The exact degrees are

    four fields: 12nu L+16,
    six fields:  nu*(32L+4m+60)+38.                (6)

In particular the eight combinations have the same degree table:

| Fields | P | Eight-lane mask | Controller mask, m>=8 |
|---|---|---:|---:|
|four|supplied|12m+232|24m+136|
|four|computed|24m+448|48m+256|
|six|supplied|36m+674|68m+418|
|six|computed|72m+1310|136m+798|

The computed-P case poses no exception: its highest part is still
8*(alpha*x+height_slack)*sum_e Ehat_e, since the removed m has degree
zero. Degree is measured in the actual supplied coordinates, including
x; no equation such as P=B^t is used to reduce it.

Writing the inherited common-register savings as d_M,d_A, the new
certificate split is

    M=m+2h+82+f_M-d_M-epsilon,
    A=2m+h+p+103+f_A-d_A.

The SOS splits are

    four: M=m+2h+100+f_M-d_M-epsilon-chi,
          A=2m+h+p+138+f_A-d_A-2chi;
    six:  M=m+2h+98+f_M-d_M-epsilon-chi,
          A=2m+h+p+134+f_A-d_A-2chi.

These charge e residual subtractions, e squares and e-1 summation
additions for the actual e=18-chi or16-chi equations.

## 4. One explicitly padded universal enumeration

Begin with any fixed effective enumeration (T_e)_(e>=0) of all c.e.
sets of positive integers. Define the effective repeated enumeration

    S_p=T_(v2(p+1)), p>=0,                        (7)

where v2 is the exponent of two dividing a positive integer. The indices
for T_e include the entire unbounded family

    p=2^e(2k+1)-1, k>=0.                         (8)

Indeed p+1 has exact two-adic valuation e. Define one fixed c.e. set

    U_pad={2^p(2x+1): p>=0 and x in S_p}.          (9)

It is c.e. by effective dovetailing. Apply the already established
[universal group construction](group_commutator_universal_substrate.md)
and its reflected projective interface to this particular U_pad once.
This produces one fixed finite alphabet, its fixed macro table and
its padded edge count m. The construction is independent of the
subsequent choice of the requested e.

After this fixed m exists, choose k=m in (8):

    p_e=2^e(2m+1)-1>=2m.                         (10)

Then S_(p_e)=T_e. The ordinary-input code is

    y=2^(p_e)*(2x+1).

Its exact two-adic valuation is p_e, and its odd part recovers x.
Thus y is in U_pad if and only if x is in T_e. The fixed projective
representation supplies the compiler numerals

    alpha=12*2^(p_e+1), beta=12*2^(p_e).          (11)

They satisfy alpha>=m, hence (1). The runtime input prefix is still
only alpha*x followed by addition of beta+1. All exponentiation in
(10)–(11) prepares fixed program numerals; it contributes no variable-input
gate and introduces no existential code for x. This uses exactly the
existing arithmetic-operation convention for fixed integer constants;
it is not a statement that preparing their potentially large binary
expansions has negligible bit complexity.

The order matters: first fix (7) and U_pad, then build its one alphabet
and determine m, then choose the equivalent program index (10). The
alphabet does not depend on that last choice, so the margin argument is
not circular. All programs use that same fixed alphabet.

This construction deliberately specifies a padded enumeration. An
earlier alphabet built from a different unspecified universal enumeration
need not have the same numerical generators or the same m. The result
asserts a complete uniform construction with one fixed alphabet for
U_pad, and a one-addition specialization for every supplied table and
numerals meeting (1); it does not silently replace an existing alphabet
while claiming its numerical size is unchanged.

## 5. Executable checks

The [source](group_projective_padded_program_margin.py) exposes the
parent's options `variant`, `controller_mask` and `compute_length`, and
checks condition (1). Its [receipt](group_projective_padded_program_margin.json)
records twenty full source variants over m=2,8,16, their unchanged
coordinate/comparison lists, the one-addition saving and inherited
exact degrees.

Across2,560 assignments, including640 signed cases, the checker applies
(5) and verifies every retained computed register, every residual and
the complete SOS against the actual general-parent source. Positive
cases explicitly check B>m and record those whose general translated
height coordinate is nonpositive, so the identity is not confused with
a positive bijection. A fixed table/numeral combination violating (1)
is rejected. Degree preservation follows from the exact constant
translation; these checks do not rerun the parent's large weighted
degree calculations.

The enumeration audit checks140 table-dependent padded indices and
576 repeated-index fixtures with exact two-adic decoding. These finite
checks supplement the elementary proofs (8)–(11); no enormous program
numeral is required merely to verify its lower bound.

Eight genuine outer fixtures use the eight single-shear macros, so
m=16, with alpha=24, beta=12 and x=1. Here u=37 already supplies the
margin. The fixed word is the reflected target36 followed by two hub
idles. Independent signed simulation starts at (1,37) in both blocks
and ends at e2; the checker constructs positive shifted histories,
edge/output hats and bounds for every field/mask/length variant, then
verifies the joined AND, reconstructed J/P, transports and outer scalar
comparisons. These fixtures satisfy the actual fixed-numeral hypothesis;
they do not reuse a long-macro table whose m would exceed u.

Native Pell coordinates in those fixtures are explicit placeholders,
not a claim of numerical full zeros. Their complete positive extensions
come from the exact parent theorem. Run the checker normally to compare
the deterministic receipt, or use `--write` to regenerate it. No parent
packet is edited by this construction.

Two independent full proof/source reviews passed without findings. They
checked the order of the padded-enumeration construction, the positive
restoration to the unit-product parent, the distinct signed translation
to the immediate parent, and all arithmetic and degree claims. One
review additionally checked768 independently expanded unit-parent
residual/SOS identities with positive restored coordinates, including24
minimal-margin cases whose translated general height was nonpositive.
The author's fresh default receipt replay passed. The second review
avoided duplicating that replay; its extra identities and proof review
are recorded separately from the executable's own evidence.
