# Unweighted joint index authentication and power pooling

Round 23, 26 October 2026. This is a synthesis of the incoming package 176
joint classified-index argument and the incoming mixed-base two-integrality
argument. Neither ingredient is credited as new here. The new combination
removes the base weights from the joint certificate. It uses ordinary
arithmetic, not a newly compiled proof-assistant derivation.

## Theorem

Let W>=258 and |A|>W^W. Let b>=16 be an integer with 12b+10<=W.
Suppose p<=15 raw
principal Pell pairs have representations

    (X_i,Y_i)=epsilon_i (X_{nu_i}(A),Y_{nu_i}(A)),
    epsilon_i in {-1,1}, |nu_i|<=b.

The requested signed indices k_i satisfy |k_i|<=b. There are s<=5 base
blocks and r<=17 power requests. Every actual base n_j and output m_i
has absolute value at most b. Each request uses one of the principal
pairs; repetitions of a pair are permitted. Retained gate equations give
Z_i=A Y_i. Define

    d=A-1,
    Omega=sum_principal ((X_i-1)^2+(Y_i-k_i)^2),
    T_j=2A n_j-n_j^2-1,
    H_j=sum_requests Y_i(m_i-X_i),
    S_j=sum_requests ((m_i-X_i+Z_i)^2-Y_i^2),
    E_j=S_j-2n_j H_j.

Then the following are equivalent:

1. Every principal pair is canonical at its requested signed index, and
   every request at a nonzero base satisfies m_i=n_j^{k_i} in Q.
2. There exists an integer z satisfying the single unweighted residual

    Omega product_j T_j
      + d sum_j E_j product_(h!=j) T_h
      - z d product_j T_j = 0.                         (UJ)

Zero-base requests impose no condition, since T_j=-1. A base with |n_j|>=2
forces k_i>=0 by integrality. Unit bases permit negative indices.
No nonzero-base, common-sign, distinctness or coprimality assumption is used.

## Nonzero denominators and classified residues

Put M=W^W. Since A is an integer and |A|>M, |A-1|>=M and A-1 has the
sign of A. If n_j=0 then T_j=-1. Otherwise

    |T_j|/|n_j| >= 2|A|-(n_j^2+1)/|n_j|
                  >=2|A|-b-1 > M,

and n_j T_j has the sign of A. All denominators are nonzero.

The integral signed Pell recurrence modulo d gives X_nu=1 and Y_nu=nu.
Thus Omega is congruent modulo d to

    o=sum_principal ((epsilon_i-1)^2+(epsilon_i nu_i-k_i)^2).

This is a nonnegative integer with o<=60(1+b^2)<=120b^2. Crucially nu_i
is the already bounded *classified* index, not the requested index whose
correctness remains to be proved.

For each request put delta_i=m_i-X_i+(A-n_j)Y_i. Exact expansion gives

    sum_requests delta_i^2=E_j-T_j sum_requests Y_i^2.       (1)

The signed recurrence in Z[v]/(v^2-(A^2-1)), evaluated at v=n_j-A
modulo T_j, gives

    X_i+(n_j-A)Y_i = epsilon_i n_j^{nu_i} mod T_j.          (2)

For negative nu_i the residue power exists since gcd(n_j,T_j)=1.

## First integrality step

Divide (UJ) by d product T_j and use (1). This makes
Omega/d+sum delta_i^2/T_j an integer. Remove the zero-base summands,
which are already integers. Let J be the remaining blocks and set

    C=(product_(j in J) n_j)^b,  L=product_(j in J) n_j,

with empty products equal to one. For a request in J define the integer

    e_i=C m_i-epsilon_i (C/n_j^b) n_j^(b+nu_i),
    D_j=sum_requests e_i^2,  D=sum_(j in J)D_j.

All exponents here are nonnegative. Equation (2) implies
C delta_i=e_i mod T_j. Hence

    R=C^2 o/d+sum_(j in J)D_j/T_j

is an integer. Because |C|<=b^(5b) and |e_i|<=2b^(6b),

    C^2 o+D <=120b^(10b+2)+68b^(12b)
              <=188b^(12b+2)<b^(12b+5)<W^(12b+5)<=W^W=M.

Here 188<b^3 and b<W; the last exponent is at most W by hypothesis.
Every active denominator has magnitude at
least M, so |R|<1 and R=0. Its summands need not have the same sign.

## Second integrality step

The two exact identities

    2A/d=2+2/d,
    2A/T_j=1/n_j+(n_j^2+1)/(n_j T_j)

and R=0 give U+V=0, where

    U=2C^2 o+sum_(j in J)D_j/n_j,
    V=2C^2 o/d+sum_(j in J)D_j(n_j^2+1)/(n_j T_j).

LU is an integer, so LV=-LU is an integer. The previous denominator
estimate gives

    (n_j^2+1)/|n_j T_j|
      <=(1+n_j^(-2))/(2|A|-b-1)<2/M.

Also |L|<=b^5. It follows that

    |LV| <=[240b^(10b+7)+136b^(12b+5)]/M
           <=376b^(12b+7)/M
            <b^(12b+10)/M
            <W^(12b+10)/M <=1.

Here 376<b^3 for b>=16, b<W, and 12b+10<=W. Thus LV=0.
Since L!=0, V=0. Every nonzero summand of V has sign(A): o,D_j are
nonnegative, d has sign(A), and n_j T_j has sign(A). Therefore o=0 and
all D_j=0. The first conclusion forces epsilon_i=1 and nu_i=k_i for
every principal pair. The second forces e_i=0, hence m_i=n_j^{k_i}.
For |n_j|>=2 a negative k_i would give the impossible integer equation
m_i n_j^{-k_i}=1.

This also covers J empty: C=L=1 and V=2o/d directly forces o=0.

## Two useful frame corollaries

For the original exact square frame, take b=floor(sqrt(W-1)). Then
b>=16, and 12b+10<=b^2+1<=W: at b=16 the difference
b^2-12b-9 is 55 and it increases thereafter. Thus the theorem applies
to the exact original hypotheses.

A weakened/centered frame may instead supply actual absolute bounds
b<=14sqrt(W), with W>=2^42. Then 12b+10<=168sqrt(W)+10<=W, since
sqrt(W)>=2^21. Consequently the same theorem applies if all *actual*
base/output/nominal-index and preorientation classified-index bounds are
independently established at that b. This is a conditional arithmetic
corollary, not an assertion that an unaudited centered source supplies those
ports. The selected equation files use the conservative exact-square source.

## Converse, restoration and partitions

Canonical pairs make d divide Omega. True powers imply T_j divides
every delta_i, hence T_j divides E_j by (1); at zero bases this is
automatic. Thus z=Omega/d+sum E_j/T_j is integral and satisfies (UJ).

The source orientation quotient is restored as Omega/d, with any recorded
retained-row correction. For a singleton with rows T=T_j and
(delta_i+T Q)=0, restore T and Q=-delta_i/T_j. For an aggregate block,
restore L_j=E_j/T_j and K_j=2H_j+(2A-n_j)L_j. All these are integers,
including zero and unit bases. Restore all original rows before applying
the source semantic sign/bootstrap argument.

One can partition the base blocks. Fuse orientation into any one part
using (UJ); it authenticates *all* principal pairs even if it contains only
some requests. Apply the incoming unweighted mixed-base theorem to the
other parts after canonicality is established. This order is noncircular.

## Literal selected source and arithmetic interface

The source is the conservative affine209 equation reproduced in
`source/pell209_affine.json`, byte-identical to the sibling signed component's
`conservative209/equation.json`. `SOURCE_BINDING.json` pins its hash and exact
source-substitution certificate. The sibling signed component retains the
ordinary affine-horizon proof and the complete incoming Pell-growth210
source, proof and reconstruction closure.

There are thirteen principal pairs and fifteen requests at four actual bases.
`joint_pell.py` records their exact affine ports, checks their norm and product
rows, and verifies the literal orientation numerator modulo the recorded
retained norm/guard rows. It independently checks both singleton congruence
blocks, both prior aggregate blocks, all norm-row corrections introduced by
the centered chart, and privacy of every removed quotient coordinate.

The retained squared C-anchor theorem bounds each raw classified index by
|C| before using the orientation row. The unchanged actual-square frame
includes C and every base, nominal index and output, so each absolute value
is at most b=floor(sqrt(W-1)); the displayed exact-frame corollary applies.
The frame also gives W>=258 and |A|>W^W independently of semantic power
interpretation. No sign bootstrap or unit-base assumption is used to apply
the joint theorem. Restore all original quotient rows before invoking the
proved source arithmetic/bootstrap semantics.

Earlier weighted-source instances with 205 variables/degree24 were useful
research controls, but their arrays are not part of this selected component.
The final package uses only the conservative affine209 source, not a weakened
or centered-square replacement frame.

## Exact numerator chart and the selected 113-variable equation

The selected low-degree joint seed uses the conservative affine209 source,
with 13 principal pairs, 15 requests and four bases B,D,q,q+1. It partitions
these as {B} and {D,q,q+1}, fusing orientation only with the first block.
Its unfused companion keeps the original orientation quotient.

Before monic elimination replace Omega in the fused residual by

    Omega_proxy=Omega+R_frame,

where R_frame is the RETAINED exact actual-square-frame residual. This is
not a weakened frame and Omega_proxy is not claimed to be nonnegative.
The exact row operation is

    R_UJ <- R_UJ+R_frame*T_B,

with inverse subtraction. Since R_frame is still required to vanish,
the old and new joint residuals agree on the retained zero set. The added
frame row cancels Omega's x^2 monomial. After eliminating x by a degree-four
unit definition, this avoids a degree-ten residual and permits every final
residual to retain degree at most eight.

The certificate explicitly lists the proxy correction, so an independent
checker verifies a polynomial identity rather than inferring its validity
from a row label. The same 89 unit-definition pivots on the unfused seed give
114 variables, 54 residuals and degree 16; on the joint/frame-shifted seed they
give 113 variables, 53 residuals and degree 16. Both have collected coefficient
height 16250018885420533678080. Their collected supports are 1,008,268 and
1,030,202 respectively. This is an isolated one-coordinate gain at unchanged
degree/height and a roughly 2.2% support cost, not a global-optimality claim.
A different unfused projection has 114 variables/degree 16 and only 127,818
collected terms at the same height; it is retained as the sparse alternative.
The generic 138-variable degree-eight endpoint is an exact monic projection
of affine209 and does not need the new joint theorem.

Every monic step solves a current residual eps*x_v+f=0, eps in{+1,-1},
as x_v=-eps*f and substitutes it into all other rows. Deleting that row and
coordinate is an integral bijection of zero sets, with inverse insertion.
The finite ordered ledgers contain every literal definition and surviving
index. Reversing them restores all eliminated coordinates; only after those
exact maps does the arithmetic theorem restore private quotient witnesses.

## Calibration and scope

The exact maps plus this ordinary theorem preserve existential integer
solvability of the authenticated source. Composing with its named inherited
C222-to-ZF-to-ZFC calibration gives, internally in ZFC,

    [the resulting polynomial has no integer zero] iff Con(ZFC).

No consistency assertion, root search, unknown coefficient, global optimum,
external peer review or new end-to-end formal-kernel build is claimed.
