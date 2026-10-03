# Range typing removes the duration-height kernel

One binary AND kernel can certify the controller, selected source digits,
the range of every history digit, and the radix itself. Together with
the exact projective endpoint, this removes the entire separate
47-operation geometry kernel. For a supplied fixed macro table the new
complete certificate costs

    3m+3h+p+185+f_flow-3min(h,3),                       (1)

with **26 equations** and **m+40 strictly positive existential witnesses**.
Its single sum-of-squares polynomial costs

    3m+3h+p+262+f_flow-3min(h,3)                        (2)

and has exact degree **12m+232**. Relative to the
[computed-port compiler](group_computed_selector_ports.md), these are
37 fewer certificate operations, 76 fewer polynomial operations,
13 fewer equations and 19 fewer witnesses. The degree increases from
12m+112; this is an explicit arithmetic/degree tradeoff.

The generic relation changes to paired vector action. For any fixed
positive compiler numerals alpha,beta, its ordinary input x>0 is accepted
exactly when a macro word has paired matrices Pmat,Qmat with

    u=alpha*x+beta+1,
    Pmat*(-1,u)^T = Qmat*(-1,u)^T = (0,1)^T.           (3)

For the special fixed universal subgroup, the
[lower-projective theorem](group_projective_zero_mortality6.md),
Sections 2–3, proves that (3) is exactly the original universal query.
That implication is specific to that subgroup; it is not asserted for
arbitrary matrix alphabets. No numerical universal alphabet is
instantiated here, and the formulas do not give a numerical improvement
on the separate 75/88 frontiers.

Here m=2^h>=2 is the padded controller edge count, p is the inherited
physical-port cost and f_flow=f_M+f_A is the literal sparse-flow cost.
For total nonempty macro length L, the established bound f_flow<=2L
gives a corresponding uniform upper bound by replacing f_flow with 2L
in (1)–(2). Fixed numeral multiplications, all signs and every
power-building instruction are charged. All comparisons are retained,
with their residual arithmetic charged in the single-polynomial ledger.

## 1. A freely chosen positive shift and the new endpoint

Supply one positive height_slack=rho and compute

    input_product=alpha*x, u=input_product+(beta+1),
    D=u+rho, c0=D-1, d0=D+u, V=D+1.                 (4)

These are six gates: 1M+5A. The numeral beta+1 is compiler data.
The initial shifted state is (c0,d0,c0,d0), and its required terminal
state is (D,V,D,V). Undoing the shift D gives precisely (3).
The parent already pays for B=8D; that multiplication is retained.
There is no supplied q_geom, equation linking height to duration,
or runtime exponentiation in (4).

Since x,alpha,beta,rho are positive, u>=3 and D>=4. All four initial
and terminal entries are strictly between zero and 2D. Unlike the old
fixed-duration choice, D is existentially chosen large enough for the
actual signed history. The range certificate below will verify the
needed bound directly.

Keep four positive packed histories H_i, eight positive selected-output
hats Zhat_i, positive P,J and the positive edge hats Ehat_e. The computed
ports remain

    E_e=Ehat_e-1,
    S_i=Phi_i-1=sum_(edge e has label i+1) E_e,
    Z_i=Zhat_i-1.                                    (5)

These are mathematical abbreviations for already paid expressions;
no additional decoder gates are introduced. Every E_e,S_i,Z_i is
nonnegative for all positive supplied tuples, before equations hold.
In particular each Phi_i is unconditionally positive.

## 2. One AND test with four purposes

Keep the existing paired-history source order (1,1,0,0,3,3,2,2) and set

    K8=sum_(i=0)^7 P^i, Kc=sum_(e=0)^(m-1) P^e,
    Hb=sum_(i=0)^7 H_(floor(i/2) xor 1) P^i,
    Mb=(B-1)*sum_(i=0)^7 S_i P^i,
    Zb=sum_(i=0)^7 Z_i P^i,
    Hc=sum_e E_e P^e, Mc=J*Kc,
    H0=Hb+P^8*Hc, M0=Mb+P^8*Mc, Z0=Zb+P^8*Hc.

All these registers are already paid in the parent. Its existing
joint_scale is T=P^(m+8). Append a duplicated history region and a
two-lane radix region:

    Rb=(2D-1)*J*K8, T2=T*P^8=P^(m+16),
    H=H0+T*Hb+T2*B,
    M=M0+T*Rb+T2*(B-1),
    Z=Z0+T*Hb,
    N=T2*P^2=P^(m+18).                              (6)

The retained prescribed-scale AND source uses q_sel=16N and the
four-bit truth prefix

    padded_A=16H+12, padded_B=16M+10, F3=16Z+8.

Its other three fields F0,F1,F2 and its native auxiliaries remain
strictly positive supplied witnesses. The
[scalar AND theorem](native_binary_masked_selection63.md) gives exactly
N dyadic, 0<=H,M<N and H AND M=Z. This is a paid polynomial certificate,
not a free bitwise instruction. Before any comparisons, (5), positive
P,J and B>=32 make H,M,Z nonnegative and F3>=8. Thus the native positive
domain is established without any Boolean digit assumption.

The new literal schedule adds exactly the following fourteen gates;
all operands on the right are existing registers or earlier lines:

    range_cell=D+c0, range_origins=range_cell*J,
    Rb=range_origins*K8, T2=T*P8,
    history_shift=T*Hb, mask_shift=T*Rb,
    Hbody=H0+history_shift, Mbody=M0+mask_shift,
    Z=Z0+history_shift,
    Bshift=T2*B, Bminus_shift=T2*(B-1),
    H=Hbody+Bshift, M=Mbody+Bminus_shift,
    N=T2*P2.                                       (7)

This costs **8M+6A**. The range_cell definition reuses c0=D-1;
computing a fresh 2D and subtracting one would cost an extra addition.
P2,P8,K8 and B-1 use the parent's resolved common-register aliases.
The existing four products defining q_sel and the three padded inputs
are redirected to (6); they are not evaluated a second time.

## 3. Scalar bounds before any cell semantics

The retained scalar comparisons include

    (B-1)J+1=P, m+radix_beta=B,
    sum_e E_e=J,
    sum_i H_i+history_bound=P,
    sum_i Zhat_i+selection_bound=P+1.               (8)

At a positive zero these imply P>=B>=32 and J<P. Hence H_i<P,
sum_i Z_i<=P-8, and E_e<=J<P. Equation (5) gives S_i<=J without
using controller typing, so (B-1)S_i<=P-1. Also

    (2D-1)J < (B-1)J=P-1.

Consequently, before P or B has been shown dyadic,

    0<=Hb,Mb,Zb,Rb<P^8,
    0<=Hc<P^m, 0<Mc<P^m,
    0<=H0,M0,Z0<T,
    0<=Hbody,Mbody,Z<T2.                            (9)

The top two-lane region needs only B<=P<P^2. This also covers J=1
and P=B, so no constraint t>=2 is hidden in the construction. Equations
(9) and 0<B-1<B<P^2 give H,M,Z<N.

The scalar AND theorem makes N=P^(m+18) a power of two. Since m+18
is a fixed positive exponent and P is a positive integer, P itself
is a power of two. Every boundary P^8,T,T2 in (6) is now a binary
boundary with the independently proved bounds (9). Splitting the
one AND relation at these boundaries gives exactly

    Hb AND Mb=Zb,
    Hc AND Mc=Hc,
    Hb AND Rb=Hb,
    B AND (B-1)=0.                                 (10)

The last equation, with B>0, makes B a power of two. Write B=2^b
and P=2^ell. The divisibility B-1 | P-1 from (8) forces b|ell:
reduce ell modulo b, obtaining 2^s-1 divisible by 2^b-1 with
0<=s<b, hence s=0. Thus

    P=B^t, J=1+B+...+B^(t-1), t>=1.                (11)

Since B=8D is dyadic and D>=4, D is dyadic too, and 2D=B/4.
This establishes all common geometry from the retained AND core.
There is no second native core or external power-typing hypothesis.

Both extra tests matter. Dyadic P and (8) alone admit the nondyadic
radix B=56, P=2^20, J=(P-1)/55. Also, ordinary selected-source AND
tests do not constrain unselected histories: for D=4, B=32 and all
selectors zero, history digit 8 passes the zero selected-output test.
It fails the added range mask, whose permitted digits are 0 through 7.
These are scoped obstructions to omitting the corresponding regions.

## 4. Recovering the controller, ranges and exact products

The proof of the retained
[regular macro controller](group_regular_macro_controller.md) now
applies using (11). The relation Hc AND Mc=Hc forces each canonical
base-P lane E_e to have a Boolean radix-B digit at each of the t cells.
The checksum sum E_e=J and the paid B>m exclude carries, giving exactly
one edge per cell. The unchanged sparse flow residual is the original
chronological state-flow polynomial: it forces the initial and final
state to be the hub and each successive source to equal the preceding
target. Computed ports (5) therefore give the actual mutually exclusive
physical letters, including hub idles.

Write each positive H_i<P canonically as

    H_i=sum_(j=0)^(t-1) X_i(j) B^j, 0<=X_i(j)<B.

Since 2D is dyadic, (2D-1)J has in each cell exactly the low log2(2D)
bits set. The relation Hb AND Rb=Hb, separated into its eight base-P
lanes, proves

    0<=X_i(j)<2D                                  (12)

for every history and every cell. Each history appears twice in Hb;
both copies impose the same range condition. No positivity of the
individual supplied digits is assumed or needed for soundness.

Now Mb contains full radix-B masks precisely at the selected cells.
The first equation of (10), together with the scalar output bounds
Z_i<P already proved, forces the exact lane identities

    Z_i=sum_j S_i(j) X_(floor(i/2) xor 1)(j) B^j.    (13)

This is the selected-source product obligation. Global nonnegativity
and the output bound prevent borrowing or carrying between its lanes.
Neither (12) nor (13) is an unpaid interpretation of a packed integer.

## 5. Histories without a duration-dependent height bound

Keep all four aggregate recurrence equations. With initial entries I_i
and endpoint entries E_i from (4), they are

    B*(H_i+delta_i)=H_i+E_i*P-I_i,
    delta_i=(Z_(2i)-Z_(2i+1))-D*(S_(2i)-S_(2i+1)). (14)

The constant coefficient of each residual in (14) is I_i-X_i(0).
Its absolute value is less than 2D<B, because I_i is strictly between
0 and 2D and (12) holds. Reduction modulo B therefore forces it to
vanish, recovering the initial state simultaneously in all four
histories.

Every interior coefficient has the form

    X_i(j-1)+epsilon*(X_(i xor 1)(j-1)-D)-X_i(j),  (15)

where epsilon is 0,+1 or -1 according to the physical letter, with
at most one coordinate updated per cell. By (12), (15) lies strictly
between -3D and 3D, hence strictly between -B and B. Once the lower
coefficients are zero, another reduction modulo B forces this
coefficient to vanish. Induction recovers the exact four signed shear
recurrences after subtracting D. The final coefficient then forces
the terminal state (D,D+1,D,D+1).

This argument uses the certified range of both adjacent supplied
digits; it needs no estimate in terms of t and does not invoke the
old one-vector matrix-faithfulness lemma. Sound shifted digits may
equal zero, which simply represents the valid signed value -D.
The terminal signed vectors are e2, proving soundness for (3).

## 6. Strictly positive completeness

Suppose a genuine macro word satisfies (3). Add hub idles if necessary
to obtain t>=1. Choose any sufficiently large power of two D with

    D>u, D>every absolute signed history coordinate, 8D>m.

Set rho=D-u>0, B=8D, P=B^t and J as in (11). Use the actual shifted
histories, edge indicators, computed physical selectors and products.
Every shifted digit is strictly between 0 and 2D, so each H_i>0.
At each cell their four-digit sum is below 8D=B; hence sum H_i<P and
the positive history_bound in (8) exists.

There is at most one active physical selector per cell. Therefore

    sum_i Z_i <= (2D-1)J,
    selection_bound=P-7-sum_i Z_i >= 6DJ-6>0.       (16)

This works also for t=1. All edge and product hats are positive,
including unused fields; radix_beta=B-m>0. Equations (10) hold for
the genuine data, and (9) bounds all regions, so the entire joined
AND is correct at scale 16N. Its truth prefix includes all four
classes, and the exact positive converse supplies F0,F1,F2 and every
remaining positive native auxiliary at this actual scale.

There is only one native extension to choose. No geometry-core
witnesses, hidden input code, additional selector-typing relation or
duration counter remain. Together with the genuine recurrences and
controller equations this supplies all positive coordinates of the
new certificate. The proof establishes equality of accepted inputs
with (3); it does not assert a bijection with the parent's different
matrix-endpoint witness tuples.

For the universal corollary, use the fixed subgroup and fixed macro
alphabet in the lower-projective theorem. Its program numerals are
alpha=12*2^(p_program+1) and beta=12*2^p_program; these are precomputed
constants. The two-gate affine prefix in (4) is fully paid for every
ordinary positive x. Program exponentiation is not a runtime operation.

## 7. Literal source, costs and degree

The [source](group_range_projective_compiler.py) starts from the exact
computed-port DAG. It removes the 47 geometry gates and their 13
comparisons, replaces the ten-gate old boundary (4M+6A) by (4), and
adds (7). A stable topological sort makes every redirected operand
available without adding arithmetic. The changes are

    -47 + (6-10) +14 = -37 gates = -21M-16A.

The 19 supplied geometry auxiliaries disappear; q_geom is replaced by
rho, leaving m+40 positive witnesses. All 26 retained comparisons are
present: five history/bound checks, 17 selector/output checks and four
controller checks. Removing geometry is justified by Sections 3–6,
not by deleting its obligation without replacement.

Let delta_M,delta_A be the inherited common-expression savings:
(1,2) for h=1, (3,3) for h=2 and (5,4) for h>=3. Then

    certificate_M=m+2h+80+f_M-delta_M,
    certificate_A=2m+h+p+105+f_A-delta_A.            (17)

The 26 residual subtractions, 26 squares and 25 sum additions cost
26M+51A=77, giving

    polynomial_M=m+2h+106+f_M-delta_M,
    polynomial_A=2m+h+p+156+f_A-delta_A.             (18)

Equations (17)–(18) prove (1)–(2), since delta_M+delta_A=3min(h,3).
The checker records the actual instruction lists, not only formulas.

For total degree, all supplied coordinates have degree one and compiler
numerals degree zero. Set s_degree=m+18, the degree of q_sel=16P^(m+18).
The unique highest residual is the first native norm; its highest form is

    w_selection^2*s_selection^4*k_selection^2
        *(16P^(m+18))^6,                           (19)

of degree 6m+116. In particular, the native packed index r remains a
supplied independent variable when degree is measured. H,M have degree
at most m+17 and Z has degree m+16; thus the packed four-class index
comparison has degree at most 3(m+18)+(m+16)=4m+70. The other
q-dependent native comparisons have degree at most 2m+39; remaining
native norm/auxiliary comparisons have degree at most ten. History,
flow and port comparisons are also strictly lower. These bounds follow
directly from the retained native formulas, with no zero-set
substitutions such as P=B^t. Hence (19) is nonzero and unique at the
highest degree. Squaring gives exact degree 12m+232 with highest form
equal to the square of (19).

## 8. Reproducible checks and their scope

The [receipt](group_range_projective_compiler.json) includes four full
fixed-table DAGs with m=2,4,8,16, their comparison lists, positive
coordinate lists, deleted geometry and boundary gates, added range
gates, and exact certificate/SOS ledgers.

The checker compares all 26 residuals with a separate direct expansion
on 1,024 arbitrary assignments, including 256 signed assignments, and
checks the complete SOS and new joined regions. Its native manual
formula includes the original strong-auxiliary correction rather than
silently using an equation to simplify an off-zero residual. Weighted
offset univariate evaluations verify the actual DAG's degree and
highest coefficient for all four tables.

Another 512 scalar fixtures verify pretyping bounds without assuming
a dyadic radix, and 512 genuine Boolean fixtures check all four joined
AND relations, canonical zero digits and the positive global bounds.
The two omitted-region counterexamples in Section 3 are replayed.
Four accepted physical-word fixtures construct the genuine signed
histories and all positive outer fields, then verify the retained
outer comparisons. Their native core values are explicitly placeholders:
the astronomical full Pell extensions are established by the exact
positive theorem, not falsely claimed as materialized finite tests.

Run the source normally to check the deterministic receipt; use
`--write` to regenerate it. Parent packets remain unchanged.
