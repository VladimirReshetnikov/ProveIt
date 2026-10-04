# Joint current/target recoding for the two U21 interfaces

The [complete sources and receipt](residue_affine_sparse_joint_recoding.json)
give **467=171M+296A** for the one-program interface and **466=171M+295A**
for the two-program interface. Both retain **67 positive witnesses**. The
uniform degree bounds remain **5091** and **5160**, respectively. Each
successor saves one addition and has exactly the supplied positive integer
zero set of its own immediate parent, on that parent's valid fixed-program
recipes. The two different interfaces are not identified with each other.

The [fresh standalone checker](residue_affine_sparse_joint_recoding.py)
reads authenticated predecessor bytes and JSON as inert data. It neither
executes nor imports predecessor code. The new schedules share a paid
current/target coefficient product and reuse a remainder-selector prefix.
They change three state codes. Consequently the whole polynomials satisfy
an explicit all-ring correction; they are not identical polynomials.

## 1. Separate interfaces and the actual retained base

The immediate parents are [recoded468](residue_affine_sparse_recoded468.md)
and [recoded467](residue_affine_sparse_recoded467.md). The former has fixed
program parameter E=3^e, ordinary positive input x, and positive height
slack eta. Its literal rows remain

    height_83 = program + input
    height_85 = height_83 + height_slack
    radix_86 = 64 * height_85.

Thus h=E+x+eta>=3 and B=64h>=192 even before imposing equations. There
are 69 supplied ports: E, x, and 67 positive witnesses. The latter has
two fixed positive program parameters E,C, with E=3^e, C dyadic, C>=64,
and C>E. Its literal rows remain

    height_85 = input + height_slack
    radix_86 = radix_program * height_85.

Here h=x+eta>=2 and B=Ch>=128. There are 70 supplied ports, including
the additional fixed parameter C. These are restrictions on the effective
fixed-program recipe, not omitted polynomial comparisons. In particular,
C is not a witness that varies with x. No claim on other fixed slices is
made. The primary distinct-interface proof is
[program_radix504, Sections 1–4](residue_affine_sparse_program_radix504.md).

For each parent the checker takes the actual ancestor closure of
`sparse_all_units` and `norm_residual0,2,3,4,5`. These are the unit product
and the five noncontrol residuals. The resulting retained base contains
389=142M+247A or 388=142M+246A rows. Every base definition remains literal.
It includes shared pair sums whose names mention control but whose values
are needed by prime selectors or the population sum. None is deleted on
the basis of its name. All 72 `native__` rows remain literal.

The actual table is the saved 21-instruction U21 program with assigned
primes (5,3,2,7,11,13,17,19). The checker reconstructs all 36 edge tuples,
including their actions, primes and payload coefficients, from that table,
and compares them to the pinned literal edge data and both parents. State
0 is the loader, states 1–21 are body states, and 22 is halt. The two
loader edges are 0->0 and 0->1. Every supplied selector is expanded through
the literal definition E_i=`edgei_hat-1`.

## 2. The selected codes and two complete control words

The old immediate-parent codes in state order 0,...,22 are

    0,1,15,21,9,17,13,11,5,18,8,25,41,32,10,3,12,4,24,2,6,7,14.

The new codes are

    0,1,15,21,9,17,13,11,5,18,8,38,30,32,10,3,12,4,40,2,6,7,14.

They are injective, give loader code 0 and halt code 14, and put every
other code in [1,40]. Only states 11,12,18 change, by +13,-11,+16. Both
code lists are below either lower bound for B. This is one selected valid
finite plan, not a minimum over code assignments or arithmetic circuits.

Let G_p be the selector of edges using prime p, I the increment selector,
L=E0+E1, and D_q the selector of edges leaving state q. The prime weights,
including the unchanged zero weight at prime 2, are

| p |2|3|5|7|11|13|17|19|
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| w_p |0|1|2|3|8|9|17|11|

The increment coefficient is 4. The only nonzero state corrections are

    d9=1, d11=29, d12=21, d13=32, d14=1, d18=32.

The body code at state q is w_prime+4*[increment]+d_q. The complete
current-control word is therefore

    C_new = sum_(p>2) w_p G_p + 4(I-L)
            + D9+D14+29D11+21D12+32(D13+D18).          (1)

For the target word use the following paid selector basis. Each vector is
recovered by exact expansion of literal retained-base additions.

| Register | Selector | Coefficient |
|---|---|---:|
| `selectors_70` | J=sum_(i=0)^35 E_i |1|
| `action_selector_126` | E2+E6+E8+E11 |4|
| `prime_selector_111` | E5+E8+E9 |1|
| `control_codes__duplicate_state_2` | E18+E19=D11 |29|
| `control_codes__duplicate_state_8` | E24+E25=D14 |1|

Subtract these vectors, with the displayed coefficients, from the vector
of new target codes. The complete residual coefficient vector is

    -1,0,10,20,0,7,16,16,7,7,10,0,17,16,7,0,0,37,
    0,2,9,2,39,1,10,2,39,5,37,6,0,13,0,39,0,39.

The target-control word N_new is the displayed paid-basis combination
plus sum_i r_i E_i for that vector. Grouping equal coefficients and
interning equal exact selector vectors determines a binary schedule; no
linear combination is treated as a free runtime primitive. All scalar
multiplications, including coefficient 29, are charged when used unless
their actual result is already paid and live.

In particular, the product

    joint_12 = 29 * control_codes__duplicate_state_2

is shared by C_new and N_new. The coefficient-2 remainder group uses

    joint_26 = remainder_total_coefficient_group_160 - edge_7,

because the paid prefix is E7+E19+E21+E25. It therefore gives
E19+E21+E25 in one subtraction. The current word also retains the paid
identity G3+2G5=(G3+G5)+G5. The compiler trims the two provisional dead
rows `joint_4` and `joint_25`, then schedules the complete live source.

The helper expands all four old/new words through the 36 actual supplied
hats, including their constant terms. It verifies every source and target
coefficient against the corresponding actual edge label. The source
interfaces are C_new=`joint_24`, N_new=`joint_61`, 14P=`joint_62`,
B*N_new=`joint_63`, and C_new+14P=`joint_64`.

## 3. Every operation and supplied port is paid

The old current and target words have disjoint private ancestors outside
the retained base. The new words share the single product `joint_12`.

| Word ancestors outside the retained base | M | A | Total |
|---|---:|---:|---:|
| Old current |8|15|23|
| Old target |12|26|38|
| Old union |20|41|61|
| New current |9|15|24|
| New target |12|25|37|
| New union, counting the shared product once |20|40|60|

Three further control producers evaluate B*N, 14P and C+14P at 2M+1A.
The control-residual subtraction is counted in the remaining finalizer.
Thus the private control schedule decreases from 64 to 63 rows.

| Disjoint live stage | One-program M,A,total | Two-program M,A,total |
|---|---|---|
| Retained base, including five noncontrol residual producers |142,247,389|142,246,388|
| New private control producers |22,41,63|22,41,63|
| Remaining finalizer rows |7,8,15|7,8,15|
| Complete successor |**171,296,467**|**171,295,466**|

All 933 rows across the two complete sources are live, and all original
supplied ports are live. The source adds no witnesses. There are 20
comparison/finalizer rows in total, five already included in the base;
their aggregate cost is 7M+13A. Excluding all 20 gives certificate costs
447=164M+283A and 446=164M+282A, each with seven comparisons and 67 positive
witnesses in the inherited convention. The complete polynomial costs
above include those comparisons and finalization.

The separately reconstructed arrays differ literally only by deleting
`height_83` and changing the two height/radix rows in Section 1. This
structural check does not assert a positive-coordinate map between their
different supplied interfaces.

## 4. Exact correction for the entire polynomial

With all quantities evaluated at the same supplied coordinates, write
delta_C=C_new-C_old and delta_N=N_new-N_old. Exact expansion gives

    delta_C = 13(E18+E19)-11(E20+E21)+16(E30+E31),
    delta_N = 13(E17+E28)-11E18+16(E22+E26+E33+E35).    (2)

The halt code remains 14. Consequently, for the actual control residual
r=B*N-C-14P,

    delta_r = r_new-r_old = B*delta_N-delta_C.           (3)

Let U=`sparse_all_units` and S be the sum of squares of the other five
actual residuals. Both complete finalizers expand to

    F_old=U*(1+S+r_old^2)-1,
    F_new=U*(1+S+r_new^2)-1.

Thus, over every commutative ring,

    F_new-F_old = U*(2*r_old*delta_r+delta_r^2).          (4)

These are source-bound identities. U and the other five residuals have
identical literal upstream closures. The four word expansions are bound
to the actual hats, and the three control producers plus residual are
guarded literally. The checker expands the complete formal finalizer,
then binds every cut to these equal or explicitly corrected computed
values. Nineteen of the 20 comparison/finalizer rows are unchanged. There
is no digest-only assumption of equality of unexamined boundary values.

## 5. Identical positive zeros within each interface

Fix a valid recipe from Section 1. At a supplied positive integer zero
of either old or new source,

    U*(1+sum_(j=0)^5 residual_j^2)=1.

The second factor is a positive integer. Hence U=1 and all six residuals
vanish. The integer native and repunit factors of U are units.

The precontrol bootstrap uses only unchanged rows. For the one-program
case, use [scale538, Sections 2–3](residue_affine_sparse_scale538.md),
[terminal537, Section 2](residue_affine_sparse_terminal537.md), and the
[control-code505 proof](residue_affine_sparse_control_codes.md). For the
two-program case, use the explicit h>=2 bootstrap in
[program_radix504, Section 2](residue_affine_sparse_program_radix504.md).
It uses C>=64, C>E, the remainder equation, positive computed scale,
range/selection information and the native equations; it does not use
control-state chronology. In either case it yields

    B dyadic, P=B^T, J=1+B+...+B^(T-1), T>=1,

and a one-hot edge at each time position, with the inherited action,
prime and range typing. In particular, this bootstrap is available at a
zero of either recoding before deciding its control equality. There is
no use of the old zero-set theorem to assume the new chronology.

For a typed edge word i_0,...,i_(T-1), both control words have canonical
base-B digits. Every old or new code is nonnegative and strictly below
B. The equality B*N=C+14P is therefore equivalent, by comparing the
T+1 base-B digits, to

    code(source(i_0))=0,
    code(target(i_j))=code(source(i_(j+1))) for j<T-1,
    code(target(i_(T-1)))=14.

Each code list is injective. Both impose exactly the same initial loader
state, adjacent control states and final halt state. Thus at a new zero
the old control equality holds on the same supplied coordinates; all
other equations and U already agree, so the old polynomial vanishes.
The converse follows identically. No re-selection of native witnesses,
payload witnesses, height slack, selectors or other supplied coordinates
is needed in either direction **within the same interface**.

The graph has no return from the body to loader state 0, and the two
loader edges, payload transport and prefix-count equations are unchanged.
The inherited ordinary-input theorem therefore transfers through this
same-coordinate zero-set equivalence. It retains the paid number of
initial loader doublings x and the actual fixed U21 execution. Native
completeness is inherited through the parent theorem; the finite checks
below do not purport to construct native Pell witnesses. The valid
fixed-program parameter conditions remain exactly those in Section 1.

## 6. Degree, finite evidence and limits

The control words are affine in the supplied edge hats. Their new
residual has degree at most 2 in the one-program interface and at most 3
when the second supplied program parameter C is counted as a variable.
The literal native main-norm cone is freshly expanded at its actual
computed boundaries as

    (X+ac+G)^2-(a^2+4a+3)c^2
      = X^2+2acX+2GX+2acG+G^2-4ac^2-3c^2.

The boundary degree bounds (X,a,c,G) are (308,374,67,375) and
(312,379,68,380). The expanded norm has bounds 816 and 827, improving
the naive 882 and 894. Propagating these guarded bounds through every
actual new row gives product-U bounds 4993 and 5062. The outer sum of
squares has bound 98, so the full bounds are 5091 and 5160. Naive
gatewise propagation would give 5157 and 5227. These are uniform upper
bounds, not exact-degree assertions.

The receipt saves both full arrays, complete free-port lists, the full
U21 table and all 36 edge tuples, both code lists, all paid-basis vectors,
actual-hat word expansions, exact control/output corrections, degree
expansions, and complete source/liveness/count checks. It also contains
64 signed whole-source modular comparisons, 32 per interface, at two
primes. These check every retained base value and (4) and supplement
the exact proof; numerical agreement is not used to certify identity.

Another 236 finite control words include 36 chronological words covering
every edge and 200 deterministic random words. Old and new code equations
are compared to actual adjacency at bases 128,192,256, for 1416 exact
integer checks. These words are control fixtures, not accepted payload
computations or complete native zero tuples. The selected schedule came
from a bounded exploratory search, but no exhaustive optimization theorem
or arithmetic lower bound is asserted. No claim concerning a universal
polynomial below 84 operations follows from this result.

The helper authenticates eleven inert dependencies: both immediate
parent trios, the saved factored-table JSON, and the four primary proof
texts named above. Their full SHA256 values are in its `PINS` dictionary
and receipt. The immediate-parent source-array bindings are also checked,
and canonical in-memory copies remain unchanged. All guards remain active
under Python optimization. Receipt creation is exclusive; replay requires
exact type-sensitive equality with the saved receipt.

Fresh normal and `python3 -O` exact replays from `/` both passed using
`--root` for the authenticated WIP directory and `--expect` for the saved
receipt. The replay binds the helper bytes as well as the complete result.
The frozen helper SHA256 is
`386f00228dd250a1c582a3bf93724e9732db71cdd8d4fea6828d0b78d06fe443`;
the receipt SHA256 is
`a3b00883d84e7c8e9a6aea04ec3e54776fe927f7193f60a04050246f32039284`.

