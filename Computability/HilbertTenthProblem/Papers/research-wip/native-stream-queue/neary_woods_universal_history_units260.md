# Two positive history units give260 operations

**Successors:** the [lower-history unit259](neary_woods_universal_lower_unit259.md)
preserves supplied positive zeros on valid input slices; the
[offset-shifted258](neary_woods_universal_offset258.md) changes the fixed
program parameter to E−1 and preserves accepted inputs on the corresponding
valid slices. The separate [all-factor partition search](neary_woods_universal_history_unit_partitions.md)
keeps the older E semantics. This note retains its original260 theorem,
source and counts.

The [literal compiler](neary_woods_universal_history_units260.py) reduces the
complete [263-operation U9 polynomial](neary_woods_universal_mask_unit263.md)
to **260=134M+126A**, with **255 certificate operations=132M+123A**, two
comparisons,43 positive witnesses and the same four positive program
parameters. Its total-degree upper bound is3866. An upper-transport-only
intermediate costs261 operations and preserves the same positive zero set.
A mapped schedule costs270 operations with degree at most608 and44 witnesses.

The default uses a positive-zero bijection: the parent's private history
bound slack is the new slack plus one. Both directions are proved below,
including strict positivity of the inverse. The fixed U9 machine, numeral
recipes, ordinary-input loader, valid program slices and exact counter
initialization are unchanged. The separate75 certificate and87 polynomial
bounds remain unchanged. The [receipt](neary_woods_universal_history_units260.json)
stores the complete selected literal sources and their exact ledgers.

## 1. The two factors and their paid schedules

Use history notation D_h for its height, K_h for its fixed radix multiplier,
b=K_h D_h, J_h for its selector sum, and P_h=(b-1)J_h+1. The fixed actual
K_h is a power of two at least8, and D_h is a sum of four positive terms,
so D_h>=4 before any equation. Write NU,NV for the two paid history update
forms, U_f,V_f for the endpoints, and V_0 for the loaded input. The current
upper transport and global bound are

    b*NU+1 = H_U+P_h*U_f,
    H_U+H_V+ZUhat0+ZVhat0+ZVhat1+beta_old = P_h.       (1)

Both left and right sides are already emitted. Introduce

    N_U = H_U+P_h*U_f-b*NU,
    N_G = P_h-(H_U+H_V+ZUhat0+ZVhat0+ZVhat1+beta).    (2)

For N_U, delete the private register `hist__U_lhs__37=b*NU+1` and
replace its one addition by the subtraction of the already paid update
from the already paid right side. Multiply N_U into one existing group
and remove the upper comparison. This adds one certificate multiplication
and removes one squared comparison, saving two polynomial additions.

For N_G, retain `hist__global_lhs__15` with its positive supplied beta,
add one subtraction and one group multiplication, and remove the global
comparison. This saves one polynomial addition. No new coordinate is
introduced. The default uses both factors; each factor may be placed in
any of the old groups, including the same group or the unsquared anchor.

At a new positive zero, each old ordinary residual is zero and every
group product is1. This holds for the all-SOS finalizer and for an
integer anchor times one plus a sum of squares, minus one. Every integer
factor is therefore either1 or-1. If the global unit is enabled, write
N_G=delta_G in{1,-1}; then

    H_U+H_V+ZUhat0+ZVhat0+ZVhat1+beta=P_h-delta_G.     (3)

If it is disabled, the original global comparison remains.

The source reconstructs and checks the complete frozen263 parent,
including all outer rows, factor groups, domains, fixed-numeral roles and
nested active interfaces. It checks that the deleted upper-left register
has no source consumer or active export and that beta is consumed only
by the global sum. Historical parent records are retained as provenance,
not substituted for the new source or comparisons.

## 2. Bounds and both native indices before history transport

Equation(3) has six positive terms. Hence P_h>=5, and every history or
product hat is strictly less than P_h. The selector definitions still
have J_h=sum(Shat_i-1)>=0 and P_h=(b-1)J_h+1. Thus J_h>=1 and b<=P_h.
These are all the global-bound consequences used in the untyped high-port
proof of [computed fields](neary_woods_universal_computed_ports275.md),
Sections1--2. Its three strict margins still hold:

    H_h-Z_h>=1, M_h-Z_h>1,
    P_h^11-H_h-M_h+Z_h>=2.                         (4)

In particular its last estimate
P_h^11-2P_h^10-P_h^3+2>=2 remains valid for P_h>=5.
Neither history transport is used in these bounds.

The signed mask factor retained from263 gives
S=(2B-1)K+delta_M, delta_M in{1,-1}. Its already proved inequalities
BK<S and K+1<=S, together with the unchanged positive loader and duration
formulas, give the same strict low-port bounds as263. Therefore the
implicit four truth fields are positive, sum to q_joint-1, have residues
(1,4,2,8) modulo16 and lie below q_joint. Their packed index r_j is
unchanged and satisfies the same strict lower bound. This conclusion
uses neither native typing nor either new unit's sign.

Apply the local rank/step-down argument of the
[coupled native theorem](neary_woods_universal_joint_and_coupled.md),
Sections2--3, to each core. All safe norms are1; a retained ordinary strong
comparison or normalized strong factor restores its full strong equation.
Both positive ratios remain. The pretyping geometry and joint index/scale
bounds are unchanged, so both linear factors are1 and the raw population
theorem holds at the potentially shifted indices:

    Q=2^popcount(R+epsilon_g-1),
    q_joint=2^popcount(r_j+epsilon_j-1),
    epsilon_g,epsilon_j in{1,-1}.                  (5)

No old total-product relation between these signs is imported: the new
factors could have changed it. In particular (5) is available independently
of delta_M, delta_G and N_U.

First exclude epsilon_j=-1. Write q_joint=2^t. Its four fields are disjoint
base-q_joint blocks with sum q_joint-1, so

    popcount(r_j)>=popcount(q_joint-1)=t.

Also r_j=1 modulo16. The exact borrow identity gives

    popcount(r_j-2)=popcount(r_j)+v2(r_j-1)-2>=t+2,

contradicting(5). Thus epsilon_j=1, and the entire original joined AND
relation is restored, without using history chronology.

There is an independent exclusion of epsilon_g=-1 using the paid loader.
To distinguish it from history notation, let d be the fixed recoder width,
B its radix, P_r its first-repunit scale and J_r its repunit coordinate.
The literal source has

    d>=3, Q=(2^d-1)*rload+1, B=2^(d-1)*Q,
    P_r=(B-1)*J_r+1, S=q_input*P_r,
    R=(2^d-1)*J_r,
    q_joint=16*B*S*P_h^11.                        (6)

Every factor on the last line is a positive integer. Since q_joint is
dyadic, B,S,P_r and Q are dyadic. Write B=2^b_r and P_r=2^e_r. Here
P_r>1 and b_r>=d, because Q>1. The repunit equality implies b_r divides
e_r: reduce e_r modulo b_r in2^e_r=1 modulo(2^b_r-1). Consequently

    P_r=B^n, J_r=1+B+...+B^(n-1), n>=1.

The d one-bits in every cell of R are disjoint since b_r>=d. Its low
cell is2^d-1, so subtraction of2 deletes exactly one bit:

    popcount(R-2)=dn-1.                            (7)

If epsilon_g=-1, (5) would give Q=2^(dn-1). But the paid loader in(6)
requires Q=1 modulo2^d-1, whereas2^(dn-1) has residue2^(d-1), not1.
This contradiction proves epsilon_g=1. Both cores now have all their
original index, linear and norm factors equal to1.

## 3. Force both new signs and reconstruct a parent zero

The mask sign also has its independent263 proof. Since B and S are
dyadic, delta_M=-1 would require2^e=-1 modulo2B-1. For B=2^b, its
possible power-of-two residues are1,2,...,2^b, all strictly smaller than
2B-2 when b>=2. Hence delta_M=1.

The restored joined AND splits into the original low recoder and high
history regions, because the same strict low bounds and all disjoint
high-lane bounds have just been proved. The history top lanes give
b AND(b-1)=0, so b is dyadic. P_h is dyadic by(6), and its repunit
formula gives

    P_h=b^T, J_h=1+b+...+b^(T-1), T>=1.             (8)

The controller lanes give exactly one selected tile per time, and the
range lanes put every H_U and H_V digit in[0,D_h-1]. The proof of these
facts in the [slope-class history](pcp_affine_slope_class_history.md),
Section3, uses the native lanes and the scalar bounds, not the transport
equalities. In particular the least base-b digit u_0 of H_U lies in
that interval.

If N_U is enabled, reduction of(2) modulo b, using b dividing P_h,
gives N_U=u_0 modulo b. The value-1 would force u_0=b-1, impossible
because D_h<b-1. Thus N_U=1 and the original upper transport is restored.
If it is disabled, that transport was retained from the start.

All old factors and the mask unit are now1. If N_G is enabled, the group
containing it consequently forces N_G=1. Define

    beta_old=beta+1.                               (9)

This is always positive, and N_G=1 gives exactly the parent global
comparison in(1). If N_G is disabled, leave beta unchanged. Every old
group and every ordinary comparison now holds. All other supplied
coordinates are identical, so this is a complete positive parent zero.
The remaining lower transport has never been weakened or omitted.

## 4. Strictly positive converse on every parent zero

At any positive263 zero, the typed history has digit range[0,D_h-1].
Thus H_U,H_V<=(D_h-1)J_h. Its one upper and two lower exceptional
selector classes are disjoint within each coordinate. Therefore their
decoded selected words obey

    ZU0<=H_U, ZV0+ZV1<=H_V.

There are three positive product hats, so the actual old bound slack
satisfies

    beta_old=P_h-H_U-H_V-ZU0-ZV0-ZV1-3
            >=((K_h-4)D_h+3)J_h-2>=17.             (10)

This holds at every parent zero, not just a specially chosen canonical
history. It is the same range/class estimate used for completeness in
Section4 of the slope-class theorem. Since K_h>=8,D_h>=4,J_h>=1,
the last numerical bound is strict enough to set beta=beta_old-1>0.
All other coordinates are retained. Then N_G=1. The old upper equation
gives N_U=1 without changing a coordinate. Every new group is1 and
every retained comparison remains true.

Equations(9) and its inverse prove a full positive-zero bijection for
the default and global-only modes. The upper-only mode has identical
positive zeros on identical supplied tuples. These claims do not assert
an identity between off-zero polynomial values. The inherited universal
relation on the actual fixed program slices follows directly from the
complete parent theorem, with no new input or machine assumption.

## 5. Literal counts, degrees and corrected off-zero values

| Enabled factors | Certificate M+A | Comparisons | Witnesses | Polynomial M+A | Degree upper bound |
|---|---:|---:|---:|---:|---:|
| Upper only |253=131M+122A|3|43|261=134M+127A|3862|
| Global only |254=131M+123A|3|43|262=134M+128A|3861|
| Both |255=132M+123A|2|43|260=134M+126A|3866|

N_U has propagated degree5 and N_G degree4. The default group therefore
has degree3856, and the remaining lower transport has degree5, giving
3856+2*5=3866. These are conservative bounds from the actual emitted
source, with only the inherited guarded main-norm cancellation; no
identity valid just at zeros lowers a degree estimate.

For the displayed parent schedules, the compiler checks every placement
of the enabled new factors into their existing groups. The default
both-factor map yields:

| Operations | Degree upper bound | Positive witnesses |
|---:|---:|---:|
|260|3866|43|
|261|3450|43|
|262|3404|43|
|263|2286|44|
|264|1518|44|
|265|1472|44|
|266|1108|44|
|267|1062|44|
|268|740|44|
|269|708|44|
|270|608|44|

The separate fixed43-witness map reaches267/1344, and the fixed45 map
reaches273/608. Both program-bound interfaces are available. This is a
placement search within already selected inherited partitions, not an
exhaustive optimization of the enlarged factor family or an exact-degree
lower bound. The frozen263 and earlier finite-optimization results remain
available unchanged.

Here are exact whole-output correction identities. Evaluate the old
source after the lift(9), where enabled, and the new source on its own
tuple. Write G_j for the old group products, M_j for the product of newly
inserted factors placed in group j, and D for the sum of squares of the
removed old residuals. Each new factor equals1 minus its associated old
residual under that lift. For an all-SOS finalizer,

    P_new=P_old-D+sum_j((G_j*M_j-1)^2-(G_j-1)^2).

For an unsquared anchor a, put
C=sum_(j!=a)((G_j*M_j-1)^2-(G_j-1)^2). Then

    P_new=M_a*(P_old+1)+M_a*G_a*(C-D)-1.             (11)

These are integer polynomial identities on all supplied assignments,
including signed ones. They apply when both new factors share a group
or occupy separate groups, and avoid division by any possibly zero unit.
The source checks retained-register values under the lift, deleted/private
consumer guards, group-to-factor metadata, operation counts and complete
source closure.

## 6. Reproducibility and scope of finite checks

```sh
python3 neary_woods_universal_history_units260.py
```

The receipt records340 ledgers:96 one-group base/interface/mode choices
and244 two-factor placements into44 distinct selected parent/interface
sources. It saves44 selected complete polynomial schedules. Its1,744
whole-output/register/group correction identities include872 signed
assignments. Seven incompatible callers exercise the strict full-parent
source/domain/consumer/export guards.

The additional76 positive actual-source outer fixtures include all four
mask/global sign pairs, with38 negative mask and38 negative global signs.
They satisfy those two signed relations and check every reconstructed
positive truth field before native typing; they are not full Pell zeros.
Another32 actual-source high-history fixtures use synthetic fixed affine
coefficients and durations1 through4, checking upper chronology, high
AND, both new unit values and the positive slack inverse. They are not
full universal zeros. Elementary audits check448 negative-geometry
population/loader residues,84 upper-unit digit cases and108 typed slack
bounds. The unbounded theorem rests on the proof, not these finite tests.

Author receipt generation and the final fresh default replay pass. Root independently reviewed the full proof, source and inherited dependencies and passed a fresh default replay. A separate literal executor and manual slack lift checked1,056 complete register/output corrections,528 signed, over132 contexts spanning44 parent schedules and all three modes. Gibbs independently reviewed the full proof/source and passed a fresh default replay; his own executor/manual lift checked216 complete output/register/group corrections,108 signed, across18 mode/placement/interface contexts, plus96 negative-geometry population/loader residues at four further widths. These are algebraic and component checks, not materialized full Pell zeros. Neither review found a remaining issue. All six local links and the whitespace check pass. The trio is frozen; no frozen parent or shared navigation file is changed by this packet.
