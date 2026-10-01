# Freezing duplicate idle selectors removes paid packing arithmetic

The power-of-two macro table contains redundant copies of its hub idle
edge. Their positive edge hats can be fixed to one, making their actual
selector words zero. Two explicit packing plans compile these fixed
lanes without changing the paid mask or scale geometry.

For the illustrative ten-letter table, this saves **4 multiplications,
8 additions and 5 positive witnesses** from the
[shared-flow compiler](group_projective_shared_flow_target.md). Its joint
variant now costs **247 certificate / 264 polynomial operations**, with
polynomial split **113M+151A**, six comparisons, 37 positive witnesses
and exact degree **3504**.

Every new output is the exact parent polynomial specialized at the fixed
hats. The accepted positive ordinary-input relation is also unchanged,
by a separate path-normalization and positive-extension proof. This is
not a bijection with all parent witness tuples. No numerical universal
alphabet is instantiated, and the separate universal 75/88 bounds remain.

## 1. The fixed lanes and the positive input equivalence

For fixed nonempty macro codes, with the empty list also allowed, put

    a=1+sum length(code), m=2^h>=max(2,a), k=m-a,

where m is the least admissible power of two. The actual
[macro-table constructor](group_regular_macro_controller.py) places the
canonical idle edge `(0,0,0)` at index zero, followed by all macro path
edges at indices1 through a-1. Each macro edge has physical label1
through8. The final k edges are exact copies of `(0,0,0)`.

For every padded index e>=a, specialize

    Ehat_e=1, so E_e=Ehat_e-1=0.                         (1)

All remaining coordinates keep their strict positive domain. In
particular the canonical edge0 remains available, including for the
empty macro list. We retain the original m, h, all fixed program
constants, radix bound, scale exponent, and full m-lane origin mask.
This packet neither reduces the alphabet geometry to a lanes nor
requires every remaining edge to occur.

Soundness is immediate after the exact source identities below: restore
the removed hats to one. Every positive new zero becomes a positive
parent zero with the same input, histories and all other coordinates.
The parent full fixed-table theorem gives the desired endpoint.

For completeness, take an accepting parent path. Replace every use of a
padded edge by edge0. The source, target and physical letter of each
replaced edge are identical, so this is still a hub-to-hub path of the
same length with the same physical trajectory. Its edge words satisfy

    E'_0=E_0+sum_(e>=a) E_e,
    E'_e=E_e for 1<=e<a, E'_e=0 for e>=a.              (2)

The old one-hot partition means the sum in (2) remains a Boolean
radix-B word: its summands occupy disjoint positions. The edge checksum,
state flow and all eight physical ports are unchanged. In particular
the histories, selected-source words, ordinary affine input, height,
length and positive joint-bound slack can be kept unchanged.

The packed controller edge word changes, so this argument does **not**
keep arbitrary old native Pell coordinates. Instead, form the joined
AND instance from the new controller word and the unchanged physical
data. Its upper controller lane still satisfies the same subset
relation against the full origin mask. All lower selection, range and
radix regions are unchanged. The prescribed AND converse supplies all
positive native coordinates at the same paid scale. The subsequent
positive coordinate maps and unit merges are exactly those in the
reviewed parent completeness theorem. Thus a new positive zero exists
for the same ordinary input.

Equivalently, the parent canonical completeness construction may choose
edge0 for every idle from the outset. Its native truth-class padding is
independent of whether these controller lanes are used. Zero padded
lanes therefore do not remove any required positive truth-class field.

## 2. Exact checksum and packed-word specialization

The supplied edge hats enter the source through its edge pack, grouped
checksum and physical/state projections. A padded hat has only two
consumers: its hub checksum sum and its edge-pack gate. Label zero is
absent from the eight physical ports, and both state coefficients are
zero. The source audits these facts against the actual incoming DAG.

The padded hats are the final k terms of the hub group. Remove those
terms from its sum and replace the computed repunit definition by

    J=sum_(e<a) Ehat_e-a.                              (3)

Under (1), this is precisely the parent's
`sum_(e<m) Ehat_e-m`. It removes k additions. All earlier partial
checksums shared with the sparse flow target remain unchanged. When
the hub is the only group, the same identity applies directly; no
empty sum or fresh coordinate is introduced.

Write

    R_n(P)=1+P+...+P^(n-1).

The parent controller word is

    Hc=sum_(e<m) Ehat_e P^e-R_m(P).

After (1), it equals exactly

    Hc=sum_(e<a) Ehat_e P^e-R_a(P).                    (4)

This follows from `R_m=R_a+P^a R_k`, as a polynomial identity for
every integer P. Neither positivity nor binary/radix typing is used.
The full mask `J R_m(P)` is retained: the a remaining selector lanes
are placed inside the original m-lane region, with the others zero.

Two paid literal plans evaluate (4).

* **Trim:** Horner-pack the a live hats and subtract R_a.
* **Tail:** start Horner packing from R_k, append the a live hats in
  descending index order, and subtract the already paid R_m.

The tail evaluates the original m-lane positive-hat pack with its
fixed suffix compressed; the trim evaluates its canceled form (4).
The source emits both candidates and selects the cheaper one, breaking
ties by multiplication count and then a fixed lexical rule. This is
optimization within two explicit plans, not a minimal circuit claim.

## 3. Every repunit operation is charged

The incoming compiler already contains P^(2^j) and R_(2^j) through m,
because its original m-lane mask and scale remain necessary. For
`n=2^j+r`, with0<r<2^j, use

    R_n=R_(2^j)+P^(2^j) R_r.                         (5)

The product is a register copy when r=1. The base R_1 is the fixed
integer one. Every other product and addition is paid. Recursion gives
the exact new-gate counts

    A_R(n)=popcount(n)-1,
    M_R(n)=A_R(n)-[n>1 and n odd].                    (6)

Existing power/repunit registers and their defining instructions are
checked explicitly before reuse. Multiplication by a varying P is
never treated as free. No quotient formula for R_n is used.

For k>0, the respective savings over the full parent certificate are

| Plan | Multiplications saved | Additions saved |
|---|---:|---:|
|Trim|k-M_R(a)|2k-A_R(a)|
|Tail|k-1+[k=1]-M_R(k)|2k-1-A_R(k)|

These include the k checksum additions. When k=0 the source is
unchanged. For every k>0 the chosen plan saves at least **2k operations**.
For k=1 the tail saves exactly two. For k>=2, (6) implies

    M_R(k)+A_R(k)<=k-2.

Indeed, for k=2j the left side is2 popcount(j)-2<=2j-2; for k=2j+1
it is2 popcount(j)-1<=2j-1. Thus the tail's total saving
`3k-2-M_R(k)-A_R(k)` is at least2k, and choosing the better plan can
only improve it. Some near-power cases favor the tail: computing a
new R_(m-1) alone need not be profitable.

Let Delta_M and Delta_A be the audited savings, and Delta their sum.
Every finalizer is unchanged, so its whole polynomial saves the same
Delta_M multiplications and Delta_A additions. The positive-witness
count decreases by k, and the comparison count is unchanged.

For the joint parent, retain its notation

    C=3m+3h+p+185+f_flow-3min(h,3)-epsilon,
    s=port-bias saving, theta=[some macro length>=3].

The resulting certificate costs `C+3-s-theta-Delta`, and the polynomial
costs `C+23-3chi-s-theta-Delta`. There are `7-chi` comparisons and
`a+27-chi` positive witnesses. The same literal rewrite is also audited
on the four-field, unshifted six-field, shifted-X and strong-unit
parents: subtract Delta and k from their respective operation and
witness counts, leaving their comparisons unchanged.

For the ten-letter table, a=11,m=16,k=5. Both plans save4M+8A. The
deterministic tie chooses the tail, using `R_5=R_4+P^4` at one new
addition. Its joint options are:

| Mask reuse | Computed P | Certificate / polynomial | Polynomial M / A | Comparisons / witnesses | Degree |
|---|---|---:|---:|---:|---:|
|Yes|Yes|247 / 264|113 / 151|6 / 37|3504|
|No|Yes|248 / 265|114 / 151|6 / 37|2928|
|Yes|No|247 / 267|114 / 153|7 / 38|1774|
|No|No|248 / 268|115 / 153|7 / 38|1486|

Other tables of the same total length can have different port and flow
costs; the receipt records the actual codes with each ledger.

## 4. Exact degree is preserved

Specialization cannot increase polynomial degree. To prove it does not
decrease it here, specialize the already proved parent highest forms.
Replacing a hat by the constant one sets its degree-one homogeneous
part to zero. Write

    J*=sum_(e<a) Ehat_e*, D*=alpha*x*+height_slack*.

The native highest forms depend on the removed edge hats only through
the old J*. It is now the displayed nonzero linear form. Computed P
still has the nonzero degree-two highest form `16D*J*`; supplied P
is unaffected. All scale exponents and mask powers still refer to m.
The highest native factors in each parent therefore survive unchanged
apart from this substitution.

For the strong/joint parents, let d_i* be the signed physical-port
difference. Removed idle edges contribute zero to every d_i*, so these
forms are unchanged. With computed P the four highest history residuals
are `-16(D*)^2(J*+d_i*)`. At positive leading weights, the retained
edge0 term makes `J*>|d_i*|`, so all four are nonzero. With supplied P
and a nonempty macro list, at least one signed-port form is a nonzero
polynomial: its edge variables are distinct and some physical edge
occurs. The sum of squared highest history forms cannot vanish as a
polynomial. The idle-only supplied-P case retains the parent's separate
degree-two outer formula, with edge0 still free.

Finally the joint unit highest form is `-P*` for computed P, or
`sum H_i*+sum Zhat_i*+bound_global*-P*` for supplied P; both survive.
Thus all exact parent degrees persist. In particular the joint degree is

    nu(36L+7m+106)+38+2d_outer,
    nu=1+chi,
    L=m+18 if epsilon=0, L=2m+10 if epsilon=1,
    d_outer=3 except idle-only supplied-P tables, where it is2.

The source's highest-form function calls the parent formula with zero
weights for the fixed hats. Its ledger checks use positive live weights,
including distinct powers of two on live edges, to avoid accidental
cancellation in a signed-port specialization. No zero-set equation is
used to estimate an off-zero degree.

## 5. Executable audit and evidence boundaries

The [source](group_projective_frozen_idle_padding.py) reconstructs the
old full edge Horner pack and the relevant hub checksum from their
literal instructions. Every removed register's consumers are audited;
none may occur in a comparison or escape the private fragment. The
checksum's changed private total differs by k, while its output J and
every downstream value are identical after specialization. Both paid
packing plans are checked independently, and topological sorting checks
every register dependency in the emitted source.

The compact [receipt](group_projective_frozen_idle_padding.json) stores
150 option ledgers and one full illustrative source/finalizer. On3,600
assignments, including1,200 signed assignments, it compares every
surviving register outside the intentionally changed checksum total,
every residual and the complete polynomial to the parent with exactly
the removed hats set to one. Direct sums independently check Hc and J.
Both pack candidates are also replayed, including the unchosen plan.

Another256 actual path normalizations replace525 padded idle occurrences,
checking the unchanged physical/state trajectory, one-hot checksum and
the subset relation against the retained full mask. These are finite
outer word fixtures, not materialized native Pell solutions. Their
positive native extension is supplied by the cited converse theorem.
The elementary uniform saving inequality is additionally checked on4,084
power-of-two layouts.

Run normally to compare the deterministic receipt, or with `--write` to
regenerate it. The parent packets are unchanged and remain runnable.

The author writer and fresh default replay passed. An independent full
proof/source review and fresh default replay passed without findings,
including the positive native extension and all five degree families.
Another300 signed full-residual and complete-output specializations on
five independent code tables covered20 tail,20 trim and10 unchanged
configurations. These remain algebraic source checks, not full Pell
witness fixtures.
The root full proof/source review and fresh default replay also passed.
