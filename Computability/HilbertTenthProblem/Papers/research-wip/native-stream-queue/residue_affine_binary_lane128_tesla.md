# A complete binary residue-affine history in 128 operations

For the fixed shortcut Collatz map, delete the redundant second selector
AND lane from the complete packed-history source. The resulting polynomial
costs **128 = 61M + 67A**, has **21 strictly positive witnesses**, and has
ordinary total degree **at most 586**. For positive ordinary inputs `x,y`,
it has a positive zero exactly when `f^T(x)=y` for some integer `T>=1`.
The horizon is unbounded and is not an additional supplied parameter.
The zero-step option costs **130 = 62M + 68A**, with the same witnesses
and degree at most 587.

This is a six-operation saving from the existing 134-operation history
construction, using the same complete native Pell kernel. It does not
prove Collatz termination, Collatz universality, or a new numerical
universal Diophantine bound. The reduction is a change of the packed host
interface, with fresh native witnesses when necessary.

## 1. Fixed map, source lineage and all supplied coordinates

The inherited shifted residue table is `((3,2),(1,1))`:

    n=2v+1  => f(n)=3v+2=(3n+1)/2,
    n=2v+2  => f(n)=v+1=n/2,       v>=0.

The external inputs `input=x` and `target=y` are positive integers. The
six positive outer witnesses are

    edge0_hat, edge1_hat, quotient_hat, product0_hat,
    height_slack, global_slack.

Write the first four minus one as `E0,E1,W,Z`, respectively, and write
`eta=height_slack`, `beta=global_slack`. The literal paid definitions are

    J=E0+E1, h=x+y+eta, B=8h, P=(B-1)J+1,
    Rmask=(h-1)J, Mclass=(B-1)E0,
    N=W+2Z+J+E0, C=2W+J+E1.                         (1)

The unchanged ordinary outer comparisons are

    J+(W+1)+(Z+1)+beta=P,
    B*N+x=C+P*y.                                   (2)

The fifteen remaining positive witnesses have literal names

    native__F0, native__F1, native__F2,
    native__odd_half, native__bound_beta,
    native__eta, native__zeta, native__f, native__o,
    native__y_aux, native__h, native__ga, native__i,
    native__j, native__tau_gap.

These are distinct from the six outer witnesses; in particular the native
`h` is not the computed outer height in (1). No selector, quotient,
duration, initial-state exponent, or packed word is supplied without its
listed defining arithmetic or paid native relation. Numeral products by
2, 4, 8 and 16 remain charged.

The parent is `residue_affine_packed_history.json`, default 134-row source,
with its complete proof `residue_affine_packed_history.md`. Its coupled
native extension is `native_binary_index_coupled_units.md`. The existing
`native_controller_boolean_pairs56.md` already develops complementary
Boolean streams in another native encoding. The elementary complement
fact used below is not claimed new; its application removes an actual
lane from this fixed-arity history source.

## 2. Three lanes, the exact deletions and the paid scale

The parent's four lanes, least significant first, are

    (E0,J,E0), (E1,J,E1), (W,Mclass,Z), (W,Rmask,W).

Keep only the first, third and fourth. Their joined integers are

    H3=E0+P*W+P^2*W,
    M3=J+P*Mclass+P^2*Rmask,
    A3=E0+P*Z+P^2*W.                               (3)

Use the scale `Q=B*P^3`. The two existing power gates now compute `P^2`
and `P^3`, followed by the retained multiplication by `B`. The prescribed
native ports are

    native__q=16Q,
    padded_A=16H3+12, padded_B=16M3+10,
    native__F3=16A3+8.                              (4)

Delete precisely these six parent rows:

    joined_H_sum_30 = edge_1 + joined_H_shift_29
    joined_H_shift_31 = scale_10 * joined_H_sum_30
    joined_M_shift_38 = scale_10 * joined_M_sum_37
    joined_M_sum_39 = selector_sum_2 + joined_M_shift_38
    joined_Z_sum_42 = edge_1 + joined_Z_shift_41
    joined_Z_shift_43 = scale_10 * joined_Z_sum_42

Replace three consumers by

    joined_H_sum_32 = edge_0 + joined_H_shift_29
    native__scaled_B = 16 * joined_M_sum_37
    joined_Z_sum_44 = edge_0 + joined_Z_shift_41

and replace the power row by

    scale_power_46 = scale_power_45 * scale_10.

There are no new producers. The 79-row tail beginning at the parent's
`native__input_A` is literal unchanged, including all native factors and
the entire finalizer. The `P^4` control variant retains the old power row
but makes the same lane deletion; it also costs 128, with degree at most
722. The principal `P^3` version has 124 literal retained rows and four
edited rows; the control has 125 literal retained rows and three edits.
Both have all 128 producers and all 23 supplied ports live.

Each deleted pair costs 1M+1A. Thus the certificate goes from
`120=59M+61A` to `114=56M+58A`, still with five comparisons in the inherited
certificate convention (four ordinary comparisons and the native unit
product comparison). Its unchanged fourteen-operation polynomial tail
costs 5M+9A. The complete count is therefore 128=61M+67A.

## 3. Pretyping bounds and positive soundness

Before equations, the six positive hats/slacks give

    E0,E1,W,Z,J>=0, h>=3, B>=24, P>=1.

Every word in (3) is nonnegative, so (4) has positive scale and padded
ports before any binary typing is assumed. At a polynomial zero the
integer unit product times `1+sum residual^2` is one; therefore all four
ordinary residuals vanish, including (2), and the inherited native unit
product equals one.

The first equation of (2) excludes `J=0`, because it would set `P=1`
while `(W+1)+(Z+1)+beta>=3`. Thus `J>=1`, `P>=B`, and

    W,Z,J<P, E0,E1<=J,
    Mclass<=P-1, Rmask<P.                            (5)

All coefficients of the three words (3) lie in `[0,P)`. Consequently

    0<=H3,M3,A3<P^3<Q.                              (6)

These bounds precede the native theorem. The inherited complete
prescribed-AND contract, with its signed index restoration, gives

    Q is dyadic, H3 AND M3=A3.                       (7)

Its preconditions hold: (4) has the required residues 12, 10, 8 modulo16,
positive fields/scale, and (6) supplies the word bounds. The two private
native coordinates are used exactly as in the parent: `F0` feeds only the
checksum pair sum and packed index; `bound_beta` feeds only the positive
X bound. Outer words, scale and supplied outer coordinates depend on
neither. Thus the possible restoration `F0_old=F0-2`,
`bound_beta_old=bound_beta+2` preserves this entire outer interface. Its
positivity and every native norm/rank/sign fact are inherited from the
complete coupled proof, not re-inferred from a free AND oracle.

Since `Q=B*P^3` is a positive power of two, both integer factors `B,P`
are dyadic. Hence `h=B/8` is dyadic. Write `B=2^b`, `P=2^p`.
The relation `(B-1)J=P-1` with `J>=1` forces `b|p`: reducing `p` modulo
`b` gives a divisible representative `2^r-1` in `[0,B-2]`. Thus

    P=B^T, J=1+B+...+B^(T-1), T>=1.                 (8)

Because `P` is dyadic and (5) bounds each lane, (7) splits into exactly

    E0 AND J=E0, W AND Mclass=Z, W AND Rmask=W.       (9)

For any nonnegative integers `e,j` with `e AND j=e`, subtraction `j-e`
removes only selected one-bits of `j`; it has no borrow and is the disjoint
bitwise complement of `e` inside `j`. Apply this to `E0,J`. The computed
`E1=J-E0` therefore obeys `E1 AND J=E1`. At each time position (8),
exactly one of `E0,E1` has bit one. This recovers the removed lane without
assuming its conclusion during the preliminary bounds.

The range lane types `W=sum v_t B^t` with `0<=v_t<h`, since `h-1` is a
full binary low-bit mask. The class lane selects exactly those quotient
digits whose `E0` bit is one. Hence the actual digits of (1) are

    C_t=2v_t+1+e1_t,
    N_t=v_t+2e0_t*v_t+1+e0_t.

They are positive and below `B`: `C_t<=2h` and `N_t<=3h-1`, whereas
`B=8h`. Also `x,y<h`. Canonical base-B comparison in (2) now yields
`C_0=x`, `C_(t+1)=N_t` and `N_(T-1)=y`. The shifted residue
interpretation in Section1 identifies an actual T-step orbit. There is
no untyped division, unordered edge balance or omitted endpoint loader.

**Remark 1 (binary scope and a rejected scale shortcut).** Deleting a last
selector test does not follow for three or more selectors merely from
individual typing of the others and their total sum. For `B=4,J=5`, the
individually typed `E0=E1=1` leave `E2=3`, which is not a subset of `J`.
This is only a counterexample to the general complement inference, not
an actual compiler zero. The two-selector argument avoids this overlap.
Also one may
not drop the factor `B` from `Q` merely because `P` is dyadic:
`B=24,J=89,P=2048` satisfies `(B-1)J+1=P` but `B` is not dyadic. This
is an algebraic boundary example, not a full native zero. The retained
paid multiplication by `B` closes exactly that typing obligation.

## 4. Complete positive converse and preserved projection

Given a genuine orbit `x=n_0,...,n_T=y`, `T>=1`, choose a dyadic `h`
strictly larger than `x+y` and all `v_t=floor((n_t-1)/2)`. Set
`eta=h-x-y>0`, `B=8h`, and (8). Pack the actual odd/even selector bits,
quotients, and odd-selected quotients into `E0,E1,W,Z`, and supply their
hats plus one. Empty selectors and the zero quotient word are allowed.
Since `Z<=W<=(h-1)J`, the unique remaining slack is positive:

    beta=P-J-(W+1)-(Z+1)
        =(B-2)J-W-Z-1
        >=(B-2h)J-1=6hJ-1>0.                       (10)

Both outer equations, all three lanes, all ranges and (4) hold at dyadic
`Q=B*P^3`. The inherited complete prescribed native theorem therefore
supplies fifteen positive native witnesses. This is the full positive
extension, not a claim that large Pell values were materialized in the
finite diagnostics.

The old four-lane interface and the new three-lane interface are equivalent
on the same positive outer coordinates after (2). Each has a fresh native
extension exactly when those outer conditions hold. Therefore their
positive-zero projections onto `(x,y,edge0_hat,edge1_hat,quotient_hat,
product0_hat,height_slack,global_slack)` agree. There is no asserted
bijection of all 21 supplied witness tuples and no off-zero identity
between the 134- and 128-operation polynomials. In particular changing
joined words or scale does not reuse an old native tuple.

For `T>=0`, append exactly

    empty_endpoint_difference=input-target,
    empty_output=norm_output*empty_endpoint_difference.

Over the integers this product vanishes exactly when the old output is
zero or `x=y`. In the latter branch arbitrary positive witnesses suffice.
It costs 1M+1A and introduces no witness, giving the stated 130-operation
option and covering the zero-step convention explicitly.

## 5. Hand-derived ordinary polynomial degree bounds

All supplied inputs and witnesses have degree one; literals have degree
zero. No source-array evaluation or automatic degree propagation is used
in this packet. The following bounds follow from the displayed formulas
and the literal retained native factors.

The outer `E0,E1,J,W,Z,h,B` have degree one, while `P` has degree two.
Equation (3) gives `deg H3,deg A3<=5`, `deg M3<=6`. For the primary
scale, `deg Q=7` and `deg F3<=5`. The retained packed native index
`r=F0+qF1+q^2F2+q^3F3` has degree at most26. Put, using native rather
than outer symbols,

    X=q(r+bound_beta), Y=(2*odd_half+1)q,
    E=XY, a=E+Y, k=eta+zeta, c=kY+eta,
    H=4a+3, Delta=a^2+H, D0=X+ga*H,
    d=ac+D0, V=of-c, K=k-h_native*E.

Their degree bounds are respectively

    X:33, Y:8, E:41, a:41, k:1, c:9,
    H:41, Delta:82, D0:42, V:9, K:42.

The genuine all-ring cancellation in the main norm is

    d^2-Delta*c^2 = D0^2+2acD0-Hc^2.                (11)

This gives degree at most92 rather than the naive100. It does not use a
zero-set relation. The other retained factors are

    auxiliary: Delta^2*(ic^2)^2*(V^2-y_aux^2)+y_aux^2,
    first: tau_gap^2+4E*kY*(tau_gap-k),
    checksum: q-(F0+F1+F2+F3),
    strong: f^2-Delta*(ic^2)^2,
    index: K-r,
    linear: V-jc+2K.

Since `deg(ic^2)=19`, these give the complete factor bounds below.

| Scale/interface | Main | Auxiliary | First | Checksum | Strong | Index | Linear | Sum |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| New `B P^3` |92|220|51|7|120|42|42|574|
| New `B P^4` |114|272|63|9|148|52|52|710|
| Old four lanes `B P^4` |118|280|65|9|152|54|54|732|

For the control scale, the corresponding intermediate bounds are
`q:9,r:32,X:41,Y:10,E:51,c:11,Delta:102,D0:52,V:11,K:52`;
substitution into the same factors establishes its row. The parent's
last row is recorded for comparison with its pinned proof.

The four retained ordinary residuals have bounds `[2,3,5,6]`: the first
outer comparison, chronological transport, and the two padded input
comparisons. Hence `1+sum residual^2` has degree at most12, and the
literal product finalizer minus one has degree at most `574+12=586`.
The control has bound `710+12=722`; the old four-lane input residual
maximum was8, giving748. Multiplying by `x-y` adds at most one. None of
these is claimed to be an exact degree or a lower bound.

## 6. Exact scope and fresh evidence

The helper reads the pinned parent JSON only as inert data. It emits the
three source arrays (primary128, control128, primary empty130), checks
all row dependencies, private native consumers, free ports, full liveness,
literal retained tail, exact changed rows and M/A counts. It contains no
numeric interpreter, symbolic interpreter or degree propagator for either
parent or child arrays, and imports no repository/predecessor program.

Separate handwritten finite checks verify binary complements, three/four
lane equivalence on bounded scalar words, and actual shortcut-Collatz
paths with the full outer initialization, chronology and positive slacks.
These formulas are independently written and do not evaluate saved source
arrays. They supplement the all-size proof; neither native Pell zeros,
nontermination, nor universality is inferred from them.

The supplied raw input is the actual positive integer `x`, with target
`y` likewise ordinary. This specialized two-branch construction does not
silently apply the lane deletion to arbitrary larger residue tables.
Earlier prime-encoded universal counter maps still require their distinct
input loader and program/control compilation; those costs and the existing
complete universal bound are unchanged.

All four dependencies below were read inertly: the entire parent source
array and proof, the complete coupled native proof, and the earlier
Boolean-complement component. External cited Pell lemmas remain inherited
through the accepted complete native theorem; they are not newly audited
in this packet. No supplied or frozen helper was executed.

| Dependency | SHA256 |
|---|---|
| `residue_affine_packed_history.json` | `b2865672ed7cf629aba52e0b528b358670b8faf857b5e0a9a819b7e3c09c7421` |
| `residue_affine_packed_history.md` | `0b6c533e8ef6c26b3ed5419dbb2baa44bc1509255c4bcf5226e5f85d37683882` |
| `native_binary_index_coupled_units.md` | `efea1218eb5fadc1ad224a2ef6864fb5ea4fecbd5231d7b1379e3e376af690b5` |
| `native_controller_boolean_pairs56.md` | `b21d2b985829ee16d09524d96ad36d940bac373f5e98770c119211641703e82e` |

The fresh writer, then normal and optimized (`-O`) receipt comparisons,
ran from `/` and passed before freezing. All 386 emitted rows are live.
The handwritten checks cover 32,896 bounded complement pairs (6,561
subsets), 39,312 scalar three/four-lane assignments (28 accepted), and
144 genuine finite histories from inputs1--24 and horizons1--6. Twelve
have an all-zero quotient word. Another 288 single-port checks reject an
incorrect target or selected quotient. These are scoped outer diagnostics,
not evaluations of the complete source arrays.

Author artifacts are `residue_affine_binary_lane128_tesla.py` (SHA256
`14f0119560751ca783faceeff0b0bc35d8f095deeaf528641883794c0f7f8823`)
and `residue_affine_binary_lane128_tesla.json` (SHA256
`daa90bb7113164e564444eaca6de7025edaddd0e27fde02f93c9e7b11f4d41ea`).
Root and the independent reviewer own their separate proof/source
challenges; this note does not pre-certify those reviews.
