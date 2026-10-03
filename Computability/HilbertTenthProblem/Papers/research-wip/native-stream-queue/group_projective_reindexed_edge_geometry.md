# Reindexing non-idle controller lanes and shrinking their geometry

After [all idle positions are removed](group_projective_idle_free_paths.md),
the actual edge fields can occupy lanes `0,...,n-1` instead of `1,...,n`.
On the parent's factored packing branch this deletes one multiplication.
When n is a power of two, the controller can also use m=n rather than
m=2n, subject to the range-mask condition below. For n>=8 this removes
three multiplications and one addition in total and lowers the exact
polynomial degree.

For the illustrative ten-letter table `(1,2,3,4,5,6,7,8,1,2)`, the new
source costs **243 certificate / 260 polynomial operations**, with
**112M+148A**, six comparisons,36 positive witnesses and exact degree
**3504**. This is a parameterized fixed-table result, not an instantiated
numerical universal alphabet. The separate75/88 frontiers are unchanged.

## 1. The exact new scalar interface

Let n be the sum of the nonempty macro lengths. The parent has m0 lanes,
where m0 is the least power of two at least max(2,n+1). Its remaining
positive edge coordinates are `Ehat_1,...,Ehat_n`; both the hub idle and
all padded idle fields have been fixed to zero by setting their hats to
one. Retain every physical edge, its source/target state numbers, and
the supplied coordinate names. Write E_e=Ehat_e-1>=0 mathematically.

The checksum still computes

    J=sum_(e=1)^n E_e.

Replace only the controller's packing convention by

    Hc=sum_(e=1)^n E_e P^(e-1),
    Mc=J R_m(P),          R_m(P)=1+P+...+P^(m-1).     (1)

The implementation applies this rewrite when the parent's selected plan
is `factored non-idle`. Its last two gates are

    inner=sum Ehat_e P^(e-1)-R_n(P),
    old_Hc=P*inner.

Rename the subtraction output to the public controller-word register and
delete the multiplication. The source audits that `inner` has no other
consumer and occurs in no comparison. Thus (1), including
`old_Hc=P*Hc`, holds for arbitrary integer assignments. No division or
zero-cost runtime arithmetic is used.

For an empty table, or when the parent selected its other packing plan,
the implementation retains the parent unchanged. For the factored
branch choose m as follows:

* If n>=2 is a power of two, set m=n, except in the next case.
* If the controller mask is also reused to bound the eight history
  lanes and n<8, retain m=m0. That reuse needs m>=8.
* Otherwise retain m=m0.

In particular n=1 retains m=2. The fixed input margin from the parent,
`alpha+beta+1>=m0`, is deliberately retained. It implies the needed
smaller margin without changing any paid boundary expression.

Let epsilon be one when the controller mask is reused and zero
otherwise. With Hb,Mb,Zb the unchanged eight-lane physical packs, define

    T=P^(m+8),
    T2=P^(2m+8) if epsilon=1, otherwise P^(m+16),
    RM=(2D-1)Mc if epsilon=1,
       (2D-1)J R_8(P) otherwise,
    H=Hb+P^8 Hc+T Hb+T2 B,
    M=Mb+P^8 Mc+T RM+T2(B-1),
    Z=Zb+P^8 Hc+T Hb,
    q=16 T2 P^2=16P^L,
    L=2m+10 if epsilon=1, otherwise m+18.           (2)

These are paid source expressions, not free exponentiation instructions.
When m changes, the source rewires the origin mask, `joint_scale`, and,
in the reused-mask case, `range_body_scale`. Existing power registers
provide every new factor. It removes only audited unused power/repunit
gates. All scalar comparisons, physical port expressions, ordered flow
expressions, histories, ordinary input and positive supplied coordinate
lists stay the same. Their downstream native values need not stay the
same because the joined AND operands and possibly its scale change.

The packet records the original coordinate-to-exponent map explicitly as
`packed_edge_exponents`; original edge e has exponent e-1 on the applied
branch and e on the fallback. `edges` retains the old physical indexing,
while `lane_edges` describes the new packed indexing. No existing source
coordinate is silently renamed.

## 2. Complete positive soundness and converse

This section proves equality of the ordinary-input existential
predicates. It does not claim a positive-tuple bijection or an identity
between the two complete polynomials.

The native and joint-bound bootstrap from the
[joint-bound unit proof](group_projective_joint_bound_unit.md) applies
unchanged, with (2) as its new joined interface. Here are the needed
bounds explicitly. Positive edge hats imply E_e>=0. The joint scalar
bound and retained repunit relation give J>0 and B<=P. Hence the
checksum implies E_e<=J<P; physical selectors are sums of subsets of
these fields, so 0<=S_i<=J and `(B-1)S_i<=P-1`. The history/output
bound gives `Hb,Zb<P^8`; physical mask coefficients give `Mb<P^8`.
Because n<=m, equation(1) gives

    0<=Hc<=Mc<P^m.

For epsilon=1, m>=8 ensures Hb<P^8<=P^m. Also
`2D-1<B-1`, so `(2D-1)J<P`, whence `RM<P^m`.
For epsilon=0, the same argument bounds RM by P^8.
Thus all lower, controller, range and top-radix regions in(2) have the
same strict nonoverlap bounds as the parent. In particular the computed
native fields remain positive before typing, and the unit-sign recovery
does not assume Boolean edges or a correct path. The exact checksum and
four fixed low-bit padding classes are unchanged in form.

The paid native theorem therefore gives the joined binary AND predicate
at scale q and types P as a power of two. Its two top radix regions
recover `B AND (B-1)=0`, hence B is dyadic. The retained repunit relation
then gives `P=B^t`, `J=R_t(B)`, for an integer t>=1. Region separation
recovers precisely `Hc AND Mc=Hc`, as well as the physical selected-source
and history-range predicates.

Every E_e lies in a distinct canonical P-lane of(1). The subset predicate
makes it a Boolean length-t radix-B word. The checksum, with
`B>m0>=m>=n`, forces exactly one of the n actual edges at every position.
The [regular controller proof](group_regular_macro_controller.md#3-exact-one-hot-edges-adjacency-and-physical-outputs)
uses the source/target state coefficients and these Boolean fields, not
their arbitrary packing order. Those coefficients and the chronological
flow comparison are unchanged. The largest state label is at most
`n-number_of_macros<n<=m`, so all its digit bounds remain valid even
after halving m. It follows that the physical word is a concatenation
of complete hub-to-hub macros.

The selected-source and range relations now give the exact shifted
history digits, with the same carry-free transport proof and endpoint
`(1,u,1,u) -> (0,1,0,1)` as the parent. This proves soundness for an
arbitrary fixed macro table and ordinary x>0.

Conversely, an accepted macro word is nonempty: the initial first
coordinate is one and its target is zero. Remove all hub idle positions
as in the parent, then choose a sufficiently large dyadic D for that
finite trace. Its duration t can be any positive integer. Set B=16D,
P=B^t and assign genuine histories, physical selections, and each live
edge's Boolean word to the same positive hat coordinate. Pack those
words in the new positions e-1. Formula(1) is a subset of the new
origin mask, and every relation in(2) is the intended binary AND.
The same strict history/joint-bound margins supply positive outer
slacks. Finally apply the scalar AND positive converse at this actual
new q and the parent's positive coordinate maps/unit equivalences to
obtain all native witnesses. They are constructed afresh; importing
old native coordinates at a different q would not prove completeness.

## 3. Literal savings and switch table

On the applied branch the final packing multiplication always saves1M.
When n is a power of two at least8, reducing m0=2n to m=n additionally
deletes:

* the square producing P^(2n), since `joint_scale` now uses the existing
  P^n register;
* the factor `P^n+1` and multiplication that produced R_(2n), since the
  origin mask now uses the existing R_n.

These are1M+1M+1A, for a total saving **3M+1A**. The checker audits that
the removed P^(2n) has exactly the expected scalar-scale consumers and
that the two repunit gates become private and unused. Powers and
repunits up to length8 remain available for physical selection.

For n=2 or4 with epsilon=0, those powers/repunits are still needed by
the eight-lane selection block, so halving geometry saves only the
packing1M. With epsilon=1 and n=4 the implementation keeps m=8 and
likewise saves1M. Fallbacks save zero. Denoting these precise savings by
s_M,s_A, the new certificate and complete polynomial both have

    M_new=M_parent-s_M,   A_new=A_parent-s_A.         (3)

Comparison and witness counts are unchanged. For the current `joint`
variant on any applied nonempty table they remain `7-chi` comparisons
and `n+27-chi` positive witnesses, where chi indicates computed P.
This is an incremental ledger against the actual paid parent schedule;
one must not substitute new m into the parent's pre-specialization
gate formula and assume all those gates were rebuilt.

For the ten-letter table with alpha=24,beta=12:

| Controller mask epsilon | Computed P chi | Certificate | Polynomial | Split | Comparisons | Positive witnesses | Degree |
|---|---|---:|---:|---|---:|---:|---:|
| 1 | 1 | 243 | 260 | 112M+148A | 6 | 36 | 3504 |
| 0 | 1 | 244 | 261 | 113M+148A | 6 | 36 | 2928 |
| 1 | 0 | 243 | 263 | 113M+150A | 7 | 37 | 1774 |
| 0 | 0 | 244 | 264 | 114M+150A | 7 | 37 | 1486 |

As a separate example, the one-macro eight-letter table `(1,...,8)` now
uses m=8 rather than16. Its epsilon=chi=1 circuit costs225 certificate /
242 polynomial operations,105M+137A, with six comparisons,34 positive
witnesses and degree2240. These sample tables are not identified with
the fixed universal subgroup's full alphabet.

## 4. Exact degree after changing the packed geometry

All five inherited source families (`four`, `six`, `shifted`, `strong`,
`joint`) are covered by the rewrite and ledgers. The corresponding
parent degree formula remains valid with the actual new m and L.
Packing reindexing does not create a new highest-degree term: Hc has
degree at most `nu(m-1)+1`, whereas the unchanged high range-history
region supplies the leading term of the packed native index. Here
nu=1+chi, and the homogeneous part of computed P is

    P*=16D*J*,  D*=alpha*x+height_slack,
    J*=sum_(e=1)^n Ehat_e.

In particular, the packed-index leading form remains

    r*=16^4 H2 (P*)^(3L+m+15),

with P* the supplied variable when chi=0. The proofs of the native
factor degrees and their nonzero leading forms are therefore unchanged
after the m,L substitution. The source's degree helper only relabels
the degree-one edge weights to match lane positions; it does not use
zero-set equations to simplify the polynomial.

For `joint`, every nonempty applied table has exact degree

    nu(36L+7m+106)+44.                              (4)

Indeed the native unit degree is `nu(36L+7m+106)+38`; the largest
remaining outer residual degree is3. When P is supplied, at least one
signed physical-port difference is a nonzero polynomial, since every
live edge affects exactly one physical coordinate. When P is computed,
the four history leading factors are proportional to J*+d_i*, where
d_i* is the signed physical-port difference for coordinate i. Their sum
is at least3J* for positive edge weights, because each edge appears in
only one d_i* with sign+1 or-1. Thus their sum of squares is nonzero
without an idle edge. The joint-bound leading form is also nonzero.
The unchanged parent factor-leading-form argument completes (4).

At n=8, epsilon=chi=1 this changes3504 to2240; at n=16 the same switch
changes6032 to3504. Reindexing alone preserves the degree, as in the
ten-letter table. These are degrees in all supplied variables of the
literal final polynomial, with no uncharged substitution P=B^t.

## 5. Source and verification scope

[The source](group_projective_reindexed_edge_geometry.py) exposes
`rewrite`, `build`, `polynomial_source`, and `degree_top`, plus the
explicit exponent metadata needed by later packing rewrites.
[The receipt](group_projective_reindexed_edge_geometry.json) stores all
ledgers and one complete illustrative source, not repeated copies of
every imported DAG.

The checker evaluates all complete residuals and final outputs against
an independently overwritten old scalar interface, including signed
off-zero assignments. It separately expands (1)-(2) directly, audits
all literal M/A differences, and checks unchanged comparison/coordinate
lists. Six exact weighted affine univariate audits verify the actual
native factor degrees and leading coefficients plus the remaining
outer sums, without expanding the large final product. Four genuine
signed-shear path fixtures check every outer comparison and the enlarged
scalar AND after m16-to8 geometry reduction. Their placeholder native
coordinates are expressly not claimed to be Pell zeros; the full
positive extension is proved in Section2.

The author writer and fresh default replay passed all180 ledgers,
2,880 complete scalar-interface/output assignments (including720 signed
assignments), six exact factor/outer degree audits and four genuine path
fixtures. Independent review by `reduce_complete75` passed the complete
proof, source and fresh default, with no findings. Its additional144
signed full-output/interface identities covered n=2,4,8,10,16, including
the small-mask exceptions and reduced-geometry cases.
