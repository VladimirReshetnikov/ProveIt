# Composing reindexed geometry with shared selector packing

The complete fixed-table compiler now costs **228 certificate / 245
polynomial operations** on the illustrative ten-letter table, with
polynomial split **104M+141A**, six comparisons, 36 positive witnesses
and exact degree **3504**. This composes two proved reductions:

1. [Reindexed geometry](group_projective_reindexed_edge_geometry.md)
   moves controller edge e to lane e-1 and, when eligible, halves its
   power-of-two lane span.
2. [Shared selector packing](group_projective_shared_selector_pack.md)
   reuses the physical selector word to construct the controller word
   by a paid polynomial identity.

The first transformation preserves the ordinary-input existential
predicate, with fresh native witnesses at the changed scalar interface.
The second preserves the entire polynomial identically on all integer
supplied assignments. These are distinct proof steps. Their composition
retains the complete compiler theorem; neither sample table below is
asserted to be a numerically instantiated universal alphabet. The
separate universal 75/88 frontier remains unchanged.

## 1. Coordinate metadata and the packing identity

Physical edge coordinates keep their original names `Ehat_e`, e=1,...,n.
The reindexed packet records their actual controller lane exponents in
`packed_edge_exponents`; it retains the physical label ell_e in
`edges`. On an applied reindexing branch p_e=e-1, and on a parent
fallback p_e=e. The shared planner reads that map explicitly.

With E_e=Ehat_e-1, the two words remain

    S=sum E_e P^ell_e, Hc=sum E_e P^p_e.

The shared-packing theorem holds for any distinct nonnegative p_e.
Its grouping by d=p_e-ell_e, minimum b=min p_e, and anchors r>=b
therefore applies without modification. The symbolic linear-polynomial
audit checks every coefficient in the actual source before and after
the replacement. Negative offsets still require only nonnegative
polynomial exponents, never division.

The degree helper delegates to the reindexed geometry packet, which
uses its actual m, scale exponent and lane-weight map. One cannot use
the old unreindexed degree helper after a geometry halving. The packing
identity then preserves this complete degree and highest form exactly.

## 2. Zero-cost aliases at exact alignment

When p_e=ell_e for every edge, Hc is already S. The correction planner
emits no arithmetic. It renames the existing S defining register to
the public controller-word register and rewires every consumer of S.
It checks that the renamed register occurs in no comparison. This is
a register alias, with no addition by zero or multiplication by one.
All comparison expressions and supplied coordinate lists are retained.

The one-edge case also needs no private Horner fragment: its old
controller word is just Ehat_1-1. The private-consumer audit is valid
when the private set is empty; the public word itself still exists and
is charged before the rewrite.

These two boundary cases are checked across the compiler families.
For example, the aligned single macro `(1,2,...,8)` has n=m=8 after
geometry halving. Its 15-gate separate pack, costing 7M+8A, disappears
entirely. The joint reused-mask/computed-P endpoint is then **210
certificate / 227 polynomial operations**, split **98M+129A**, six
comparisons, 34 positive witnesses and degree **2240**. Its parent
before these two transformations used m=16. This is a different
illustrative table from the ten-letter comparison below.

## 3. The six-gate ten-letter controller word

For labels `(1,2,3,4,5,6,7,8,1,2)` and positions p_e=e-1, the
first eight edges have offset zero and the last two have offset eight.
Let

    T=Ehat_9+P*Ehat_10-(P+1).

The exact controller word is

    Hc=S+(P^8-1)*T.

The existing P+1 and P^8 are reused. Computing T costs 1M+2A; P^8-1
costs 1A; the correction product and final addition cost 1M+1A. Thus
the fragment costs **2M+4A**, six gates. The reindexed parent's
separate pack costs 10M+11A, so this step saves **8M+7A**. Reindexing
had already saved one multiplication from the idle-free parent. The
combined saving from its 261-operation polynomial is **9M+7A**, or
16 operations.

The four joint choices are:

| Mask reuse | Computed P | Certificate / polynomial | Polynomial M / A | Comparisons / witnesses | Degree |
|---|---|---:|---:|---:|---:|
| Yes | Yes | 228 / 245 | 104 / 141 | 6 / 36 | 3504 |
| No | Yes | 229 / 246 | 105 / 141 | 6 / 36 | 2928 |
| Yes | No | 228 / 248 | 105 / 143 | 7 / 37 | 1774 |
| No | No | 229 / 249 | 106 / 143 | 7 / 37 | 1486 |

For the same table, retaining the strong-unit comparison arrangement
gives polynomial/degree pairs 246/3502, 247/2926, 249/1773 and 250/1485
in the same row order. The shifted family before either unit merge
has certificate 223 and polynomial 246, eight comparisons, 36 witnesses
and degree 4298 in the reused-mask/computed-P configuration.
The unshifted six-field supplied-P options give 252/1211 and 253/995
with 38 witnesses. The four-field no-mask/supplied-P option gives
259/802 with 40 witnesses. These are audited operation/degree
tradeoffs, with no arithmetic optimality claim.

For arbitrary tables the wrapper uses each transformation's actual
saving and fallback. It never assumes the repeated-label structure of
this example. In particular neither a geometry halving nor a shared
packing saving is universal across tables.

## 4. Executable evidence

The [source](group_projective_reindexed_shared_pack.py) composes the
existing builders and the generalized alias-aware shared planner. Its
[receipt](group_projective_reindexed_shared_pack.json) records 190
ledgers covering all five source families and both compiler switches.
Across 4,560 complete-source assignments, including 1,520 signed
assignments, every retained register, every residual and the complete
polynomial agree with the actual reindexed source. There are 110
ledgers with a zero-cost alias candidate, explicitly checked without
an S copy gate. All degrees and weighted leading coefficients agree
with the geometry source. The unchanged unreindexed shared-packing
receipt also passes after the generalization.

The geometry packet separately proves and checks the changed native
interface and its positive converse. Finite identities in this packet
are supplementary source evidence; the all-integer coefficient identity
and the parametric positive geometry proof establish the composition.
Normal execution compares against the saved receipt; `--write`
regenerates it. Earlier packet sources remain runnable.

Independent review passed the proof, source and both fresh default
receipts. It added 480 signed complete-output identities, including
60 alias configurations, 30 geometry halvings and 10 packing fallbacks.
