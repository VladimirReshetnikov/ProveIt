# Label-aligned controller lanes within the existing geometry

The controller's packed lane order need not match its physical edge-ID
order. This packet chooses among finitely many lane assignments, pays
their complete packing expressions, and retains the
[current compiler](group_projective_reindexed_shared_pack.md) whenever
none is cheaper. The lane span m, masks, scale, physical codes, edge IDs,
state-flow equations, comparisons and positive coordinate lists are
unchanged. The algorithm never enlarges m.

For the physically scrambled macro `(8,6,4,2,7,5,3,1)`, label-aligned
lanes save **7M+8A**, taking the same table from225 certificate /242
polynomial operations to **210 /227**, with98M+129A, six comparisons,
34 positive witnesses and exact degree2240. The physical word remains
`(8,6,4,2,7,5,3,1)` throughout: its actions are not reordered to obtain
the saving. The usual ten-letter table retains its existing245-operation
source. No numerical universal alphabet or improvement of75/88 is claimed.

## 1. Packing positions are independent of chronological order

There are n actual non-idle edges with fixed physical IDs e=1,...,n,
and a fixed power-of-two lane capacity m>=n. Let E_e=Ehat_e-1>=0 and
let ell_e in{0,...,7} be the edge's physical letter minus one. The
already paid physical selector pack is

    S=sum_e E_e P^ell_e.

For any injection p:{1,...,n}->{0,...,m-1}, the controller may instead
use

    Hc(p)=sum_e E_e P^p_e,  Mc=J R_m(P),
    J=sum_e E_e,           R_m(P)=sum_(j<m) P^j.     (1)

The lane exponent determines which field is stored in which P-sized
region. It does not determine which edge acts first. Chronological
positions are the radix-B digits inside each field E_e. The ordered
source/target-state flow comparison still uses the original physical
edge IDs and coefficients. No action within a macro is moved, and no
macro word is sorted or replaced.

The packet retains the original `codes` and `edges`. It records the new
injection in `packed_edge_exponents` and the correspondingly permuted
`lane_edges`, while each coordinate keeps its original name
`controller__edge_hat{e}`. Empty tables keep the current source.

## 2. A bounded paid planner and a guaranteed fallback

The planner constructs at most six distinct candidate maps, besides the
current source. Its two kinds of proposals are:

* **Layers of eight.** Choose phase0 or min_e ell_e, and traverse the
  original edge IDs in increasing or decreasing order. For an edge with
  label ell and zero-based occurrence number j of that label, its
  preferred position is `ell-phase+8j`. Keep this position if it lies
  within0,...,m-1. Assign overflow edges to the remaining unused slots
  in increasing slot order. Preferred positions are distinct: different
  labels differ by less than eight, and occurrences of one label differ
  by eight. There are enough unused slots because n<=m.
* **Contiguous label groups.** Sort edges by their physical label, with
  original IDs increasing or decreasing inside each label, and assign
  positions0,...,n-1. This sorts storage positions only; the source's
  physical path table and state-flow coefficients are retained.

Duplicate maps are removed. Every proposal is an injection into the
existing m lanes, including when a label occurs too often for all its
preferred positions to fit. There is no hidden lane-span increase or
new scale exponent.

For each proposal, the source first builds a completely paid direct
packing fragment. It orders occupied positions from high to low, uses
sparse Horner multiplication across each gap, and separately computes
the constant mask `sum_e P^p_e` to subtract from the hatted word.
Existing pure P-powers are reused only after an exact source audit;
missing powers, products and sums are emitted as literal binary gates.
The final lower-position factor is charged when nontrivial. No
subtraction of all n hats is assumed free.

The [shared-selector planner](group_projective_shared_selector_pack.md)
then applies its audited coefficient identity to this actual fragment.
It may reuse S and pay corrections by offsets `p_e-ell_e`, or keep the
direct fragment. Its all-integer linear-polynomial audit independently
checks every edge-hat coefficient and the constant term of Hc(p).
The private-consumer audit ensures that replacing the fragment changes
no unrelated source register. Register aliases at exact alignment are
handled without a paid copy operation.

Finally compare the complete candidate DAGs against the actual current
compiler DAG, including all new power, mask, correction and final gates.
Choose fewer total operations; ties retain the current source. Remaining
ties between strictly better candidates use multiplication count and a
deterministic plan name. Thus

    C_new<=C_current,   Poly_new<=Poly_current,       (2)

with comparisons, witnesses and finalizer costs fixed. Neither M nor A
separately is asserted to be monotone; the receipt records both exact
differences. Compilation-time search over a fixed table is not a new
runtime primitive. The search is only over these specified candidates,
not all lane permutations or all arithmetic circuits.

## 3. Full positive ordinary-input equivalence

The new full polynomial need not equal the old polynomial on arbitrary
integer tuples. Its Hc argument changes. This section proves equality
of their existential ordinary-input predicates, using the complete
fixed-table compiler and fresh native witnesses.

All scalar history, output, checksum and repunit bounds are unchanged.
The pretyping argument in the
[reindexed geometry proof](group_projective_reindexed_edge_geometry.md#2-complete-positive-soundness-and-converse)
uses only positive hats, `sum E_e=J`, and placement in distinct lanes
within the m-lane origin mask. Those hypotheses still give

    0<=E_e<=J<P,       0<=Hc(p)<=Mc<P^m.             (3)

For example, `Mc-Hc(p)` has coefficient J-E_e in occupied lanes and J
in unused lanes; each is nonnegative. All physical ports and the three
low batch words Hb,Mb,Zb are unchanged. The history-range region and
top radix-test region also stay unchanged. Thus all strict nonoverlap
bounds, computed native-field positivity, joint-unit sign recovery and
the independent native index-sign proof apply before Boolean typing.
Their use of the four fixed low-bit classes and exact checksum is not
altered by the choice of p.

The native theorem supplies the same dyadic P and B, the same common
cell duration, and the subset relation

    Hc(p) AND Mc=Hc(p).

By(3), each occupied lane decodes exactly its E_e. The subset relation
makes these Boolean radix-B fields; the unchanged checksum, with B>m,
forces exactly one edge per cell. Physical output sums and the ordered
state-flow comparison still identify the same hub-to-hub macro path.
The remaining selected-source and history-range predicates recover its
actual four-coordinate trace and endpoint. This proves soundness without
permuting chronological cells or changing a physical action.

Conversely take any accepted macro word. The parent's completeness proof
provides a sufficiently large dyadic height, the same positive duration,
genuine histories and one-hot edge fields. Keep all of those outer
coordinates, including each original edge's positive hat. Pack its field
in lane p_e instead. The new Hc(p) is a subset of the same Mc, and all
other separated binary predicates remain true. The complete scalar AND
converse at the unchanged native scale supplies fresh strictly positive
native witnesses; the retained coordinate maps and unit merges then
give a complete new zero. In the other direction the same argument can
repack a recovered genuine path in the old lanes.

Native coordinates generally change even though the scale stays fixed,
because the packed fields and their encoded native index change. No
same-tuple bijection with all old zeros is claimed. Finite off-zero
identities below concern the explicit changed scalar interface, not an
unrestricted identity between the old and new full polynomials.

## 4. Degree and exact sample savings

Write nu=1+chi, where chi indicates computed P. Because m and every
scale expression stay fixed, q=16P^L has the same highest form, with
L=2m+10 for a reused controller mask and L=m+18 otherwise. For every
candidate injection,

    deg Hc(p)<=nu(m-1)+1.

The joined selected word is

    Z=Zb+P^8 Hc(p)+P^(m+8) Hb.

Its last term has highest form `H2*(P*)^(m+15)`. Its degree exceeds
the possible controller term's degree by8nu and the low batch term's
degree by at least nu(m+8). Thus the leading controller cancellations
cannot affect this term. The complete native packed index still has

    r*=16^4 H2*(P*)^(3L+m+15).                       (4)

All native factor highest-form proofs in the five inherited compiler
families use the same q*, r*, positive supplied native coordinates and
unchanged definitions. They therefore retain their exact degrees and
leading forms. The four transport polynomials, state flow, remaining
scalar bounds and their highest forms are literally unchanged. This
also preserves the largest outer degree and its nonzero square sum.

In particular the nonempty `joint` family still has exact degree

    nu(36L+7m+106)+44.                              (5)

The helper builds its leading-weight map from the actual injection p;
it does not confuse a physical ID with a packed lane. The proof uses
the literal DAG and no equation such as P=B^t to lower a degree.

All rows below use the `joint` family with reused mask and computed P:

| Fixed physical macros | Old / new polynomial | New certificate | New M+A | Comparisons / witnesses | Degree |
|---|---:|---:|---|---:|---:|
| `(8,6,4,2,7,5,3,1)` |242 /227|210|98M+129A|6 /34|2240|
| `(8,6,4)`, `(2,7)`, `(5,3,1)` |242 /227|210|98M+129A|6 /34|2240|
| `(8,8,8,8,1,2,3,4,5,6,7,1)` |273 /270|253|114M+156A|6 /38|3504|
| `(8,7,6,5,4,3,2,1)` repeated twice |294 /281|264|117M+164A|6 /42|3504|
| `(1,2,3,4,5,6,7,8,1,2)` |245 /245|228|104M+141A|6 /36|3504|

For the first row, assign p=(7,5,3,1,6,4,2,0) to the eight original
edge IDs. Then Hc=S, so the separate7M+8A controller pack disappears.
This works for every one-macro permutation of the eight different
physical labels: storage can be aligned without changing that macro's
action order. The third row shows that the planner also improves an
unbalanced table where all occurrences cannot fit their preferred
layered positions. The last row is an explicit fallback.

The sample tables are not the numerical universal subgroup alphabet.
The complete fixed-table theorem continues to apply to any such fixed
alphabet when instantiated, with its actual audited ledger.

## 5. Executable evidence and its scope

[The source](group_projective_label_aligned_lanes.py) exposes `build`,
`rewrite`, `polynomial_source`, and `degree_top`. The rewrite accepts an
unshared reindexed geometry packet and includes its current shared-pack
compiler as the fallback. [The receipt](group_projective_label_aligned_lanes.json)
stores variant ledgers and one complete nonaligned illustrative DAG.

For positive and signed supplied tuples, the checker directly computes
`sum(Ehat_e-1)P^p_e`, substitutes exactly that scalar controller word into
the original unshared source, and compares every retained register,
every residual and the complete output. Replaying the unshared source
matters when the old optimized source aliased Hc and S: overriding that
alias would incorrectly change the physical selector pack as well.
Origin mask, scale, physical low packs, J, comparisons and coordinate
lists are checked unchanged. Every proposed word also passes the exact
integer-polynomial coefficient audit before selection.

Four weighted affine univariate audits verify the actual native factor
and outer leading forms for nonaligned single-path, split-path and
unbalanced cases. Four genuine accepted signed-shear trajectories use a
permuted list of single-letter macros, retain the exact physical trace,
and check all outer comparisons and the joined scalar AND after lane
permutation. Their placeholder native coordinates are not claimed Pell
zeros; the complete positive extension is the argument in Section3.
Normal execution compares the deterministic receipt; `--write` regenerates it.

The author writer and fresh default passed210 ledgers and3,360 complete
changed-interface/output checks, including840 signed assignments, plus
the four exact degree audits and four genuine outer-path fixtures.
Root's independent full proof/source/default review passed without
findings. Independent `substrates` review also passed the full proof,
source and fresh default. It additionally checked288 arbitrary-injection
scalar/residual cases at P=-2,-1,0,1,2,7, and768 independently constructed
path/flow cases, including287 rejected bad flows. Those injections extend
beyond the planner's proposals. They supplement the parametric proof and
do not claim to materialize full native Pell zeros. The packet is frozen
after these reviews.
