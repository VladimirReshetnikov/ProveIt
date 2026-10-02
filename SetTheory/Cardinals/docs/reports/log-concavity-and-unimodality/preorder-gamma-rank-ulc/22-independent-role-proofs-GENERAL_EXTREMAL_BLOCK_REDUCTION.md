# Minimal and maximal equivalence-block refinements

Status: an extension of the independently approved boundary-block identities, prepared for external scope review. The formulas are unchanged; only the ambient-preorder hypothesis is widened.

## Statement

Let B be a minimal equivalence class of a finite preorder, of size two or three. No vertex outside B lies below any member of B. The block need not be below every outside vertex: outside vertices may be incomparable with it. The size-two and size-three positive role-weighted refinement formulas from `BOUNDARY_REDUCTIONS.md` preserve the entire disjoint-support polynomial, while replacing B by a strict chain. Dually, the same holds for a maximal equivalence class.

This identity holds in all ranks and leaves every outside activity and every outside arc unchanged. Effective activities can be zero. It does not apply to arbitrary interior equivalence blocks.

## Why the broader hypothesis suffices

All vertices of an equivalence class have identical strict outside neighborhoods. Since B is minimal, no outside tail can match a head in B. Let a selected local state have t tails and h heads. Necessarily t>=h. The local heads must be matched internally, and the t-h surplus local tails all have the same outgoing neighborhood N outside B.

Consequently, for a fixed outside endpoint support, feasibility depends only on the pair (t,h) and whether the local state admits an internal matching covering its h heads. It does not depend on the identities of the surplus block tails: every such tail has neighborhood N, including when N omits incomparable outside vertices. Summing the weights of feasible local states for every pair (t,h) is therefore sufficient to determine the full weighted support polynomial. There is no multiplicity from choosing an internal matching witness or choosing which surplus tail matches a given outside head.

The existing formulas preserve exactly these local state sums. That proof never uses N being the entire outside vertex set. This establishes the broader transfer statement.

## Explicit formulas

For a two-element minimal block, keep tail activities u1,u2, replace the block by 1<2, and set

v2'=v2+u2 v1/u1.

The first head is unused and may have any positive activity. Pure-tail state sums are unchanged and the only mixed state has weight u1 v2'=u1 v2+u2 v1.

For a three-element minimal block, permute its vertices so their tail activities are x<=y<=z, carrying their head activities with them. Put

a=sum_(i!=j) u_i v_j,
c=sum_j v_j xyz/u_j,
Delta=z(x+y)-xy>0.

Keep the ordered tail activities, replace the block by a strict chain, and set

v2'=[(x+y)c-xy a]/[x Delta],
v3'=[z a-c]/Delta.

The first head is unused. The mixed local states (t,h)=(1,1) and(2,1) have weights a,c, because

x v2'+(x+y)v3'=a,
xz v2'+xy v3'=c.

The effective heads are nonnegative. Explicitly,

(x+y)c-xy a=y^2(z-x)v1+x^2(z-y)v2>=0,
z a-c=z^2(v1+v2)+Delta v3>0.

All pure-tail elementary symmetric state sums are unchanged. These exhaust the local states since the block has size three. The maximal version follows by reversing the order and interchanging tail/head roles.

Permuting within an equivalence block is an automorphism of the original preorder. The sorting used for a size-three block therefore does not restrict the original activities. Different choices of the sorted order produce isomorphic refined relation types, with the activities carried by the corresponding vertex map.

## Simultaneous refinements and actual degree

Several disjoint minimal or maximal blocks may be refined successively. Minimal-block refinement changes only head activities in that block; maximal-block refinement changes only tail activities there. Each chosen disjoint block is refined only once, even if it is both minimal and maximal. The denominator activities needed by every other disjoint block are unchanged and remain positive. Zero effective activities are allowed at the end and handled by continuity.

The underlying undirected comparability graph is unchanged by replacing an equivalence block by a strict chain. More importantly, the whole gamma polynomial is preserved, so its surviving degree is exactly preserved as well. A theorem on the refined relation applies at the original actual degree, without padding.

## Finite-target maps

`nontotal7_boundary_refinements.json` lists eligible extremal blocks, refined rows, and canonical target IDs for the seven-vertex catalog. The relational refinement sorts each block by its canonical labels; the activity-level proof first uses an appropriate within-block automorphism to sort activities. The map file is not a theorem until the widened scope and the target identities are independently reviewed.
