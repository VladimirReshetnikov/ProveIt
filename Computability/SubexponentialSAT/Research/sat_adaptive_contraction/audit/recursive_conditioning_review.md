# Independent review: uncached recursive conditioning of the mode graph

**Verdict: valid.** The proposed reorganization improves the paid mode-enumeration factor in polynomial space. It does not require a cheap oracle for a group tensor, a second application of the tensor-contraction theorem to inadmissibly high-degree tensors, or exponential caches.

## Exact identity and oracle dependence

For one fixed exact pair-weight array, let `I_e` be the finite list of exponent vectors for directed group pair e, and `d_e=|I_e|`. Reject the entire array immediately if any `d_e=0`. The global domain is the Cartesian product of these lists because the total-weight constraint has already been fixed through the array. Every group factor `Z_g` depends only on lists incident with g.

For a subset S of the group vertices, hold its external boundary assignments fixed and let `F_S` sum the product of its factors over its internal pair indices. Split `S=A disjoint_union B`. The internal variables separate into the cut C between A and B and the internal variables of A and B. Distributivity gives the exact identity

`F_S(boundary) = sum_{x_C} F_A(boundary_A,x_C) F_B(boundary_B,x_C)`.

At a singleton `{g}`, every incident pair has acquired an assignment at one ancestor cut. The leaf can therefore call the actual expensive child-contraction oracle `Z_g`. Nonincident exponents may be filled with zero in a complete tuple representation: the definition of the g-child never reads them. Creation precision and interpolation parameters do not depend on those unused values.

The identity uses only addition and multiplication, so it remains exact over the original coefficient ring, including powers-of-two quotients and nilpotents. It introduces no division or precision loss. All accumulation takes place at the already justified working precision.

## Exact call ledger

Use depth-first recursion and no caches. A root-to-leaf path fixes the cut assignments at its ancestors. Those cut sets are disjoint: an edge appears at the unique split separating its two endpoints. For leaf g let `P_g` be the union of the cuts on its path. Then the number of calls to its expensive oracle is exactly

`prod_{e in P_g} d_e`.

Total oracle calls are the **sum**, not the product, over leaves:

`sum_g prod_{e in P_g} d_e <= r max_g prod_{e in P_g} d_e`.

The key distinction is that after a root cut assignment, the algorithm completely sums one child, completely sums the other, and multiplies the two scalar results. It does not cross-enumerate their internal assignments. Repeated evaluation of any leaf under irrelevant ancestor assignments is already charged in the displayed product.

An internal-node visit count is the product of domain sizes on its ancestor cuts plus its own cut. This set is contained in the path cut union of every descendant leaf. Since `d_e>=1`, internal work is bounded by `(2r-1)` times the maximum leaf product, up to polynomial work per visit. Thus multiplication, addition, rank/unrank operations, and context changes do not introduce an uncharged exponential factor.

## Space

Store the current assignments to ancestor cuts, one accumulator and two returned scalar values per stack level, and the polynomial-size exact-weight rank/unrank data. The number of groups r is fixed. Each mode vector, rank, ring element, and original tensor description has polynomial bit length in the global root size. The outer contraction recursion has logarithmic-logarithmic depth. No exponentially large table is stored. The actual oracle calls retain the source's immutable-description convention and polynomial-space execution.

## Balanced-tree coefficient

For balanced bisection of r group vertices, define

`v(1)=0`,

`v(r)=2 floor(r/2) ceil(r/2)+max(v(floor(r/2)),v(ceil(r/2)))`.

It bounds the number of directed pair axes on a leaf path. For `r=16`,

`v(16)=128+32+8+2=170`,

whereas full mode enumeration charges all `16*15=240` directed pairs. For powers of two, `v(r)=2(r^2-1)/3`.

The already established exact-weight subset entropy estimate gives

`sum_{e in P_g} log2 d_e <= (sqrt(v(r))/r+o(1)) K(M,u)`,

where `K(M,u)=pi sqrt(2) M/(ln(2) sqrt(u))` under nearly lossless padding and full-orientation slope-four modes. This charges the leaf oracle honestly, yielding the upper recurrence

`T_d <= poly(s) 2^((sqrt(v(r))/r+o(1)) K(M_d,u_d)) T_(d+1)`.

At r=16 the factor relative to full enumeration is

`sqrt(170/240)=sqrt(17/24)`.

Using the previously checked adaptive boundary schedule therefore gives

`C_RC = 66.19272369357722... sqrt(17/24)`

`     = 55.70947831890998...`,

with polynomial space. The new constant remains on the normalized wire scale, and its theorem retains `C_RC+o(1)`. This is a constant improvement; it does not satisfy the stronger unproved `M/u` structured-summation hypothesis.

## Independent finite check

`check_recursive_conditioning_independent.py` implements this identity independently of the proposed main implementation. It compares against full Cartesian enumeration over the nonfield ring `(Z/64Z)[V]/(V^2)`, checks the exact individual leaf-call counts against the product formula, checks maximum live assigned-pair counts, and exercises empty and unequal domains.

Both normal Python and `python -O` passed all 40 fixtures, with group counts 2 through 6. The structural path counts were checked through r=17, including `v(16)=170`. Output ledgers are `recursive_conditioning_independent.json` and `recursive_conditioning_independent_optimized.json`. These are finite local validations, not an end-to-end SAT implementation or an asymptotic proof.

## Corpus overlap and attribution

The fourteen-packet corpus was searched for recursive conditioning, bisection, separators, cutsets, binary trees, and related group-summation terms; relevant mode-graph and exact-weight indexing code was then inspected directly.

- `3sat_refinement/code/weighted_partitions.py` reorganizes the same exhaustive sum by exact pair weights and ranks. It still enumerates the Cartesian product across all pairs; it does not use recursive conditioning.
- `3sat_precision_refinement/code/mode_network.py` validates two-group exact sums and compact indexing. It does not supply this multigroup separator algorithm.
- `eth_joint_cauchy/.../code/mode_graph.py` and its report construct group caches and three block tables, then perform a direct or Strassen triangle contraction. Its resource analysis deliberately permits exponential storage. It does not contain the uncached recursive-conditioning route above.
- Other packets refine packing, precision, schedules, scalar lifting, or mode bases; no corresponding uncached multigroup contraction was found in the inspected corpus.

The general method itself is classical recursive conditioning, not a newly invented universal algorithm. Appropriate primary attribution is:

Adnan Darwiche, **Recursive conditioning**, *Artificial Intelligence* 126(1-2):5-41, 2001. DOI `10.1016/S0004-3702(00)00069-2`.

Publisher source: https://www.sciencedirect.com/science/article/pii/S0004370200000692

The source explicitly treats exact inference and linear-to-exponential-space tradeoffs. The contribution here is the application to exact-weight mode-pair lists, the fully paid child-contraction oracle accounting, and the resulting sharper polynomial-space certificate relative to this repository corpus. No broad literature-wide novelty claim is justified.
