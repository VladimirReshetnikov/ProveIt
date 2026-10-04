# Independent review: five-live-signal positive-determinant planar realization

**Verdict: PASS for the main physical theorem and its stated scope. No correction is required in the frozen packet.**

Audit date: 4 October 2026. This is a source-bound conventional mathematical review with independently authored exact/static evidence, not a formal proof-assistant certificate or a physical simulation.

## 1. Audited source and preservation

Frozen source directory: `/workspace/shared/five-signal-planar-realization60-20261004`.

- `PROOF.md`: SHA256 `e0ddd64cdbbb5c7f448266ab58f1dfeb2868892ac0f230632b2337e4d0bed065`
- `static_planar.py`: SHA256 `1ae26d3f2e671ac1b0675d547e646bc56923304205af3b72114ca06faa3e303f`
- `PACKET_MANIFEST.json`: SHA256 `8b21f8aed0eeec382c881eaeddbfda547f8bb00a5ed1f3dd2a928e54b410886c`

All 79 manifest entries have the recorded byte lengths and hashes. The entire proof, README, and author source were inspected as inert text. The 75 fixture JSON files were parsed as inert data. No author compiler, checker, upstream code, saved collision runner, or physical simulator was executed. All executed mathematical reconstruction is the new, separately inspected `independent_static_audit.py` in this review directory.

`frozen_inventory_before.json` and `frozen_inventory_after.json` agree exactly on every source-tree entry's bytes/hash, size, mode, and nanosecond mtime. No frozen source entry was modified. Access times were not an audit invariant.

The review covers the complete physical proof, the source implementation, the finite evidence, the temporal claims, and the logical interface of Section 8.1. Section 8.1 explicitly depends on the separately authored spectral classification; this review does not turn that unpinned external theorem into an independently certified part of the physical packet. Its application hypotheses and displayed conditional formulas were checked.

## 2. Main mathematical conclusion

For every rational 2-by-2 matrix A with positive determinant and every positive rational lambda, the packet supplies a finite rational-speed deterministic number-preserving signal machine, an exactly five-live-signal outgoing section, and a complete finite binary-collision word. The word returns centered homogeneous coordinates by lambda times diag(1,A), restores all marker labels and the messenger's left-anchor outgoing phase, and has exactly the stated bounded rational open chamber containing its center. Consequently its infinite-word domain is precisely the intersection of the iterated preimages of that chamber.

The proof establishes existence after A and lambda are fixed. It does not establish minimality, one unchanged finite machine for all A, a polynomial-size compiler, a negative-determinant obstruction, or an extension through a Zeno accumulation. Those exclusions are accurate and material.

## 3. Primitive chronology and no hidden contacts

### 3.1 Anchor scale (proof lines 28–46; source lines 104–131)

For a positive scale u, let h=(u−1)/(u+1). Then −1<h<1. The moving target's line, after its launch at time z, is z+h(t−z). Its meeting with the messenger returning from the anchor on the line t−2z occurs at t=(u+2)z and position uz. Thus the four principal contacts are exactly those printed in the proof, and the duration is 2(z+uz).

Let the unchanged inner spectator distances be 0<s1<...<sk<min(z,uz). Their four sets of crossing times are s_i, 2z−s_i, 2z+s_i, and 2z+2uz−s_i. These are respectively in outward, reversed, outward, and reversed order. The strict endpoint inequalities place every group strictly between the appropriate principal contacts. In particular there is no missing third outward spectator crossing after the first anchor bounce.

The target travels monotonically between z and uz. Requiring both endpoints inside the same open neighbor interval therefore prevents every target/stationary-marker contact. The messenger travels monotonically on each specified leg; all stationary points on that leg have been listed, while all outer markers lie beyond the leg's maximum extent. The inequalities −1<h<1 ensure separation immediately after launch and a unique return intersection. These observations exclude both hidden messenger contacts and remote marker contacts, not just collisions at the printed endpoints.

If a prospective endpoint reaches a stationary neighbor, the target contacts that neighbor by that checkpoint. If it crosses one, continuity forces an earlier contact. Equality can produce a simultaneous contact or collapse a prescribed interval. Every possibility destroys the selected globally separated complete binary word even if the identity completion subsequently lets some strands continue. The same argument applies at the anchor as a lower endpoint.

### 3.2 Reflector homothety (proof lines 48–56; source lines 133–157)

With h=(1−v)/(1+v), solving z's returning messenger line against the launched target gives t'=vt+(1−v)z and restoration time 2z−t'. The target is required to be nearest to the anchor. Its entire moving segment lies in the interval between its old and new positions, so 0<t,t'<s excludes contacts with every unchanged marker, including intermediate spectators and reflector.

For a spectator q, the two messenger crossings are q and 2z−q. Since both target endpoints are below the nearest spectator, these are ordered before the reflector and between the reflector and target restoration as claimed. Restoration precedes the final anchor bounce because t'>0. The outgoing and returning messenger legs each have only their indicated target intersection, using the strict speed bounds. Hence the 4+2k event count is complete.

The same first-contact argument proves necessity. A nonpositive final target position reaches the anchor by or before the prospective restoration; a target beyond the nearest unchanged outer marker reaches that marker first. No physical continuation after such an obstruction is assumed in deriving the contradiction.

### 3.3 Translation and the omitted internal row (proof lines 58–66; source lines 159–163)

Write k=t/(1−e) and f=t+ez. The elementary identity

    k−f = e(f−z)/(1−e)

makes the reduction of guards explicit. If 0<e<1 and f<z, then t<k<f. If e<0, then f<k<t whenever t<z. If e=0 all three endpoints coincide. Therefore, on the claimed guard 0<t,f<s<=z, the internal scale endpoint k is automatically inside the same neighbor interval. The translation discards no necessary extra condition.

Conversely, if the internal scale endpoint fails its interval, the scale already breaks the word; if it is valid but the final endpoint fails, the homothety breaks the word. This is the appropriate first-obstruction proof for a grouped translation. It avoids treating the final affine formula as a real trajectory after an earlier obstruction.

Parameters equal to zero do not yield empty words or simultaneous principal contacts: the target remains stationary at a positive distance, and its messenger partner still has speed +1 or −1. Temporary zero-speed labels are legal.

### 3.4 Transfers and reflection (proof lines 68–70)

A transfer has all four markers stationary, and its three positive times follow immediately from the section order. There is no time-zero switch of anchor. Reflection about D preserves all distance inequalities and durations while reversing every physical velocity. The source's right-anchor distance and position assignment correctly implements this reflection.

## 4. Signed shears, every pivot branch, and phase closure

For an x micro-shear, the two translations add delta*y and −2delta*D/3. Their sum is delta*Y. For a right-anchor micro-shear, r=D−y and s=D−x give r'=r+t(s−2D/3). Since s−2D/3=−X, converting back gives y'=y+tX. The lower shear has the same sign as t.

The subdivision N=max(1,ceil(4|t|)) puts every delta in [−1/4,1/4]. At the center, each completed micro-shear returns to its center target position; its intervening endpoint is between D/6 and D/2. Both are strictly within the neighbor interval ending at 2D/3. Center strictness survives arbitrarily many finite factors. The 4N+4 guards retain every translation-group endpoint; the translation lemma supplies its hidden internal endpoints. The 18N event count includes both far-reflector spectator crossings on every micro-step.

Direct multiplication verifies all three SL2 formulas in proof lines 115–147. The nonzero-c formula never divides by a or d, so zero diagonal pivots cause no problem. The upper-triangular branch divides only by its explicitly nonzero b. The diagonal branch first establishes a!=0 and works unchanged for negative a. The implementation multiplies each chronological shear on the left of the accumulated product, so it uses the correct rightmost-first column-vector convention.

The messenger begins at L. The c!=0 branch has x,y,x and two transfers; the b!=0 triangular branch has y,x,y and four transfers, including both endpoint transfers; the diagonal branch has y,x,y,x and four. There is no lost initial or terminal right-anchor phase.

For B=I the diagonal list y(−1),x(0),y(1),x(0) remains present. It has K=10, T=4 and 192 events before any lambda suffix. Its independently reconstructed chamber has positive area 4/27, and its center duration is 20176/315. Thus the identity is a substantive closed word, not an empty-word loophole.

## 5. Centered dilation: the decisive positive-determinant step

The map L_x(q) followed by T_D((1−q)/3) sends x to qx+(1−q)D/3, exactly giving X'=qX. It leaves y and D unchanged. On 3/4<=q<=5/4 the first scale is positive, and e=(1−q)/3 is in [−1/12,1/12], so every primitive speed and sign hypothesis holds. At the center, its explicitly retained endpoints are D/3, qD/3, D/3, all strictly below the neighboring 2D/3.

Importantly, the scale endpoint qx cannot be dropped merely because the starting and final positions are valid. The exact rational witness q=5/4, x=1/2, y=3/5 has final x=13/24 in (0,y), while qx=5/8 exceeds y. The packet correctly retains the corresponding guard. By the translation lemma no additional row is needed for qx/(1−e). This block has 14 events, eight supplied guards, and three temporary labels, as claimed.

For any rational q>0 different from one, the points u_j=1+j(q−1)/H all lie between 1 and q. Thus u_j>=min(1,q)>0, and the stated choice of H implies |u_j/u_(j−1)−1|<=1/4. All small factors are rational, positive and legal; their product telescopes to q. This argument covers q<1 as well as q>1 without square roots. Omitting the determinant dilation at q=1 does not make the whole realization empty, since the SL2 word remains.

Finally B=diag(q^−1,1)A has determinant one. Performing B first and then C_q gives C_q B=A. Reversing that order would be wrong in general, but neither the proof nor the source reverses it.

## 6. Global scaling, finite completion, and exact chamber

For lambda<1, scaling X,Y,D in that order puts already-scaled inner neighbors below both endpoints and untouched outer neighbors above both. For lambda>1, D,Y,X is the correct reverse order. The outermost D scale legitimately has no upper neighbor. The three primitive counts are 4,8,12, including all inner spectator crossings. Their sum is 24, and there is no extra guard.

Every explicit rule has a unique messenger phase Q_j. Thus distinct event positions cannot collide in the rule table's input key. The temporary marker speed is strictly inside (−1,1), whereas every messenger phase has speed ±1, so both the incoming and outgoing pairs have distinct speeds. The final Q_0 is right-going at L, with all four permanent marker labels restored. Identity output on all other legal collision sets is finite, deterministic and cardinality-preserving. Unprescribed contacts still count as contacts and cannot be silently erased from a complete-word specification.

At a collision or the initial anchor section, the live count is understood as the two outgoing strands plus the three other strands, rather than a count of occupied spatial sites. This is consistent with the standard initial-collision convention: [Becker et al., Abstract Geometrical Computation 8](https://arxiv.org/pdf/1307.6468), Definition 1 and the configuration discussion on PDF pages 4–5, permits distinct-speed outgoing signals at a common initial location and requires distinct speeds within both sides of a collision rule. That primary source was checked in this audit.

Every retained endpoint row is rational and homogeneous in (D,X,Y), since all prior return maps are rational and homogeneous. All are strict at the center. The first block's initial rows enforce 0<x<y<D even if the first block is right-based, because 0<r<s<D is equivalent to that order. Therefore the normalized intersection is full-dimensional, convex and bounded.

Sufficiency follows by concatenating the exact primitive words, while necessity uses the first endpoint obstruction with a previously valid prefix. The proof does not assume that an invalid affine continuation is physical. Repeated or redundant rows do not invalidate exactness; “necessary” means the conjunction characterizes precisely the word domain, not that every row is an irredundant facet.

The alphabet/event/guard formulas agree with counting the explicit grammar. The distinction between five live signals and the much larger finite meta-signal alphabet is maintained throughout.

## 7. Repetition, Zeno behavior, and rational accumulation time

Complete restoration of the labels and outgoing phase licenses literal repetition. Dividing the homogeneous return by D'=lambda D yields w'=Aw. Thus infinite complete-word validity is exactly membership in every A^(-n)P, including n=0; no closure or invariant replacement polygon is substituted.

Each primitive duration is a rational homogeneous row. Before the suffix, the scale endpoints and reflector distances are within [0,D]. This gives the displayed upper bounds of 6D per translation, 12D per micro-shear, 10D per centered dilation, and D per transfer. The suffix has duration 2(1+lambda)(x+y+D)<6(1+lambda)D. Every retained micro-shear contains a far-reflector homothety of duration 2D. Since at least one remains even at the identity, the stated lower bound holds.

Consequently the n-th duration is bounded above and below by positive constants times lambda^n D_0 along any valid orbit. The Zeno equivalence lambda<1 follows, and the whole n-th macro stays inside [0,max(1,lambda)D_n], proving spatial accumulation at L in that case.

The cyclic-subspace repair to the accumulation-time formula is correct. For rational z and rational N, V=span_Q(z,Nz,N²z) is rational and invariant by Cayley–Hamilton. Bounded normalized valid orbits and lambda<1 imply N^n z tends to zero. Since z is cyclic on V, no eigenvalue of modulus at least one can occur in the restriction. Hence (I−N)|_V is invertible over the rationals, giving a rational total time. The packet correctly declines to use the full inverse when it can be singular.

## 8. Conditional spectral corollary and scope

The physical construction meets the companion theorem's stated requirements: A rational, P a bounded open convex rational polygon, and 0 interior. Its claimed nonsemialgebraicity criterion and contact formulas are correctly presented as consequences of that separate theorem, not as newly proved by the physical compiler.

For a rational positive definite Q and a nonconstant guard h_i w<b_i, the formulas d_i=h_i Q^−1 h_i^T, r_i²=b_i²/d_i and p_i=(b_i/d_i)Q^−1 h_i^T have the correct tangent-point normalization. Initial-order boundary exclusions on a contained nondegenerate ellipse are finite, so deleting those from a dense rejected tail does not spoil the density argument. The finite highest-nonzero-homogeneous-component replacement of a polynomial sign along a positive ray is legitimate, including the case when every component vanishes. The resulting positive-gap obstruction is conditional on the companion's dense accepted/rejected tails, exactly as stated.

No independent novelty, minimality, or exhaustive literature judgment is supplied by this audit. The unverified retrieval of the older AGC6 manuscript is disclosed by the packet rather than hidden. Nothing in that attribution is used as an unproved physical construction lemma.

## 9. Independently reconstructed evidence

The independent source was written in this review directory, inspected in full, and then run normally and with Python optimization. Both runs succeeded with identical reported output. It reads the source packet only as JSON/text, uses exact `Fraction` arithmetic and an explicitly prescribed symbolic grammar, and never selects the next collision or advances physical particles.

Results in `independent_results.json`:

- All 75 fixture JSON objects match the reconstruction exactly, across every field: factors, all 7,020 supplied guard records, primitive phase metadata, all 24,678 event/rule records, all speeds, full return rows, duration rows, counts, and completion declaration
- All three pivot branches, both global-scaling orders, identity/negative identity, negative diagonals, zero diagonal pivots, and determinant factors above and below one are included
- Independent rational half-plane clipping computes the entire closed polygon corresponding to each strict chamber, verifies every vertex against every guard, and finds positive exact area in all fixtures; the largest polygon has eight vertices
- Duration rows obey the claimed bounds throughout each chamber closure and strictly at the center, not just on a sampled orbit
- A separate algebra sweep checks every 2-by-2 integer matrix with entries from −3 through 3 and positive determinant, comprising 1,056 matrices; all factorization branches and near-one products pass
- Additional scalar factors are 1, 3/4, 5/4, 1/17, 17/16, 16/17, 101/97 and 97/101
- The author summary independently agrees with all 75 reconstructed fixture descriptors, hashes, counts and center durations, and the source manifest covers exactly the intended file set
- The intermediate-dilation-guard necessity witness is recorded exactly

The source-bound finite evidence supports the all-parameter argument; it does not replace the continuity, monotonicity, speed-separation, and first-obstruction proof of exact chronology.

## 10. Audit artifacts

- `REVIEW.md`: this review
- `independent_static_audit.py`: separately authored inspected static reconstruction
- `independent_results.json`: fixture-by-fixture hashes, reconstructed counts, exact chamber vertices/areas, duration results and algebra sweep
- `run_stdout.json` / `run_optimized_stdout.json`: identical successful runs
- `summary_consistency.json`: independent summary/manifest consistency receipt
- `frozen_inventory_before.json` / `frozen_inventory_after.json`: exact source-preservation evidence
- `REVIEW_MANIFEST.json`: hashes of this review packet, excluding the manifest itself

**No blocking defect, necessary correction, or unsupported expansion of the main physical theorem was found.**
