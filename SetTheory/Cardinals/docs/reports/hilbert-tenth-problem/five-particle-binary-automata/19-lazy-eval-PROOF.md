# Lazy exact evaluation of the frozen ordered binary CA

## Status and scope

This is a new finite-support evaluator of the **same ordered CA composition**, not a new CA rule and not a source-machine shortcut. Its correctness claim covers every finite subset of the integers, including malformed encodings, multiple heads, competing raw keys, dense clusters, and non-admissible source modes. It does not evaluate arbitrary infinite configurations. The frozen construction already establishes the full-shift CA and its bijectivity; the theorem below establishes equality of this finite-support implementation with its finite ordered product.

The reference compiler is the byte-identical `frozen_reversible_binary.py`, SHA-256 `f95a6028c9d3cc6f8b0b497cfc0cad68104da6d70e55205df04ad234e5d0c76f`. `lazy_reversible.py` checks the adjacent file's bytes **before executing them**, then executes precisely that checked byte string. It never resolves the reference by an unpinned search-path import. The parser/guard evaluator and immutable Gate/Branch representations are reused; the eager compiler is called only by tests on small sources.

The universal table used only by the benchmark is SHA-256 `fa61d06178d718511232a80a05e02192d940fde3c273f0c202f0623253b2ade3`. No universal factor array, binary local truth table, or array indexed by all factor positions is built.

## 1. Metadata and the exact factor order

Write m for controls, p for nonzero branches, a for zero branches, and b=p+a. Their order is the input order, with the same order-preserving filtering as the frozen compiler. Put

- D=2m+4p, S=2D+2, B2=D+1, L=3D+4, B3=4D+5
- Z=10B3+10+2J
- r=L-S+1=D+3
- U=2D+6, A=4D+15, V=2D+7, C=4D+14

Home signed gaps are 2q+1,2q+2 for zero-based control q. Branch e's outbound gaps are 2m+4e+1,2m+4e+2, and inbound gaps are 2m+4e+3,2m+4e+4. In each pair the odd gap is plus.

There are pA+a E factors followed by pC+m P factors. The total is

F=8pD+29p+m+a.

For moving branch e and kind k=0 (O),1 (I), the E base is eA+kU:

- free: base
- behind(t), S<=t<=L: base+1+t-S
- ahead(t), S+1<=t<=L: base+(D+3)+t-S

Dispatch, endpoint, commit are at eA+4D+12, eA+4D+13, eA+4D+14. Zero branch j is at pA+j.

For the P block, add |E| to every following index. Branch e, kind k has base=eC+kV:

- phase-free: base
- phase-near(-,t): base+1+t-S
- phase-near(+,t): base+D+4+t-S

Home q is at pC+q. `gate_at(i)` inverts these arithmetic partitions and constructs just that gate. The constants, supports, contextual domain/image table, name, and radius are identical to the frozen factor at i. No iteration over a travel interval occurs.

### Source-validation equivalence

Primitive type/schema validation, guard parsing, and guard-program evaluation use the pinned original functions. Every branch is checked over the same (J+2)^2 representative counter classes, including the exact inverse-image guard and negative-pre/post-counter checks. Boolean values are rejected as integers. Outgoing and incoming class sets are represented as integer masks indexed by control. A class bit belongs to two domains/images exactly when the original sum at that control/class exceeds one.

All rows are parsed before overlap rejection, preserving the original validation order. Conflict masks are inspected in control order, least counter-class order, and domain-before-image order, also preserving the original overlap-error precedence and messages. The accepted source set and computed immutable branch tables therefore agree. This replaces the reference validator's repeated all-branches scan per control, without changing its condition.

## 2. Discovering every potentially nonidentity factor

Given finite support X, inspect every occupied pair (h,h+d), h<h+d, with 1<=d<=D. The gap uniquely identifies its signed mode. Every two-particle gate endpoint is one such pair.

Every three-particle endpoint has **exactly one close pair** of gap at most D. Its other particle z is at distance at least S from the head anchor h, so its distance from either head particle is at least S-D=D+2>D. This remains true at the translated reverse endpoint: there the marker's coordinate is shifted, but its relative head distance is S. Thus enumerating all occupied close pairs and every distinct third particle finds the close pair and singleton of every raw triple, even when X itself has many other close pairs. It is not necessary to identify a unique head globally.

Let H=h-z and let delta_sign be 0 for a plus gap, 1 for a minus gap. For a moving mode with travel direction w:

- behind predecessor t=wH-delta_sign, retained when S<=t<=L
- ahead predecessor t=-wH+delta_sign, retained when S+1<=t<=L
- phase-near: t=|H|, side=sign(H), retained when S<=t<=L

A free and phase-free factor for that moving mode are candidates for every detected close pair. The interaction candidates are:

- O_e plus, H=-vS: endpoint
- O_e minus, H=vS: dispatch
- I_e plus, H=vS: commit
- I_e minus, H=-vS: endpoint

Here v=e.side. For H_q plus with H=S, add all source-adjacent moving dispatch and zero-update direct factors; for H_q minus add all target-adjacent moving commit and zero-update direct factors. Either home sign adds its home-phase factor. Control-to-factor incidence is stored in O(b) entries.

Candidate discovery deliberately does not test raw-window emptiness, isolation, competing keys, or context. It can therefore return false positives. The property needed is only:

**Candidate completeness.** If factor i has any raw key in X, then i is emitted.

The unique-close-pair argument and the complete endpoint equations prove this. In particular, a factor absent from the candidate set is the identity on X. Candidate discovery never scans all t in [S,L] or all moving modes.

## 3. Exact evaluation of one factor

`apply_gate` is extensionally the original `Gate.apply` on finite supports.

1. For each of the two sorted shapes and each occupied coordinate first, set u=first-shape[0]. A raw occurrence's least occupied site must appear in this enumeration. Check all two/three required sites and count ones in the **closed** interval [u-B,u+B] by binary search in sorted X. This is exactly the original raw definition.
2. Keep every raw key, including keys that will fail isolation or context. A key has another raw key within distance M if and only if its immediate predecessor or successor in the sorted raw-key list is that close. This implements the original exclusion over all raw keys.
3. Count [u-(3B+1),u+(3B+1)] inclusively. This is exactly the original isolation test.
4. For contextual gates, inspect the two closed intervals [u-Z-J,u-Z] and [u+Z,u+Z+J]. Zero particles gives class J+1, one gives its exact offset k, and more than one rejects the guard. This is exactly `_ClassGuard.allows`, without a scan over J+1 sites.
5. Compute the entire active-key list from the same pre-factor X. Only then replace every active endpoint. The original isolated-swap lemma makes these simultaneous supports disjoint. The inverse endpoint's invariant old-marker key, and free minus endpoint's predecessor-anchor key, are recovered by the exact original shapes, not guessed from the current marker/head anchor.

Optional verification explicitly checks mass, raw-key invariance, and the factor's involution. These checks use raises, not asserts, and remain active under `python -O`.

## 4. The ordered-evaluation theorem

**Theorem.** For every source accepted by the frozen compiler and every finite support X, `compile_lazy_source(source).step(X)` equals the frozen eager `compile_source(source).step(X)`. With inverse=True it equals the original factors applied in exactly reverse order.

**Proof.** Maintain the current support and the last processed factor index. Generate the current candidate set. Process its remaining indices in ascending order (descending for inverse). Any intervening noncandidate factor has no raw key, by candidate completeness, hence is an identity on the unchanged current support. Execute a selected factor by the exact simultaneous algorithm above.

If it is the identity, the current candidate set remains valid. If it changes support, advance the cursor past this factor and regenerate candidates from the new support before doing anything else. Factors created at already-passed indices are correctly ignored, since the frozen product does not revisit them. Newly created future candidates are found. Context or eligibility changes are also reevaluated on the new snapshot. Induction on the remaining ordered factor indices proves identical supports. Each selected index advances strictly, so evaluation terminates after at most F factor checks. Descending order gives exactly the inverse product because each original factor is an involution. QED.

Consequently finite mass conservation, forward/backward roundtrips, and translation equivariance follow for all finite inputs from equality with the frozen product. This is a mathematical proof with independent code audit and finite differential tests, not a proof-assistant formalization.

## 5. Honest costs and remaining limits

Let n=|X|, c=(J+2)^2, G be total guard-program size, and Delta the maximum number of incident dispatch/direct or commit/direct entries for a home signed mode. Let K be the number of changing factors actually executed and A_test the number of candidate factors tested. Let C_X bound the number of candidates in any snapshot during this step. Always

- K<=A_test<=F
- candidate generations = K+1
- C_X <= F and C_X=O(n^3+n^2 Delta)

Metadata storage is O(m+b+G+bc) machine words, plus string/number payloads; the immutable source snapshot is included. With unit-cost exact integer operations and hash operations, guard tables cost O(cG+bc) work. The current dense integer-mask builder performs c growing-mask operations per branch; in a bit model its deliberately loose bound is O(bc^2) bit work, in addition to guard evaluation and integer comparison costs. Large binary-encoded J therefore remains expensive: this implementation retains the original explicit class-table validation. It does not claim polynomial cost in log J.

Under the customary constant-expected-time hash model, one step, excluding metadata creation and optional trace output, costs

O((K+1)[n log(n+1)+n^3+n^2 Delta+C_X log(C_X+1)]
  + A_test n log(n+1)).

The last term is sparse factor application; sorting and binary-search interval counts avoid a scan of the coordinate span or of J. Gate names have their actual string-copy cost as well. Work memory is O(n+C_X), beyond fixed metadata. With trace=True, stored active-key event records add O(Kn) coordinate words in the worst case; trace=False does not retain events.

Python integer/set operations are not unit-cost worst-case primitives. For a conservative adversarial-hash bound, candidate-set insertions and dictionary lookups can be charged their linear container sizes, and a factor's membership checks become O(n^2) rather than expected O(n). In particular, a loose deterministic container-operation bound is

O((K+1)[(n^3+n^2 Delta)(C_X+n+m+b+1)+C_X log(C_X+1)]
  + A_test[n^2+n log(n+1)]).

This is not claimed tight. It makes explicit that adversarial exact integer hashes cannot invalidate the algorithm, although they can reduce its speed. Source-validation dictionaries have the analogous collision degradation.

For coordinate bit complexity, let H0 bound initial |coordinate|. Every changing factor can match particles between its two supports with displacement at most 2B3. Throughout the step, all occupied coordinates therefore have magnitude at most H0+2KB3. Arithmetic used for reading contexts also reaches Z+J farther. A uniform bit bound is

W=O(1+log(1+H0+2FB3+Z+J)).

Coordinate additions/comparisons and integer hashing cost O(W) in the simple bit model; multiply appropriate coordinate-operation bounds by W. Factor indices use O(log(F+1)) bits. Occupied coordinate extent is never enumerated. This handles enormous positive and negative coordinates exactly.

**No input-independent small-K claim is made.** Factors are traversed in their true order, and malformed inputs can activate later factors through changes to geometry, isolation, context, or competitors. The worst-case bounds retain K and A_test, potentially as large as F. Since F=O((m+b)^2), avoiding its allocation still gives a finite polynomial-source-size algorithm, but not a general bound polynomial in log F independent of source size or cascade length. The benchmark's few tests per step do not establish a general constant bound.

## 6. A concrete cascade regression

Take controls q,h; one branch q->h, right-counter increment, true guard, J=0. Then D=8,S=18,B3=37. For outbound gaps d+=5,d-=6, use

X={-118,-112,0,18,23}.

The E free factor first moves the far pair, unblocking a later behind factor for the triple at origin. In the full step the changing global indices are 0,1,47,60, and the result is

{-119,-113,0,19,24}.

The E block and the P block each fail to be involutions on this malformed input. This is **consistent with the frozen proof**, which only identifies those whole blocks with matchings on admissible inputs; it proves global reversibility from individual factors and reverses their order globally. This fixture prevents accidentally extending the promised matching property to arbitrary inputs.

## 7. What the universal benchmark establishes

The pinned universal metadata has m=122622,p=66066,a=75495,J=0, D=509508 and F=269291358255. The benchmark executes 128 literal CA microsteps beginning at the published START,(1,0) particle support, checking each reverse step; it also executes 128 arbitrary endpoint/noise configurations drawn from factor indices across the entire range, again checking inverse and mass.

These are global evaluator calls. They do not jump to source boundaries, and they do not assume an encoded state when deciding which factor to apply. The 128 startup steps do **not** complete the long startup, simulate a whole Turing step, or establish halting. They demonstrate that finite global steps can be evaluated without materializing the huge factor array. Whole-composition equality is tested against eager composition on small sources and proved above; no eager universal oracle is claimed.
