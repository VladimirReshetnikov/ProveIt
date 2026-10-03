# Independent audit: lazy ordered reversible evaluator

## Scope and conclusion

The audited evaluator is `lazy_reversible.py`, against the byte-pinned frozen compiler `frozen_reversible_binary.py` (SHA-256 `f95a6028c9d3cc6f8b0b497cfc0cad68104da6d70e55205df04ad234e5d0c76f`). This audit covers arbitrary finite sets/frozensets of exact Python integers, not merely well-formed five-particle encodings. It does not certify the universality of any source table or upgrade the original mathematical proof to a machine-checked proof.

No semantic discrepancy remains in the inspected implementation. One validation-order discrepancy was found and corrected: overlap errors must be delayed until all rows have passed structural/type/guard validation. The revised conflict-mask pass also preserves the frozen control/class/domain-before-image error precedence and messages.

The all-input exactness argument below is independent of valid-encoding simulation. Finite tests provide regression evidence, not its replacement. `audit-receipt.json` records the exact tested implementation hash and counts. `audit_checks.py` reproduces the checks without building a universal factor array.

## 1. Exact factor indexing

Write `r=D+3=L-S+1`, `em=2D+6`, `es=4D+15`, and `pm=2D+7`. Nonzero branches have index `i` in their original filtered order. Their kinds are `k=0` for O and `k=1` for I.

The E mode base is `eb=i*es+k*em`:

- free: `eb`
- behind(t), `S <= t <= L`: `eb+1+t-S`
- ahead(t), `S+1 <= t <= L`: `eb+r+t-S`

The three interaction factors are at `i*es+2*em`, then `+1`, then `+2`, in dispatch/endpoint/commit order. Direct branch `j`, in its original zero-update filtered order, is at `p*es+j`. Thus

`E_count=p*(4D+15)+a`.

For global P indices, let `pb=E_count+(2i+k)*pm`:

- phase-free: `pb`
- phase-near(-1,t): `pb+1+t-S`
- phase-near(+1,t): `pb+1+r+t-S`
- phase-home(control j): `E_count+2p*pm+j`

Thus `P_count=p*(4D+14)+m` and total factors equal `8pD+29p+m+a` exactly. Inspection and exhaustive descriptor comparison on the small test sources confirm that `gate_at` realizes these ranges with precisely the original shape order, names, contextual tables, and radius constants.

## 2. Complete candidate discovery on every finite support

Every compiler triple endpoint has exactly one intrinsic close pair with gap in `[1,D]`. Its other particle is at distance at least `S-D=D+2>D` from both close-pair endpoints. Pair factors plainly have their unique pair. This is a statement about each raw support; a malformed entire configuration can contain arbitrarily many close pairs. The code correctly enumerates every increasing occupied pair of gap at most D.

Gap parity determines sign (odd = plus, even = minus). The first `2m` gaps identify home controls. Remaining gaps are grouped four per nonzero branch, in O+, O-, I+, I- order. Therefore a present raw occurrence has a unique enumerated close pair decoding its mode and sign. Its pair anchor `h` is always the leftmost pair particle, also for leftward motion.

For a moving pair and any distinct occupied singleton `z`, put `distance=h-z`, and let `delta_sign=0` for plus or `1` for minus. Moving direction is `w=e.side` for O and `w=-e.side` for I. The raw endpoint equations invert to:

- behind: `t=w*distance-delta_sign`, with `S <= t <= L`
- ahead: `t=-w*distance+delta_sign`, with `S+1 <= t <= L`
- phase-near: `t=abs(distance)` and side `sign(distance)`, with `S <= t <= L`
- dispatch reverse: O- and `distance=e.side*S`
- endpoint forward: O+ and `distance=-e.side*S`
- endpoint reverse: I- and `distance=-e.side*S`
- commit forward: I+ and `distance=e.side*S`

A home pair requires the uniquely determined singleton `z=h-S`. Plus endpoints enumerate all source-adjacent dispatch/direct factors, minus endpoints all target-adjacent commit/direct factors, and both enumerate their home phase factor. Enumerating all adjacency entries matters even when guards happen to be false: candidate completeness concerns raw shape occurrence, not a valid machine state.

The endpoint reverse singleton is the *new* marker. Its invariant raw key is `z-e.side*e.delta`, not `z`. The free reverse raw key is `h-w`, not its new head anchor. Candidate discovery only proposes the factor index; subsequent exact shape matching computes both keys from the actual frozen shapes, preserving these distinctions.

Consequently every factor with at least one raw occurrence appears in the candidate set. Extra candidates are harmless. No isolation, guard, or admissibility assumption enters this implication. If a factor is absent, it has no raw occurrence and therefore acts as the identity.

## 3. Ordered skipping is exact, including all cascades

Maintain a cursor through the global E-then-P factor order. In forward evaluation choose the next candidate strictly above the cursor; in reverse evaluation choose the next strictly below it. Apply exactly that factor, advance past it, and regenerate candidates whenever the support changes. Between changes, the current support and therefore the set of absent/identity factors is unchanged.

Induction on the original factor sequence proves equality with the frozen composition: all skipped factors are identities on the current support, every encountered nonidentity factor is performed in its original place, and already-passed factors are never revisited. If no remaining candidate exists, every remaining factor is an identity. The argument applies verbatim to descending factor order because each individual gate is its own inverse.

It is essential to regenerate after a change and not freeze eligibility for a block. It is also essential not to apply a block as an involution or reorder its factors. Both E and P can have cascades on malformed inputs (Section 6).

## 4. Sparse factor application is the same gate

`_raw_sparse` tests the same translated shapes and assigned keys as the original. Bisect counts give the exact number of occupied sites in each inclusive integer interval `[u-B,u+B]`. Hence its raw dictionary equals the original raw dictionary, independent of iteration order.

The isolation count likewise uses the same inclusive `[u-L,u+L]`. For sorted distinct raw keys, another key at positive distance at most M exists if and only if an immediately adjacent raw key is that close. Therefore the nearest-neighbor key check equals the original all-keys predicate. It uses **all raw keys**, including competitors that fail isolation or their contextual guard.

Because support entries are validated exact integers, the integer interval `[u-Z-J,u-Z]` is exactly the left set of J+1 contextual read sites, and `[u+Z,u+Z+J]` exactly the right set. Zero particles gives class `J+1`, one gives precisely its k, and multiple particles reject. Thus `_guard_sparse` equals `_ClassGuard.allows`, including malformed multi-one contexts.

All eligible keys are computed from the same original support before any rewriting. Rewrites are then the exact frozen paired substitutions. The compiler's gate lemma ensures their disjointness; the implementation additionally supports the same conservation, raw-key invariance, and involution verification. No new invariant of well-formed encodings is assumed.

## 5. Validation and storage audit

Primitive exact-type, schema, threshold, guard parsing, and class evaluation routines are reused from the byte-pinned reference. Domain and image tables are computed on the same representatives with the same natural-output test. A class bit is marked as conflicting exactly when two incident branches contain that class. Processing the lowest conflict bit in control order reproduces the frozen nested control/class scan, choosing domain before image when both fail at the same class.

Returned source data, branch data, adjacency maps, and control maps are immutable snapshots. No input containers are retained. The compiler does not construct E/P arrays or enumerate travel distances: it stores source-scale data and arithmetic counts. `gate_at` builds one factor on request. `step` stores support-dependent candidate indices and builds only selected factors. This is an evaluator, not a literal enumeration of the enormous local truth table.

## 6. Concrete malformed-input block cascades

Use two controls q,h and one true-guard right-increment branch e from q to h, with J=0. The constants are `D=8,S=18,B3=37`; O gaps are `5,6`; triple isolation radius is `112`.

For `X={-118,-112,0,18,23}`:

- P factor 0 changes the far-left minus pair `{−118,−112}` to `{−118,−113}`
- This removes the extra particle at the inclusive left boundary of the local triple's isolation window
- P factor 12, phase-near O on side +1 at t=18, can then change the local plus head `{18,23}` to `{18,24}`
- On the second P application the far-left pair moves back to include `−112`, blocking the local factor: `P(P(X))={−118,−112,0,18,24} != X`

The same X witnesses an E cascade:

- E factor 0 changes the far-left pair to `{−119,−114}`
- E factor 1, behind O at t=18, changes the local head to `{19,25}`
- A second E application restores the external pair and blocks the local reverse: `E(E(X))={−118,−112,0,19,25} != X`

All these steps passed the frozen per-gate verification. They directly demonstrate why any malformed-input evaluator must preserve fixed ordering and current-state eligibility.

## 7. Executable evidence

The audit suite compares every descriptor for five structurally diverse small sources, including no branches, zero-only branches, both movement sides and signs, interleaved zero/nonzero rows, and multiple source/target-adjacent guarded branches. It translates every gate endpoint to several ordinary and enormous coordinates and checks candidate inclusion. It compares sparse/original factor results at B, L, and M boundaries, with remote competitors and simultaneous eligible keys, and checks guard reads.

Whole-step comparisons include arbitrary unions of raw shapes, dense malformed overlaps, extremely distant clusters, both factor orders, and inverse roundtrips. Additional exhaustive comparisons cover every subset of two eleven-site universes around the cascade and endpoint boundary configurations. Validation fuzzing compares acceptance or exact exception class/message across randomized guarded sources. The receipt distinguishes all finite-test counts from the all-finite-input proof above.

## 8. Universal-source arithmetic and complexity limits

An independent read of the pinned source table (SHA-256 `fa61d06178d718511232a80a05e02192d940fde3c273f0c202f0623253b2ade3`) gives m=122,622, p=66,066, a=75,495, J=0, and 141,561 total source branches. Consequently D=509,508, E_count=134,645,688,597, P_count=134,645,669,658, and total F=269,291,358,255. These independently counted values and the no-factor-materialization check are recorded in `audit-universal-count.json`. This count audit does not execute or revalidate universality of that source.

Let b=p+a, c=(J+2)^2, and G denote the total size of parsed guard expressions. Source metadata has the source-scale bound O((m+b)c+G) words. Class evaluation takes O(cG) guard operations, with integer costs additional. In particular, the present Python integer-mask construction must not be described as constant cost per class bit: repeated shifts/ORs give O(b*c^2) worst-case bit work for that accumulation, in addition to guard evaluation and other parsing work.

For support size n, candidate generation takes O(n^3+n^2*Delta) unit-cost work, where Delta bounds the largest relevant source/target incidence list. Candidate sorting contributes O(C log C) for candidate-set size C. A sparse gate test takes O(n log n) unit-cost work, including sorted support/raw keys and interval checks. There are at most F tested factors A and at most A changing factors K; candidates are regenerated at most K+1 times. Thus the algorithm avoids mandatory enumeration of all F factors but has **no worst-case polynomial-in-log(F) guarantee**. Adversarial malformed configurations can still force large work.

Particle mass stays n, and each factor moves an involved particle by at most 2B3. After one full ordered step, coordinates are bounded in absolute value by the initial bound plus 2FB3. Their bit lengths are therefore bounded by the initial coordinate bit length plus O(log(FB3)); arithmetic also involves source constants such as J and Z. Python big-integer comparisons, arithmetic, and hashing must be charged by these lengths when claiming bit complexity. Neither compact metadata nor the sample timings establish a uniform fast evaluator for every finite input.
