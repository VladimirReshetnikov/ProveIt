# Audit: an isolated, prospectively stable parallel-swap lemma

## Result

The proposed construction works on the entire binary full shift with the explicit constants

\[
H=2(b+r),\qquad R_{\mathrm{elig}}=2b+3r,\qquad R_{\mathrm{output}}=3(b+r).
\]

Here a swap changes only coordinates within distance \(b\) of its anchor, while each raw candidate predicate reads coordinates within distance \(r\) of its anchor. The number of candidate/gate types does not enter these radius bounds. The prospective check must compare the **complete set of raw candidate keys**, including their type labels, within anchor distance \(b+r\), not just candidates of the current type and not just currently eligible candidates.

The construction is a safe replacement for a sequence of local involutions when the separate simulation argument shows that the intended moves pass its tests. It does not, by itself, equal an arbitrary ordered product on all configurations.

## Precise setup

Let \(X=\{0,1\}^{\mathbb Z}\), let \(G\) be a finite set of types, and let \(0\leq b\leq r\) be integers. Write \(I_a(u)=[u-a,u+a]\cap\mathbb Z\).

For each type \(g\), choose its own finite write block \(W_g\subseteq I_b(0)\) and two distinct binary words \(p_g,q_g\) on \(W_g\), with the same number of ones. Define \(\tau_{g,u}\) on all of \(X\) by exchanging these two words on \(u+W_g\), leaving every other word on that write block and every coordinate outside \(u+W_g\) unchanged. In particular, bits in \(I_b(u)\setminus(u+W_g)\) are arbitrary and are retained, rather than being required to be zero or overwritten. Thus

\[
\tau_{g,u}^{\,2}=\mathrm{id},
\]

and every nontrivial application preserves the number of particles on its support.

Let \(c_g(x,u)\) be a Boolean, translation-covariant raw-candidate predicate determined by \(x|_{I_r(u)}\). Require that \(c_g(x,u)\) implies that \(x|_{u+W_g}\) is either \(p_g\) or \(q_g\), in translated coordinates. The predicate may additionally require exactness or empty padding in a larger type-specific read window. The intended symmetric-guard assumption is

\[
c_g(x,u)=c_g(\tau_{g,u}x,u).
\]

The argument below uses this natural hypothesis to ensure that the same candidate key represents both orientations. In fact the stronger prospective test would itself enforce persistence of the selected key.

A key is a pair \(k=(g,u)\). Define

\[
C(x)=\{(g,u):c_g(x,u)=1\}.
\]

Multiplicity matters: two different types at the same anchor are two different keys. Endpoint orientation is not an extra key; both endpoints belong to the same key.

## Eligibility and the parallel map

Fix \(H=2(b+r)\). A key \(k=(g,u)\) is eligible in \(x\) if all three conditions hold:

1. \(k\in C(x)\).
2. **Raw-key isolation:** there is no \(\ell=(h,v)\in C(x)\setminus\{k\}\) with \(|v-u|\leq H\).
3. **Prospective stability:**
   \[
   C(\tau_kx)\cap(G\times I_{b+r}(u))
   =C(x)\cap(G\times I_{b+r}(u)).
   \]

Let \(E(x)\) denote the eligible-key set. Define \(F(x)\) by applying \(\tau_k\) simultaneously for all \(k\in E(x)\).

There is no infinite-product issue: distinct eligible anchors have distance strictly greater than \(H\geq2b\), so even their containing intervals \(I_b(u)\) are disjoint. Each output coordinate belongs to at most one eligible write block.

## Theorem

For every \(x\in X\), the map above satisfies

\[
C(Fx)=C(x),\qquad E(Fx)=E(x),\qquad F^2x=x.
\]

It is therefore a reversible, particle-conserving cellular automaton of radius at most \(3(b+r)\). No well-formedness, finite-support, or admissibility assumption on \(x\) is needed.

Here particle conservation means that every selected disjoint finite block preserves its number of ones; in particular total particle number is preserved on every finite-particle configuration. On arbitrary configurations the map has bounded-displacement local particle transport, rather than an assertion about equality of two divergent infinite sums.

## Proof

### 1. The finite prospective check is a global candidate-set check

A swap anchored at \(u\) changes only \(I_b(u)\). A candidate anchored at \(v\) reads only \(I_r(v)\). If \(|v-u|>b+r\), these intervals are disjoint, so that candidate's status cannot change. Thus condition 3 is equivalent to

\[
C(\tau_kx)=C(x).
\tag{1}
\]

This equivalence concerns the raw predicates only. It is neither recursive nor a check of other keys' eligibility.

### 2. No candidate window can see two eligible moves

If a candidate read interval \(I_r(v)\) meets an eligible support \(I_b(u)\), then \(|u-v|\leq b+r\). Were it to meet two eligible supports, their anchors would have distance at most \(2(b+r)=H\), contradicting isolation.

Consequently, for every raw key \(\ell=(h,v)\), its read block in \(Fx\) is either unchanged from \(x\), or agrees with its read block in \(\tau_kx\) for exactly one \(k\in E(x)\). In the latter case (1) gives

\[
c_h(Fx,v)=c_h(\tau_kx,v)=c_h(x,v).
\]

This proves \(C(Fx)=C(x)\). In particular, it rules out cooperative candidate births: two separately harmless eligible rewrites never simultaneously affect the same candidate test.

### 3. Identify the complete read neighborhood of a prospective test

For a key anchored at \(u\), condition 3 examines candidate anchors in \(I_{b+r}(u)\), and each such candidate reads a radius-\(r\) interval. It is therefore determined by

\[
x|_{I_{b+2r}(u)}.
\tag{2}
\]

Producing the hypothetical \(\tau_kx\) requires no additional coordinates: its type-specific write block is contained in \(I_b(u)\), which is already in that interval.

Write \(P_k(x)\) for condition 3, defined using the globally defined involution \(\tau_k\). Because applying \(\tau_k\) twice is the identity, equality of the two candidate sets is symmetric, so

\[
P_k(\tau_kx)=P_k(x).
\tag{3}
\]

Thus the prospective test is unchanged by the candidate's own swap as well as by modifications outside (2).

### 4. Every isolated raw candidate retains its eligibility status

Since \(C(Fx)=C(x)\), raw-key isolation is identical in \(x\) and \(Fx\). Consider any isolated raw candidate \(k=(g,u)\), whether or not it is eligible.

Every other eligible key \(\ell=(h,v)\) is a different raw candidate, so isolation gives \(|v-u|>H=2b+2r\). Its support \(I_b(v)\) is therefore disjoint from \(I_{b+2r}(u)\). No other eligible move affects the complete prospective-test neighborhood (2).

If \(k\notin E(x)\), that neighborhood is unchanged by \(F\), and \(P_k(Fx)=P_k(x)\). If \(k\in E(x)\), it is changed there only by \(\tau_k\), so (3) again yields \(P_k(Fx)=P_k(x)\).

Nonisolated candidates remain nonisolated, and noncandidates remain noncandidates. Hence all keys retain eligibility and \(E(Fx)=E(x)\).

This step is essential: merely showing that already eligible keys remain eligible would not rule out additional moves on the second application.

### 5. Involution

The second application uses exactly the same disjoint supports and the same type labels. Each \(\tau_k\) is an involution, so it restores its original endpoint block. Every untouched coordinate remains untouched. Therefore \(F^2x=x\) on the entire full shift.

### 6. Locality and radius

For a key anchored at \(u\):

- Checking its own candidacy reads radius \(r\).
- Checking isolation examines all raw-candidate anchors at distance at most \(H\), and hence reads radius \(H+r\).
- Checking prospectivity reads radius \(b+2r\), by (2).

Thus eligibility reads radius

\[
R_{\mathrm{elig}}=\max\{r,H+r,b+2r\}=2b+3r.
\]

To determine output coordinate \(i\), one checks only potential selected supports anchored at distance at most \(b\) from \(i\). Hence

\[
R_{\mathrm{output}}
\leq b+R_{\mathrm{elig}}
=3b+3r.
\]

Finiteness of \(G\) makes these finite Boolean tests. Adding more gate types may enlarge their computation or truth-table size, but does not enlarge their coordinate radius. Translation covariance of the raw predicates and endpoint swaps makes \(F\) shift commuting.

## Compiler/application checklist

1. Bound the **actual changed support** by \(I_b(u)\) and the **complete raw predicate read support** by \(I_r(u)\), including zero padding, contextual guards, and endpoint recognition.
2. Use a single type label for the two orientations of a swap. If an implementation records oriented candidates, compare after the known orientation-reversal identification; literal equality of oriented labels would reject every nontrivial swap.
3. Apply isolation across **all** raw types. A candidate of another type at the same anchor must count as a conflict.
4. Evaluate the prospective test on the original configuration with **only this one swap applied**. Compare all raw types at every anchor in \(I_{b+r}(u)\).
5. Use \(H=2(b+r)\) with exclusion at distances \(\leq H\). A smaller exclusion might work for a special predicate family, but disjoint rewrite supports alone do not justify it: read windows and prospective-test windows are larger than changed supports.
6. Prove separately that every intended move on the well-formed configurations passes these tests. In particular, a locally isolated candidate can fail prospectivity if its swap creates or destroys another raw candidate nearby.
7. If a valid state has exactly one raw key globally and applying its swap still leaves exactly that same raw key, eligibility is immediate. Several intended moves are also permitted if their keys satisfy the stated separation and each is prospectively stable.

## Direct audit of the suggested simplified candidate family

There is no need to retain an earlier, same-type isolation test inside the raw candidate predicate solely for this theorem. Exact endpoint recognition plus the original symmetric contextual guard is sufficient, provided its whole read neighborhood is included in \(r\). The new all-type isolation and prospective check supply the full-shift safety argument. Whether deleting the old test exposes additional raw keys on intended valid configurations is a separate application-specific question that must be checked.

### `parallel_particles.py` formulation audit

The implementation is consistent with the type-specific-write-block version above:

- For a frozen compiler gate, take \(W_g=I_{B_g}(0)\), \(b=B_3\), and regard `P` and `Q` as supports of words on \(W_g\). `Pattern.isolation` is the distinct **read/exactness** radius \(L_g=3B_g+1\), not the write radius.
- `candidates` requires exactly the selected endpoint particles in \(I_{L_g}(u)\) and then checks the guard. `swap` and the simultaneous update remove the old endpoint support and insert the new endpoint support. They retain all other particles, including those in \(I_{B_3}(u)\setminus I_{B_g}(u)\). This is precisely the restriction of the globally defined \(\tau_g\) to candidate configurations.
- The pair templates can have \(L_2<B_3\), which is allowed. Their raw predicates do not need to inspect or constrain all of \(I_{B_3}(u)\).
- The edge read bound `Z+J` covers every exactness window and both class-guard windows. The phase read bound `3*B3+1` covers every phase exactness window. Compiler class guards inspect only offsets \(\pm(Z+k)\), \(0\leq k\leq J\), outside the changed support, and are therefore symmetric.
- `eligible` compares sets of `(type_index, anchor)` keys within `r+b`; orientation values are deliberately excluded. It separately verifies reversal of the selected orientation. `H=2*(b+r)` and `radius=3*(b+r)` match the lemma.
- `local_output` looks for possible writing anchors within distance `b`, checks raw isolation within `H`, and compares prospective candidate keys within `r+b`. Every queried predicate fits in the advertised output neighborhood.

This is a source-level audit, not a claim that the full regression suite was rerun here. The generic `ParallelBlock` constructor accepts arbitrary guard objects without checking their read support or purity. The theorem applies to such custom objects only under the stated locality/symmetry contract; the frozen compiler's `_ClassGuard` satisfies it. The interpreter enumerates finite particle supports, while the theorem supplies the extension to all bi-infinite configurations.
