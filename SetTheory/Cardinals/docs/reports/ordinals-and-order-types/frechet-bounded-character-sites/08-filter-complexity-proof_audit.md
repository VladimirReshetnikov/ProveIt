# Proof audit

This audit is an internal mathematical review, not independent refereeing or proof-assistant certification. All infinite results are proved in the accompanying article, with one explicit imported forcing-model input.

## Result ledger

| Article result | Content | Proof input and status |
|---|---|---|
| Lemma 2.2 | Finite-generation stage equals the positive quotient Boolean algebra | Direct filter calculation in ZFC. |
| Lemma 2.3 | Adding finitely many generators and forming compatible joint filters stays in the site | No regularity of kappa required. |
| Lemma 3.2 | Recovery of a filter from its ultrafilter-extension set | Uses ultrafilter extension; proved explicitly. |
| Theorem 3.3 | Regular-open representation and equivalence of dense covers with Boolean joins | Proved by the nonempty clopen base and matching-family extension. |
| Lemma 4.1 | aleph_1 <= p <= u <= c | Countable diagonalization; splitting a supposed ultrafilter pseudointersection. |
| Theorem 4.2 | Exact p threshold, including the obstruction to every complete event-preserving map | The definition of p plus the two different meets of one centered family. |
| Corollary 4.3 | Countably generated site has the original atomless completion | Uses aleph_1 <= p; does not use any additional axiom. |
| Proposition 4.5 | Exact zero-meet arity gap | A small family with positive new meet is centered, hence has an old positive lower bound below p. |
| Proposition 4.6 | A small filter's old-completion representative is the original interior of its Stone closed set | Every original neighborhood meeting that set admits a pseudointersection refinement. |
| Theorem 5.1 | Atom spectrum equals the small-character ultrafilters | Hausdorff clopens split two points; singleton opens recover ultrafilters. |
| Proposition 5.2 | Geometric points of the Booleanization correspond to atoms | Complete frame maps, not merely ordinary ultrafilters. |
| Theorem 5.3 | Full atomicity criterion and atomic/atomless factor decomposition | Complete Boolean distributivity of finite meets over arbitrary joins. |
| Proposition 5.5 | Less-than-kappa closure | Assumes kappa regular. No singular extension asserted. |
| Proposition 6.1 | Particular model properties involving small P-points and c = 2^aleph_1 = aleph_2 | **Imported:** Millán 2009, proof of Theorem 3.14. Not reproved. |
| Lemma 6.2 | There are 2^c free ultrafilters | Independent-family construction, given in full. |
| Theorem 6.3 | Three stages, including early atomicity and two distinct atomic algebras | Fully proved from Proposition 6.1 and the earlier ZFC theorems. |
| Proposition 7.1 | Finite–cofinite toy example: abstract isomorphism but no compatible complete map | Explicit countable atom sets and descending cofinite tails. |
| Theorem 8.5 | Exact mixing sheafification | Equality, local surjectivity, and universal gluing property proved. General method credited to earlier Boolean-valued/sheaf theory. |
| Corollary 8.6 | Binary associated sheaf equals the relative completion | Split every binary label into its two value events. |
| Corollary 8.7 | Product of ultrapowers at atomic stages | Dense atom cover; local value at an allowed ultrafilter equals its ultrapower. |
| Theorem 9.1 | Finitary transfer and attained existential value | Formula induction, finite partition refinements, pointwise witnesses using choice. |
| Theorem 9.2 | Sharp infinitary separation at arity p | Fixed old predicates, complete meet semantics, and the p-witness. |
| Corollary 9.3 | Stable range preserves the complete mixing model | Transport coefficients under the marked complete isomorphism. |
| Theorem 10.1 | Regular global rings and idempotent algebra | Piecewise generalized inverse; Boolean splitting of field idempotents. |
| Corollary 10.2 | No full product of fields in the atomless range | Such a product has primitive idempotents; the constructed ring has none. |
| Proposition 11.2 | General Boolean-algebra lower-bound threshold | Same argument with a centered-family lower-bound invariant. |
| Proposition 11.3 | Sufficient exact order-density criterion between arbitrary stages | Dense compatible inclusion; no converse for arbitrary abstract isomorphisms asserted. |

Numbering should be read from article.tex if the document is edited; this ledger describes the delivered version.

## Most important adversarial tests

### 1. Strict versus non-strict bounds

The site allows **fewer than** kappa generators. A p-sized witness is not admitted merely by setting kappa = p. Therefore the stable interval includes kappa = p, and the first change is at p^+. Similarly the first allowed minimal-character ultrafilter appears at u^+.

### 2. Ordinary base character versus generation modulo the cofinite filter

Fr has modulo-finite generating character zero. The usual inclusion-base character would incorrectly eliminate the finite-generation endpoint. The two notions agree on free ultrafilters, since no free ultrafilter is countably generated and adding finite deletions does not enlarge an uncountable base cardinal.

### 3. Topological refinement does not imply a complete comparison map

The identity on the underlying set is continuous from the finer topology to the coarser one. It does not follow that it induces a complete homomorphism between their regular-open Boolean algebras. The displayed p-sized meet gives a direct obstruction. The toy model shows that even abstractly isomorphic completions need not admit a complete map fixing the original algebra.

### 4. Meet calculations

In RO(X), the meet of a family of regular opens is the **interior of their intersection**, not simply their set intersection. For the p-witness, the original intersection is nonempty but has empty original interior; in the refined topology it is clopen and nonempty. This is the exact zero-to-positive change.

For a countably generated filter, its closed ultrafilter-extension set may fail to be originally clopen while having dense original interior. Its old-completion representative is that interior. The repository's row–tail set is not assumed nowhere dense.

### 5. Nonempty atom set does not prove density

Existence of an ultrafilter of character below kappa proves only that C_kappa has an atom. Atomicity requires every K_F to contain such an ultrafilter. Original Stone density, which follows by transporting a small ultrafilter onto an arbitrary infinite subset, is weaker than density in the refined topology.

### 6. Geometric points are completely prime

The point-free conclusion concerns the Boolean localic topos. The original set of ultrafilters remains nonempty. The proof uses maps preserving arbitrary joins, and does not misidentify ordinary Boolean ultrafilters with such maps.

### 7. The imported model is explicit

The ZFC threshold theorems do not depend on Millán. Only the early-atomicity example invokes his model properties. The counts of small-character ultrafilters and the resulting completions are derived here; the forcing construction is not.

### 8. No hidden complete distributivity

Mixture proofs only distribute a **finite** meet over arbitrary joins. Simultaneous refinements are formed for finitely many arguments of a finitary formula. No interchange of two unrestricted infinitary operations is used.

### 9. First-order transfer versus infinitary conjunction

A single existential formula has a chosen pointwise witness, giving fullness. This does not imply saturation. The p-fold conjunction is intentionally outside the finitary theorem, and its Boolean interpretation is not required to coincide with its pointwise infinitary truth event.

### 10. Internal fields versus global rings

Global polynomial identities are valid. Field disjunctions have Boolean truth value 1 without forcing either disjunct to hold globally. Consequently the global ring has many idempotents and is not a field. The no-product conclusion excludes **full** products, not subdirect-product representations.

### 11. Set-sized constructions

The index set, language, structure, Boolean algebra, set of filters, and collection of antichain-labelled sequence mixtures are all sets. No proper-class product or unbounded class of names is used.

### 12. Empty support and nonempty structures

Mix(0) has one element, the empty mixture. Structures M are assumed nonempty throughout the model-theoretic construction; this supplies a default for non-witnessing coordinates. Products in the ring argument exclude the zero ring, and the zero ring is separately ruled out by distinct constant sections 0 and 1.

## Computational scope

The verification script uses finite Boolean algebras P(n), not free filters on a finite set. Its tests cover the filter/Stone dictionary, frame points, mixing equality, pointwise witness attainment, regular inverses, and Boolean idempotent operations. It cannot establish the p or u threshold, any uncountable ultrafilter character, or a consistency result.

No Lean, Rocq, or other proof-assistant code was executed for the infinite theorems. No claim of kernel verification is made.
