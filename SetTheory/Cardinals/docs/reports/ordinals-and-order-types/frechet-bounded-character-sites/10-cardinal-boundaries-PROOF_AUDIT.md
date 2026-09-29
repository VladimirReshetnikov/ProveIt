# Proof audit and scope ledger

This is a public mathematical dependency ledger, not a proof-assistant certificate or independent referee report. The full arguments are in the article.

## Central comparison theorem (Theorem 4.3)

**Forward direction below p.** A filter base of size less than p has an infinite pseudointersection. Its principal-modulo-finite extension is a condition in the site. Hence the distinguished copy of P(omega)/Fin is order dense and has the usual unique complete extension.

**Failure C -> D_kappa at or above p.** A filter F without a pseudointersection gives a dense family E_F of old events incompatible with F. Its join in C is 1; the join of its images misses the nonzero cone above F. A unital complete map respecting old events cannot preserve that join.

**Failure D_kappa -> C at or above p.** Filters without pseudointersections are dense: either a condition already is one, or a p-witness is transported into a pseudointersection of the condition. Every such cone must map to zero, since a nonzero lower bound for all of its old membership events would give a pseudointersection. Completeness would therefore send 1 to 0.

**Scope.** Both maps are required to be unital and to preserve the distinguished old events. No intermediate abstract nonisomorphism follows from this theorem alone. Corollary 6.3 proves abstract nonisomorphism when kappa >= h by partition distributivity.

## Closure and distributivity (Theorem 5.1)

The union of an increasing chain of filters of length less than kappa^+ is proper, and the union of their bases has size at most kappa. This works for singular as well as regular infinite kappa. Successive antichain decisions and union lower bounds give a common refining antichain for at most kappa partitions.

## Atoms and points (Theorem 7.3)

A non-ultrafilter condition splits by adjoining a set and its complement, both positively. An ultrafilter condition has a singleton cone. Cones are order dense, so these account for all atoms.

The proof that complete Boolean points are precisely atoms uses the join of the kernel of the point map. It does not identify ordinary Stone-space ultrafilters with complete locale points.

## Explicit sheaf (Theorem 9.2)

Raw equality at F is equivalent to Boolean equality on the cone above F. A Boolean mixture has a dense cover on which it is raw. Compatible sections glue after disjoint refinement and flattening. These properties give the full universal property, not merely an injective map into some sheaf.

For infinite value sets, the labels must be raw sequences rather than only constants. The identity sequence on omega is a concrete witness of this distinction.

## Transfer (Theorem 10.1)

Existential truth is witnessed coordinatewise on each presentation cell. The proof does not commute the old-event embedding with an arbitrary infinite join, which would be invalid above p.

## Saturation (Theorems 11.1–11.2)

1. Countable partition refinement gives simultaneous raw labels for all parameters locally.
2. On each cell, the finite-satisfiability truth sets E_m are decreasing.
3. At coordinate k, choose a witness for the first max({0} union {m <= k : k in E_m}) formulas.
4. The first n+1 satisfiability set, minus a finite initial segment, is contained in the truth set of formula n for this witness.
5. Mixing produces localized realization on any Boolean region d.
6. For an ordinary ultrafilter specialization, finite-part truth values e_m belong to the ultrafilter but need not equal 1.
7. Partition 1 into e_m minus e_(m+1), and the intersection of all e_m. Use finite witnesses on the former and localized countable realization on the latter.
8. The mixed witness has formula-n truth at least e_(n+1), and hence realizes the type in the quotient.

The language-countability qualification is essential for identifying the countable-type conclusion with full aleph_1 saturation. No higher saturation is asserted.

## Cardinalities (Theorem 12.4)

- The raw binary quotient has continuum many classes.
- A continuum-sized almost disjoint family yields 2^c distinct joins in C.
- Order density bounds every antichain in C by c, and hence bounds the number of mixed presentations by 2^c for |A| <= c.
- An explicit independent family proves that there are 2^c free ultrafilters.
- The full-site product then has size 2^(2^c).

These are cardinality statements, not a chain of complete embeddings.

## Artifact checks

The final source was compiled with pdfLaTeX until references stabilized. The final log contained no undefined references, overfull/underfull box diagnostics, or LaTeX warnings. All 26 pages were rendered and inspected through contact sheets, with additional full-page inspection of the main comparison theorem, the saturation theorem, and final layout changes.

No finite computational test, Lean build, or independent proof review is claimed.
