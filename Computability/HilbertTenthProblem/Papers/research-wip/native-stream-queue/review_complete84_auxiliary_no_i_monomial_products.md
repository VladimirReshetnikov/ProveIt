# Independent review of the no-i-monomial-product condition

**PASS; no change requested.** The strengthened necessary condition follows from the inherited frontier and joint V,W product bound. It does not exclude the remaining nonmonomial direct-Q constructions or establish ten-gate optimality.

Reviewed companion: [complete84_auxiliary_no_i_monomial_products.md](complete84_auxiliary_no_i_monomial_products.md), SHA-256 `4d98a15d3eb9ec8beb989149d0b93d5f44fd3094fe31994b8c850891ff0dae59`.

I read the complete companion and used the already read proper-pivot, nine-gate frontier and mixed-cut proofs as explicit inherited premises. Their pins, and the proper-pivot helper/receipt pins, were freshly authenticated against all five entries in the companion. No predecessor program was imported or executed. This is a proof review; no numerical test is needed or claimed.

The scalar-span argument is valid in the stated rational polynomial ring. Before the direct-Q addition, Q is a fixed rational linear combination of the original paid ports and earlier multiplication outputs. Since Q is outside the paid span, some multiplication coefficient is nonzero. Specialization at i=0 preserves those scalar coefficients.

If a nonzero i-containing monomial multiplication occurs later than the direct-Q addition, it vanishes under specialization and is absent from the earlier relation. Deleting that product and then the relation's latest nonzero product coefficient removes two distinct multiplications chronologically.

For an earlier multiplication output g not proportional to Q, monomial independence gives `Q ∉ P0+span_ℚ{g}`. This uses precisely the declared paid monomials; it grants no extra power of c or other computed value. Thus Q's relation has a nonzero coefficient on a product other than g. Delete g first by its zero specialization and choose the largest remaining nonzero coefficient. If its index is earlier than g, removing g also removes the only potentially later term in the relation. If its index is later than g, intervening computations already have g replaced by zero. In either order the second product is expressible through strictly earlier surviving products and specialized original ports. Dependencies between the two products cause no cycle or unpaid multiplication.

An earlier g proportional to Q is correctly handled separately. Its scalar alias is already available before the addition U=Q, so redirecting U's uses and removing that addition gives at most five multiplications and three additions in the same scalar-free relaxation. This contradicts the inherited three-addition bound. Proportional monomials are not incorrectly treated as linearly independent.

Every remaining case therefore leaves a circuit for V and W=S|i=0 with at most three nonconstant multiplications, contradicting the inherited four-product bound. The whole original computation remains charged except for the two explicitly deleted products. The argument uses only fixed rational divisions and free linear combinations inside a multiplication-count contradiction. Specialization is an all-value polynomial proof device, not a purported positive compiler tuple.

The optional extension is also sound: a later multiplication merely needs to vanish at i=0; an earlier vanishing multiplication additionally needs the stated scalar-span exclusion. The note does not infer that condition for arbitrary nonmonomial products.

The conclusion is restricted to counted products of two nonconstant expressions in the independent-port model with paid c² and Delta*c². Scalar multiplications, arbitrary changed interfaces and compiler-only relations are outside the asserted obstruction. Nonmonomial i-dependent multiplication outputs remain unresolved. No new source, bound reduction or global nine-gate impossibility is claimed, and no repository or frozen author file was changed.
