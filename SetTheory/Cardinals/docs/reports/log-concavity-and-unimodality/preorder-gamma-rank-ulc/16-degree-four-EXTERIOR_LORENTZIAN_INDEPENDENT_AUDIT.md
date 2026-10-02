# Independent audit of the exterior-only Lorentzian lemma

## Verdict

APPROVED. For the graph P→I→Q with no other arcs, where the core sets and the physical exterior set are pairwise disjoint, the homogeneous polynomial H(z,t)=Σ F_k z^(r−k)t^k is Lorentzian at order r=|P|+|Q|. Independent nonnegative exterior head/tail activities are permitted.

This is an order-r result. The audit does not infer actual-degree normalization by dividing out a power of z, does not claim real-rootedness in general, and does not extend the conclusion automatically to the original polynomial with core arcs restored.

## 1. Dummy-basis coefficients

The P-side transversal matroid has one private dummy d_p adjacent only to each slot p. All dummies form a basis, so its rank is exactly |P| even when some physical exterior elements are loops. A basis with physical set R and dummy set {d_p:p∉P′} has size |P| exactly when |R|=|P′|. Since its dummies force their own slots, it exists exactly when R matches into P′.

Thus each pair (R,P′) is represented by one ground-set basis, independent of how many bijections realize the matching. The same argument applies to the Q-side. The ordinary basis-generating coefficients are one; there is no permanent or factorial multiplicity. Although the general exponential support formula contains α! denominators, every basis exponent here is zero or one, so all such denominators equal one.

## 2. Product, truncation, and specialization

The two basis polynomials use distinct dummy variables and shared physical variables x_i. Their product is homogeneous of degree r and Lorentzian. A repeated physical variable is precisely an exterior vertex used in both roles. Coordinate upper truncation at exponent one deletes precisely those collisions without changing a surviving coefficient.

A surviving pair of bases specifies the ordered support A=P′∪L, B=Q′∪R uniquely. Different role allocations to the same physical union are different ordered supports and correctly contribute separately after variables are identified. The two exterior matchings are independent once L∩R=∅. Hence setting all dummy variables to z and all physical variables to t gives exactly the claimed coefficients F_k.

The all-dummy monomial survives, so the polynomial is nonzero even at zero role activities. Its degree remains r throughout. Nonnegative head and tail activities are simply separate diagonal substitutions in the two factors before multiplication and truncation; they attach exactly the product of the chosen role weights to each support. Core activities and per-edge weights are not added to the claim.

## 3. Primary-source hypotheses checked directly

Brändén--Huh, *Lorentzian polynomials*, Theorem 3.10 identifies the exponential generating polynomial of an M-convex support as Lorentzian, including matroid bases. Theorem 2.10 allows nonnegative linear substitutions, including zero activities. The squarefree observation above gives the ordinary basis polynomial here: https://annals.math.princeton.edu/wp-content/uploads/annals-v192-n3-p04-s.pdf .

Ross--Süss--Wannerer, *Dually Lorentzian Polynomials*, Theorem 3.1 states product and nonnegative-substitution closure for Lorentzian polynomials. Proposition 3.3, with Definition 3.2, really asserts coefficient-preserving coordinate upper truncation of ordinary Lorentzian polynomials, not only a dually Lorentzian variant: https://link.springer.com/article/10.1007/s00605-025-02134-6 . These exact hypotheses match the construction.

## 4. Correct degree-four normalization

For r=4 the relevant quadratic derivatives are

∂t²H=2F₂ z²+6F₃ zt+12F₄ t²,
∂z∂tH=3F₁ z²+4F₂ zt+3F₃ t²,
∂z²H=12F₀ z²+6F₁ zt+2F₂ t².

Their Hessians have at most one positive eigenvalue. With nonnegative coefficients this gives their nonnegative discriminants and exactly the constants 3F₃²≥8F₂F₄, 4F₂²≥9F₁F₃, and 3F₁²≥8F₀F₂. No normalization parameter is silently reduced.

## 5. Core corrections remain separate

For a four-core graph, every matching edge touches a core vertex. A four-edge matching must therefore have four core--exterior edges and no core edge, so Γ₄=F₄. A three-edge matching with a core edge has exactly four core and two exterior vertices, explaining Γ₃=F₃+C. A two-edge matching with a core edge has zero or one exterior vertex, explaining Γ₂=F₂+B. Categories cannot overlap because the number of selected exterior vertices is fixed by a support.

The displayed correction identity follows algebraically. The Lorentzian lemma proves only its exterior-only first summand nonnegative; the remaining correction requires its own proof. This boundary is mathematically necessary and is preserved in the approved statement.
