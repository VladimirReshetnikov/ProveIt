# Physical role merging by differentiation

Elementary proof simplification verified on October 1, 2026. This does not change the already delivered role-cover archive or any frozen proof hash.

For a polynomial multiaffine in a,b, write

    f(a,b,w)=ab A(w)+a B(w)+b C(w)+D(w).

The physical merge operator ab↦z, a↦1, b↦1, 1↦0 satisfies the exact identity

    Merge(f)(z,w) = [d/dt f(t,t,w)]_(t=z/2).

Indeed, f(t,t,w)=t²A+t(B+C)+D, whose derivative at z/2 is zA+B+C. Thus this merge preserves real stability, up to the possible zero polynomial, by three standard closure operations: diagonalization, differentiation and positive scaling. In the support-polynomial application, the empty-support monomial retains coefficient1, so the merged polynomial is nonzero.

This gives an elementary replacement for the algebraic-symbol argument for each physical merge. It applies equally to exterior/exterior, core/exterior and core/core role pairs. The remaining variables are untouched and the new variable z is fresh. It does not remove the finite-degree stability-preserver theorem from the separate auxiliary rank-two coupling proof or from other uses in the article.

Reference for the three closure properties: D. G. Wagner, *Multivariate stable polynomials: theory and applications*, Lemma2.4(b),(c),(f), https://www.math.uwaterloo.ca/~dgwagner/ceb_wagner.pdf .

Use this optional simplification in the unified article or a later revision; the delivered role-cover package is already correct and remains frozen.
