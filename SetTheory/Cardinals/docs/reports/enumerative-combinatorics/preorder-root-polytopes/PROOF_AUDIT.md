# Independent-review checklist

The main route is Sections 1–5 of the article. Section 6 is a second geometric
route. Appendix A reconstructs a known input via hypertrees. None of these
arguments assumes the desired palindromicity or unimodality.

## 1. Orientation and draconian vectors

The neighborhood of left i is the principal IDEAL {j : j <=_tau i}.
Transitivity makes the union of such neighborhoods an ideal. This proves
that the graph's draconian vectors are precisely the original preorder
lattice points. Reversing this orientation without transposing coordinates
would silently substitute the dual problem.

## 2. The complete real inequality system

At equal nonnegative margin totals m, membership in B_tau is equivalent to
u(I)-v(I) <= v_0 for every ideal I, together with coordinate nonnegativity.
Use weighted Hall for ALL left subsets, then enlarge a subset to its ideal
closure. This proves completeness; no assumption that every displayed
inequality defines a facet is required.

## 3. The inverse fibers

For y=(u_i-v_i) on indices 1,...,n, set p=sum(y_i^+), q=sum(y_i^-),
a=max_I y(I), and g=q+a. The base margins are

    u_min = (a+q-p, y^+),   v_min = (a, y^-).

They lie in g B_tau. The inverse fiber coordinates are

    w_0 = v_0-a,   w_i = min(u_i,v_i), i>0.

Membership makes these nonnegative; their sum is m-g. Conversely, every
such w gives a valid margin pair. For integral y all these quantities are
integral. The actual integer fibers, not dimension counting, justify the
Ehrhart-series factorization.

## 4. The two lattices

B_tau has dimension 2n in the full affine lattice sum(u)=sum(v)=1.
C_tau has dimension n in Z^n. The fiber factor (1-t)^(-n) cancels the
DIFFERENCE of the two Ehrhart denominator exponents. Normalized volumes
agree, not unnormalized Euclidean volumes in different dimensions.

## 5. Root unimodularity and genuine polytopality

Any n linearly independent roots e_i-e_j, with e_0=0, give a spanning tree
on n+1 vertices. Deleting the 0-row of its incidence matrix has determinant
+/-1. Apply this to cones from 0 over boundary simplices. Polytopality of a
pulling boundary comes from Athanasiadis's Lemma 2.1, not from an invalid
claim that every sphere or every shellable complex is polytopal.

## 6. Independent special-simplex route

Each defining facet of B_tau omits exactly one diagonal root d_i=e_i+f_i.
Their convex hull is a special n-simplex. Bipartite root triangulations are
unimodular in the full lattice. Athanasiadis's special-simplex theorem then
gives dimension 2n-(n+1)+1=n. The interior translation by the all-one vector
has index n+1 and supplies a separate reciprocity check.

## 7. Computational independence and limits

Small cases compare: direct ideal enumeration; actual spanning trees and
activity transfers; sums of root vertices; all-subset and ideal Hall tests;
polar inequalities and the ideal gauge; inverse fibers; interior translation.
The tests do not use floating-point arithmetic. They do not by themselves
certify an all-n theorem or produce a formal proof. The numerical tests of
palindromicity alone are not novel size records.
