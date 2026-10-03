# A one-tail role cover with a half-plane-property side matroid

Status: proposed ordinary theorem and exact application data, awaiting independent approval. No target in the role ledger is promoted on the strength of this note yet.

## 1. General criterion

Let D be a finite loopless directed relation. Suppose there are a physical vertex p and a set Q of physical vertices such that every arc i->j satisfies i=p or j in Q. Physical overlap p in Q is allowed. Give vertices arbitrary positive independent tail/head activities u_i,v_i.

Construct a transversal matroid M of rank r=|Q| as follows. Its r matching centers are the head copies indexed by Q. Its ground elements are every physical tail copy i, with neighborhood N(i) intersect Q, and r new private dummy elements d_j, one for each j in Q, with neighborhood {j}. Thus its rank is exactly r. Let F_M be its basis polynomial, with one monomial for each feasible ground-element basis, not one monomial per witnessing matching.

**Criterion.** If F_M is real stable (M has the half-plane property), then the signed physical monomer polynomial of D is real stable under the specified role activities. Consequently its support polynomial has only negative real zeros and is rank-ULC at its actual surviving degree. The conclusion extends to nonnegative activities by continuity. Transitivity is not required.

## 2. Stable bipartite base

Split every physical vertex into a tail copy and a head copy. First keep only arcs from all tail copies into the head copies Q. Denote this bipartite relation by B. Give tail-copy monomer variables a_i and covered-head monomer variables b_j. Its signed monomer polynomial is exactly

 mu_B(a,b) = (product_i a_i)(product_(j in Q) v_j)
             F_M(d_j=b_j/v_j, t_i=-u_i/a_i).

To check this identity, a basis chooses selected tail copies S and dummy elements for the unused covered heads Q-T. Its term after the substitution and multiplication is

 (-1)^|S| u_S v_T product_(i notin S) a_i product_(j in Q-T) b_j,

and the basis condition is precisely support feasibility from S to T. The selected sets are counted once, irrespective of witnesses. Empty-neighborhood tail columns are matroid loops and simply contribute their unused-tail monomer factors.

For all monomer variables in the open upper half-plane, each b_j/v_j and -u_i/a_i also lies there. The prefactors do not vanish. Since F_M is stable, mu_B is stable. Multiaffinity of F_M cancels every denominator, so this is a polynomial identity.

## 3. Add the uncovered head copies as pendants

Every head copy x outside Q has incoming neighbors contained in the single tail copy p. If its incoming set is empty, multiply the polynomial by its monomer b_x. Otherwise the exact support recurrence is

 mu_new = b_x mu_old - u_p v_x partial_(a_p) mu_old.

A support using x must use p->x, so deleting those forced endpoints gives the derivative term. No matching multiplicity is introduced. Write mu_old=a_p A+B, using multiaffinity in a_p. For c=u_p v_x>=0,

 b_x mu_old-c partial_(a_p)mu_old
   = b_x[(a_p-c/b_x)A+B].

If b_x is in the upper half-plane, -c/b_x has nonnegative imaginary part. Thus a_p-c/b_x stays in the upper half-plane and the displayed polynomial is nonzero. This proves stability directly, without needing an operator-classification theorem for this step. Sequential pendant additions cannot reuse p, since the polynomial remains multiaffine in a_p and a term using p has no a_p factor.

This constructs the signed monomer polynomial of the fully role-split relation.

## 4. Merge the physical copies

For each physical vertex, apply the already-approved physical-copy merge

 a_i b_i -> z_i,   a_i -> 1,   b_i -> 1,   1 -> 0.

Equivalently, T_i f is (partial_(a_i)+partial_(b_i))f evaluated at a_i=b_i=z_i/2. The nonnegative directional derivative preserves stability or gives zero: introduce t by f(a_i+t,b_i+t), differentiate in t, and specialize t=0. Diagonalization at z_i/2 then preserves stability. Its finite-degree symbol is also the stable polynomial z_i+r_i+s_i; this is the same merge used in the approved two-by-two role-cover theorem. It keeps an unused physical vertex as a monomer, keeps exactly one used role, and removes simultaneous occupancy of both roles. Every surviving split support corresponds to exactly one physically disjoint ordered support of D. Hence the resulting polynomial is precisely the physical signed monomer polynomial, and is stable.

The empty-support monomial product_i z_i has coefficient one, so none of the stability-preserving operations has zero-polynomial output. This also prevents a zero limit when some activities are taken to zero. Diagonalization gives mu(t,...,t)=t^n Gamma(-t^-2), proving negative real-rootedness and surviving-degree rank-ULC.

The order-dual form, one covered head and an arbitrary set of covered tails, follows by reversing every arc and exchanging u and v.

## 5. Simplification of the side matroid

The private dummies form an independent basis. A tail element with empty neighborhood is a loop. A tail element with singleton neighborhood {j} is parallel to d_j. These are the only parallel classes: two nonempty columns are dependent as a pair exactly when their neighbor union has size one. In particular, repeated two- or three-neighbor columns MUST NOT be identified.

The simplification therefore has r private representatives plus one distinct element for every tail whose neighborhood in Q has cardinality at least two. HPP of this simplification implies HPP of M: replace each private representative's variable by the sum of all variables in its parallel class, and omit loop variables. A sum of upper-half-plane variables is again in that half-plane.

## 6. Published small-matroid input

Primary source: Mario Kummer and Büşra Sert, *Matroids on Eight Elements with the Half-plane Property and Related Concepts*, arXiv:2111.09610v4, especially the introduction and Section 5, Theorem 5.2 (printed page 12).
https://arxiv.org/pdf/2111.09610

The complete classification states that the exceptions on at most seven elements are F7, F7-minus, F7-minus-minus, F7-minus-3, M(K4)+e and their duals. The five displayed exceptions have rank three; their duals have rank four. Every new eight-element excluded minor is rank-four sparse paving. Consequently an eight-element matroid whose one-element deletions and contractions all have HPP is itself HPP if its rank is not four, or if it is not sparse paving.

The rank-three exceptions have at least four nontrivial three-point lines; a simple rank-three transversal matroid with three private dummies has at most three nontrivial lines, one for each two-center subset. Thus rank-three side simplifications on at most seven elements automatically have HPP. Do NOT extend that automatic statement to arbitrary-rank transversal matroids: the dual of F7-minus-3 is a rank-four transversal counterexample. For higher-rank applications below, the exact exception/minor tests are performed explicitly.

The older classification and exact primary details are also discussed in Wagner--Wei, *A criterion for the half-plane property*, arXiv:0709.1269, and Choe--Oxley--Sokal--Wagner, *Homogeneous multivariate polynomials with the half-plane property*, Appendix A.2. No literature-wide novelty claim is made for this criterion or its applications.

## 7. Exact seven-vertex applications

The three initially identified cases are:

- 934: reverse the relation; p=1, Q={4,5,6}; tail-neighbor masks [5,7,6,7,4,4,0]. Simplified masks [1,2,4,5,7,6,7], rank three on seven elements, with two dependent triples.
- 937: reverse; p=1, Q={4,5,6}; masks [7,7,6,7,4,4,0]. Simplification [1,2,4,7,7,6,7], rank three on seven elements, with one dependent triple.
- 1008: no reversal; p=6, Q={0,1,2}; masks [0,0,2,3,6,7,7]. Simplification [1,2,4,3,6,7,7], rank three on seven elements, with two dependent triples.

The general criterion also allows |Q|>3. The exact local screen in screen_one_tail_hpp.py and nontotal7_one_tail_hpp_screen.json finds candidates for 27 of the current 41 unproved sources, including several rank-four seven-element side matroids and non-sparse-paving eight-element side matroids with HPP minors.

For every record, the script stores the working directed relation, duality flag, p, Q, every tail-neighbor mask, every retained simplified column, and the complete side-matroid basis set. It generates the five seven-element exception classes from the Fano plane and its zero-to-three circuit-hyperplane relaxations (including the concurrent-three relaxation M(K4)+e). Classification is by exact isomorphism, with explicit dualization at rank four. Eight-element cases require all deletions/contractions to pass that seven-element test and then use only the published rank/non-sparse-paving sufficient condition. No uncertain eight-element sparse-paving case is declared HPP.

These applications remain proposed until the theorem, published classification boundary, finite basis/minor tests, and physical support identities are independently audited. The frozen vertex theorem packages are unchanged.
