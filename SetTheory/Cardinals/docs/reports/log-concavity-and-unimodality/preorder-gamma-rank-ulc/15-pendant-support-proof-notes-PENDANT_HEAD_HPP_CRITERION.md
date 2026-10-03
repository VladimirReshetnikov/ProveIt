# Many-tail pendant-head extensions of a stable transversal seed

Research note, October 1, 2026. This is a direct extension of the independently approved one-tail criterion in the same research project. It handles a genuine internal-core subfamily of two-tail/three-head covers, but is not the general five-role-cover theorem.

## Conditional theorem

Let D be a finite loopless directed relation on physical vertex set V. Fix Q subset V. Suppose every vertex j outside Q has at most one incoming neighbor in D. Form a transversal matroid M_Q as follows:

- Its matching positions are the head copies q−, q in Q.
- Its ground set contains every tail copy i+, i in V, and a private dummy d_q for each q in Q.
- Tail i+ is adjacent to positions N_D^+(i) intersect Q.
- Dummy d_q is adjacent only to position q−.

The rank is exactly |Q| because all dummies form a basis. Assume the ordinary squarefree basis-generating polynomial B_M is real stable (the half-plane property).

Then, for arbitrary nonnegative independent tail and head activities u_i,v_i, the signed physical monomer polynomial

    mu_D(z) = sum_(S,T feasible) (-1)^|S| u^S v^T
                  product_(i notin S union T) z_i

is real stable. Here feasible supports are ordered disjoint equal-cardinality pairs admitting a directed perfect matching, each counted once.

Consequently Gamma_D(t)=sum gamma_k t^k has only negative real zeros and is rank-ultra-log-concave at its actual surviving degree. The constant-polynomial case has no zeros. No transitivity, bound on |Q|, bound on the number of distinct tail hubs, or restriction on physical overlap is imposed.

In role-cover terminology, if P+ union Q− covers all arcs, it is enough that every head copy outside Q has degree at most one. Such heads are pendant at their own tail hubs, which need not all be the same vertex. Arbitrary arcs between the selected tail and head roles are permitted, as long as the Q-side matroid satisfies the stated HPP condition.

## Proof

### The Q-head seed

Temporarily split every physical vertex into an independent tail and head copy. Begin with all tail copies and only the head copies indexed by Q. There are exactly the arcs i+→q− specified by D.

Write a_i for the tail-copy monomer variable and b_q for the Q-head-copy monomer variable. For positive activities, the signed monomer polynomial of this split seed is

    mu_0(a,b)
       = [product_(i in V) a_i] [product_(q in Q) v_q]
          B_M( x_i=-u_i/a_i, d_q=b_q/v_q ).

A basis consists of selected tail copies S together with dummies Q\T; it exists exactly when S can be matched to T. Thus this identity counts each pair (S,T) once, not matching witnesses. Multiplication by the tail monomers cancels all denominators because B_M is multiaffine.

The substitutions −u_i/a_i and b_q/v_q lie in the upper half-plane when the monomer arguments do. The HPP assumption therefore makes mu_0 real stable. Isolated tail copies merely retain their monomer factors. The all-unused monomial has coefficient one, so the polynomial is nonzero.

### Insert every remaining head copy

Consider j outside Q. If j has no incoming neighbor, its head copy is isolated and contributes the stable factor b_j. Otherwise let i be its unique incoming neighbor. With w=u_i v_j, the new split monomer polynomial is

    mu_new = b_j mu_old − w partial_(a_i) mu_old.

Every support using the new head j− must use i+→j−, so deleting that pair leaves exactly a support in which i+ is unused. The derivative records this unused tail; there is no multiplicity or choice of witnessing edge at j−. The identity follows at support level.

Since mu_old is affine in a_i,

    mu_new = b_j mu_old(a_i − w/b_j),

with other arguments unchanged. For b_j in the upper half-plane and w≥0, the number −w/b_j has nonnegative imaginary part. Thus the shifted a_i remains strictly upper and the expression is nonzero. This proves stability after the insertion. Repeat for every j outside Q, at any sequence of tail hubs. Several heads may have the same hub.

### Recombine physical copies

Once all role copies are present, apply for each physical vertex i the ordinary monomer merge

    a_i b_i -> z_i,       a_i -> 1,       b_i -> 1,       1 -> 0.

It retains a single unused physical monomer if both copies are unused, removes the unused copy if exactly one role is used, and deletes terms using both roles. Its algebraic symbol is z_i+r_i+s_i, so it preserves real stability. Tensoring with untouched variables only adds stable factors.

An elementary verification needs no operator-classification theorem: for f=Aab+Ba+Cb+D, the desired image Az+B+C equals the derivative in t of f(t,t), evaluated at t=z/2. Diagonal identification, differentiation, and positive rescaling preserve stability or give zero. The all-unused monomial excludes zero output here.

The resulting polynomial is exactly mu_D, since role supports and ordered physical supports agree after prohibited double use is removed. Its all-unused term remains product_i z_i.

Nonnegative activities follow by coefficientwise limits from positive activities. The constant empty-support monomial prevents an identically zero limit, so stability is retained even if the matching degree drops.

Finally, if n=|V|,

    mu_D(s,...,s) = s^n Gamma_D(−s^(−2)).

Real stability of the left side gives real-rootedness on the real diagonal. Since Gamma_D has nonnegative coefficients and constant coefficient one, the standard root transfer implies that every zero of Gamma_D is strictly negative. Newton's inequalities apply at the actual surviving degree.

## An explicit all-rank HPP subfamily

Suppose |Q|=q≥2 and every nonempty tail neighborhood inside Q is either a singleton or all of Q. Let

    r_q = d_q + sum_(i: N_D^+(i) intersect Q = {q}) x_i

for each q in Q, and let g_1,...,g_m be the variables of the tails whose neighborhood is all of Q. Tails with empty neighborhood are loops and do not occur in a basis. Then

    B_M = e_q( (r_q)_(q in Q), g_1,...,g_m ).

Indeed, singleton-neighborhood elements with the same neighbor form a parallel class. A q-element subset is a basis exactly when it uses at most one element from each singleton class; all remaining universal elements can be assigned injectively to the remaining positions. This is the displayed elementary symmetric polynomial after parallel-class substitution.

Elementary symmetric polynomials are real stable, as follows by differentiating the stable product product_j(s+y_j) an appropriate number of times in s and then setting s=0. Nonnegative class-sum substitutions preserve stability. Therefore this explicit neighborhood condition supplies the HPP hypothesis of the conditional theorem for every q.

For q=1, every nonempty neighborhood is already a singleton and the basis polynomial is linear; for q=0, the seed is edgeless and the pendant insertion proof starts from the product of tail monomers.

In particular, for q=3 and two tail hubs, any number of private uncovered heads may be attached to either hub, and each tail's Q-neighborhood may be empty, singleton, or universal. The two hubs may have arbitrary such neighborhoods themselves, so many nonempty internal 2×3 core patterns are covered. All physical identifications are allowed if the original relation remains loopless. A universal Q-neighborhood is impossible for a physical tail already in Q because it would include a loop; this is automatically excluded by the hypothesis that D is loopless.

## Concrete overlapping, non-bipartite example

Let V={0,...,8}, P={0,1}, and Q={1,2,3}. Include the following arcs and no others:

- 0→1,2,3,7;
- 1→0,2,8;
- i→1,2,3 for i=4,5,6.

The physical graph contains the triangle 0,1,2, so the separate bipartite-orientation Lorentzian theorem does not apply. The selected role cover has overlap P intersect Q={1}. Every uncovered head has at most one incoming neighbor. Each Q-neighborhood is empty, singleton, or universal, so the explicit HPP criterion applies. With unit activities, exact support enumeration gives

    Gamma_D(t)=1+16t+47t^2+31t^3+4t^4.

The theorem proves real-rootedness for all independent nonnegative activities on this entire structural family. The companion standard-library checker additionally verifies the displayed example and 480 random weighted examples (160 at each overlap size 0,1,2), including 458 zero-activity cases, by exact rational Sturm counts on the negative real axis. It verifies actual-degree Newton inequalities in every test and reaches degree five. See `check_pendant_head_examples.py` and `pendant_verification.json`.

## Scope and sources

The single-tail version was already proved and independently approved in `../weighted-preorder-gamma/ONE_TAIL_HPP_ROLE_COVER.md`. The added observation is that its pendant insertion can be repeated at any number of different tail hubs. No new stability-preserver result is asserted.

The seed uses exactly the stated HPP assumption; arbitrary rank-three transversal matroids are not assumed stable. Their stability is false in general.

The stability facts and finite-degree algebraic-symbol convention are those used in the approved 2×2 role-cover proof. Primary sources include:

- Julius Borcea and Petter Brändén, *The Lee–Yang and Pólya–Schur programs. I. Linear operators preserving stability*, Inventiones Mathematicae 177 (2009), 541–569; https://arxiv.org/abs/0809.0401
- Petter Brändén and June Huh, *Lorentzian polynomials*, Lemma 3.3 for the same multiaffine merge, with a direct stable-symbol proof in its discussion; https://arxiv.org/pdf/1902.03719

The main argument above is ordinary mathematics. Supplemental finite checks do not replace the unbounded proof.
