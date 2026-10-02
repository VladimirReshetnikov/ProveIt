# The final seven-vertex role-weighted case: an exact half-plane-property proof

Status: exact local proof candidate, submitted for independent audit. This note does not itself promote the finite ledger.

## 1. Directed relation and side matroid

The catalog's target 1565 has off-diagonal row masks

    [0, 1, 3, 7, 39, 23, 63].

Take the covered tail p=6 and covered heads Q={0,1,2,4,5}, in the listed order. Every arc has tail p or head in Q. The side transversal matroid in ONE_TAIL_HPP_ROLE_COVER.md has five private dummy elements and all seven original tail elements. Removing loops and identifying only genuine singleton-neighborhood parallel classes gives the rank-five matroid M on ten elements with neighbor masks

    [1, 2, 4, 8, 16, 3, 7, 23, 15, 31].

Elements are indexed from 0 to 9 in precisely this order. Its 198 bases are stored explicitly in side1565_rayleigh_0_9_certificate.json and are independently reconstructible by checking a bijection from each five-element set to the five centers. Multi-neighbor columns are not merged.

## 2. Proper minors

Every one-element deletion and contraction of M has the half-plane property. The exact basis sets, loop/coloop/parallel/series reductions and published-list isomorphisms are recorded in side1565_proper_minor_screen.json.

Eight reduced minors use the independently approved small-matroid criterion of Kummer--Sert, Section 5, Theorem 5.2: all relevant seven-element exceptional minors are excluded and the remaining eight-element cases have rank different from four or are not sparse paving. The other twelve minors match certified-positive entries of the published nine-element half-plane-property list, with duality where appropriate. The one-based list lines used are 1536, 1751, 2020, 2385 and 3368.

The official data are https://zenodo.org/records/6108027/files/n9r4Hpp.txt?download=1. Its SHA256 is a3c7a6eaebe02ef50998710282542be2751b218a6713853cdd2eecadbe1f1f86 and its published MD5 is c73d80267112a960df5485f159ab56e0. Only the certified-positive list is used. This is an application of the published certified list, not a local replay of the authors' original Gram certificates. The separate proper-minor audit checks all basis sets, reduction operations and explicit list isomorphisms.

## 3. A rational Gram identity valid on all of R^8

Let F be M's basis-generating polynomial. Write F_ab for the coefficient of x_0^a x_9^b, with a,b in {0,1}. The Rayleigh difference is

    Delta_09 F = F_10 F_01 - F_00 F_11.

It is independent of x_0 and x_9. In the remaining ground-element order [1,2,3,4,5,6,7,8], it is a homogeneous degree-eight polynomial q with 397 nonzero monomials. Let B be the sorted set of the 37 squarefree degree-four exponent vectors a such that q has a nonzero coefficient at 2a. For each exponent e, put

    N_e = number of ordered pairs (a,b) in B x B with a+b=e.

Define the 37 by 37 rational symmetric matrix

    G_ab = coefficient(q, a+b) / N_(a+b).

This is a completely exact definition from the 198 bases; a missing coefficient means zero. By construction, if h_a=x^a, then q=h^T G h. The only entries of G are

    0, 1/8, 1/6, 1/4, 1/3, 1/2, 1.

The supplied certificate proves G is positive semidefinite of rank 32. Specifically, exact rational Schur elimination gives 32 strictly positive pivots and a zero residual matrix. The certificate stores the resulting positive rational weights w_l and rational vectors c_l, and the checker verifies both

    G = sum_l w_l c_l c_l^T,       w_l > 0,
    q = sum_l w_l (sum_a c_la x^a)^2.

There is no remainder and no monomial prefactor of uncontrolled sign. Thus Delta_09 F is nonnegative for every real assignment of its eight variables, not merely on the positive orthant. Its certificate SHA256 is 57f737171c2df6876c93c3760015997b7e56b64517be6fd8dbe221200bc2b287.

The discovery used floating-point projection, but the proof and portable replay use only the explicitly supplied rational matrix/squares. No numerical solver output, tolerance, or positive-orthant certificate is used as evidence of nonnegativity.

## 4. Apply Wagner--Wei and merge physical roles

Wagner--Wei, *A criterion for the half-plane property*, Theorem 3(c), states that a multiaffine polynomial with positive coefficients is stable if all its one-variable deletions and contractions are strongly Rayleigh and one Rayleigh difference is nonnegative for all real values of the remaining variables. For homogeneous matroid basis polynomials, HPP, real stability and the strong Rayleigh property agree. The theorem's two hypotheses are supplied by Sections 2 and 3. Hence F is real stable.

Primary source: https://arxiv.org/pdf/0709.1269, Theorem 3, printed page 3.

Restore the side matroid's parallel classes by sums of variables; loops are irrelevant. Then apply the independently approved one-tail HPP criterion: substitute the side basis polynomial into the bipartite signed monomer formula, add uncovered heads as pendants using b_x f-u_p v_x partial_(a_p)f, and merge each physical tail/head pair via

    (partial_(a_i)+partial_(b_i))f at a_i=b_i=z_i/2.

This proves real stability of the physical signed monomer polynomial and negative real-rootedness of the support gamma polynomial for arbitrary positive independent tail/head activities on target 1565. Nonnegative activities follow by continuity; the empty-support term prevents a zero-polynomial limit. Newton's inequalities use the actual surviving degree.

The existing approved extremal-block refinement then transfers role-weighted ULC to source 1611. Its effective activities may be zero, which is allowed by the just-proved boundary conclusion. These two promotions, together with the already audited ledger, would complete the seven-vertex independent-role domain. Global degree-three assembly is a separate dependency check.
