# Primary literature notes for the unknot-recognition continuation

Checked 2026-10-09. These are research notes, not a claim that the repository has a quasipolynomial recognizer.

## Current-status sources

### Lackenby 2021 technical slides
- Oxford technical handout: https://people.maths.ox.ac.uk/lackenby/quasipolynomial-talk-oxford-compressed.pdf
- Full slides: https://people.maths.ox.ac.uk/lackenby/quasipolynomial-talk-oxford.pdf
- The technical announcement is 2^{O((log n)^3)} = n^{O((log n)^2)}. Its outline uses surfaces of genus-like complexity O(n^2), compressed hierarchy encodings, multisurfaces, and Cheeger regions/generalised Heegaard splittings to obtain effective hierarchy length O((log n)^2). Do not silently replace this with n^{O(log n)}.
- Oxford's news announcement https://www.maths.ox.ac.uk/node/38304 says n^{c log n}. Cite the technical slides when an exact exponent matters, and identify the discrepancy if discussing it.
- Author publication page, https://people.maths.ox.ac.uk/lackenby/, is updated through September 2026. It still lists the quasipolynomial result under 2021 talks, while listing a different July-2026 hierarchy preprint under papers. Absence from a webpage is not proof of nonexistence; write “the sources checked supply a talk-level announcement, not a complete proof of that bound.”

### Lackenby 2026 hierarchy preprint
- Marc Lackenby, Incompressible surfaces, hierarchies and unknot recognition, arXiv:2607.23350v1, 25 July 2026, 54 pages.
- https://arxiv.org/html/2607.23350v1; https://people.maths.ox.ac.uk/lackenby/algorithm-incompressible-250726.pdf.
- Theorem 1.1: incompressibility algorithm for compact orientable normal surface in compact orientable irreducible triangulated 3-manifold. Corollary 1.2: unknot algorithm. Theorem 1.6: essential boundary pattern is in NP and co-NP.
- Definition 5.8: q-complexity sum_H max(I(H),0)^2. Proposition 5.9: normal nonseparating cut cannot increase q-complexity; equality forces a relative homology class representable vertically in the interior parallelity bundle. Proposition 10.2: refined algorithm terminates and every partial hierarchy has length at most 4 c_q(H).
- Introduction explicitly defers possible speed-up to future work. This is not a quasipolynomial runtime theorem. Short hierarchy length does not itself bound repeated repairs or bit-size growth.

### Lackenby 2026 fixed-link Reidemeister preprint
- A polynomial upper bound on Reidemeister moves for each link type, arXiv:2602.09923v1, 10 February 2026, 136 pp.
- https://arxiv.org/abs/2602.09923.
- For fixed link type K, there is a polynomial p_K such that diagrams with c_1,c_2 crossings differ by at most p_K(c_1)+p_K(c_2) Reidemeister moves. This supplies NP certificates for each fixed link type, not a polynomial search method and not a uniform bound in variable K.

## Closest prior work for LP / support / propagation claims

### Burton–Ozlen practical recognizer
- Benjamin A. Burton and Melih Ozlen, A fast branching algorithm for unknot recognition with experimental polynomial-time behaviour, arXiv:1211.1079v3, 9 October 2014.
- https://arxiv.org/pdf/1211.1079.
- Lemma 7 already proves that support-minimal positive-Euler normal coordinates span an extreme ray, whose primitive integral generator is connected. Algorithm 9 obtains this by trying coordinate zeros, with O(7t) LP feasibility calls after an admissible witness is found. Lemma 8 uses a triangle zero to exclude the vertex link in a one-vertex triangulation.
- Theorem 12 isolates the exponential step: positive-Euler nonvertex normal surface search, O(3^t poly(t)); the remaining algorithmic steps are polynomial, and the outer crushing loop runs O(c) times.
- Their quad constraints are SOS1 constraints. Greedy support minimization, primitive ray normalization, and feasibility branching are established baselines. A new result should state the exact saving, e.g. oracle count, ambiguity parameter, certificate size, or restricted topological class.

### Burton–Ozlen normal-surface tree traversal
- A tree traversal algorithm for decision problems in knot theory and 3-manifold topology, arXiv:1010.6200.
- https://arxiv.org/pdf/1010.6200.
- Section 3.4 and Algorithms 3.15–3.16 already develop incremental dual-simplex feasibility: retain a basis, add zero constraints, shift x_j >= 1 into the right side, and warm-start child LPs from parents. Section 4 bounds arithmetic sizes (Theorem 4.4 and corollaries).
- Thus “warm-start dual simplex” by itself is not a new method. Polynomial LP existence and practical simplex runtime are distinct claims.

### Burton maximal admissible faces
- Benjamin A. Burton, Maximal admissible faces and asymptotic bounds for the normal surface solution space, J. Combin. Theory A 118 (2011), 1410–1435; arXiv:1004.2605.
- https://arxiv.org/pdf/1004.2605.
- Lemma 3.7: points in an admissible face are pairwise compatible. Lemma 3.9: a pairwise compatible admissible set lies in a maximal admissible face. Corollary 3.12 characterizes maximal admissible faces by maximal compatible sets; in projectivization, by convex hulls of maximal compatible vertex sets. Corollary 3.8 gives <=5t facets in standard coordinates, <=t in quadrilateral coordinates.
- Face support / forbidden quadrilateral formulations should cite this work. None of these facts bounds the number of relevant faces polynomially.

### Hardness near the normal constraints
- Benjamin A. Burton and Alexander He, On the hardness of finding normal surfaces, arXiv:1912.09051v3.
- https://arxiv.org/html/1912.09051v3.
- Theorem 8: abstract normal constraint optimisation is NP-complete. The abstraction retains matching-equation incidence bounds, nonnegativity, quadrilateral compatibility, a linear objective, and a designated triangle zero, but not all geometric restrictions of real triangulations.
- Theorem 12: splitting surfaces consisting only of one quadrilateral per tetrahedron can be found by three BFS propagation attempts, because a quadrilateral normal-arc pattern forces a neighbor's type.
- Theorem 18: connected spanning central-surface detection is NP-complete even in orientable 3-manifold triangulations.
- Do not infer NP-hardness of knot-exterior sphere/disc search, or QP impossibility, from these theorems. Their legitimate implication is that generic sparse constraint form alone is insufficient to justify a universal small-ambiguity theorem.

## Closest prior work for compressed extraction and boundary curves

### AHT
- Ian Agol, Joel Hass, William Thurston, The computational complexity of knot genus and spanning area, Trans. Amer. Math. Soc. 358 (2006), 3821–3850; arXiv:math/0205057v2.
- https://arxiv.org/pdf/math/0205057.
- Theorem 12: orbit count for k interval pairings on [1,N] in poly(k log N) time. Corollaries 13–14 apply to normal curves/surfaces with time poly(t log W). Theorem 16 adds vector-valued piecewise-constant weights, with polynomial dependence on input parameters and their logarithmic integer sizes.
- Crucial: Section 6 defines compressed output ([r_i,s_i],v_i), encoding s_i-r_i+1 orbits with common weight v_i. “List of orbits” is not an explicit N-entry output. Weighted coordinates already give component normal-coordinate vectors and multiplicities.
- Consequently basic log-weight component extraction is classical. New work must identify an improved special-purpose bound or a genuinely additional geometric datum.

### Schaefer–Sedgwick–Stefankovic
- Algorithms for Normal Curves and Surfaces, COCOON 2002.
- https://www.cs.rochester.edu/~stefanko/Publications/Cocoon%2702.pdf.
- Theorem 1(a): marked-component normal coordinates are computable in polynomial time; related clauses count components and list curve isotopy types/multiplicities. This is another prior baseline for a “extract one marked component” claim.

### Erickson–Nayyeri compressed curve tracing
- Tracing Compressed Curves in Triangulated Surfaces, SoCG 2012.
- https://jeffe.cs.illinois.edu/pubs/pdf/tracingx.pdf.
- Theorems 4.4–4.5 give O(t^2 log X) tracing for a connected / reduced normal curve. Theorem 5.1 counts isotopy classes and multiplicities within the same bound. The discussion after Theorem 5.1 explains reconstruction of one component's original normal coordinates in O(t^2 log X); reconstructing all has an extra topology factor.
- This is a 2D curve theorem, not automatically a 3D surface algorithm. The distinction between compressed tracing data and coordinates in the original triangulation matters.

### Lackenby fast curves paper
- Marc Lackenby, Some fast algorithms for curves in surfaces, Discrete & Computational Geometry (2026), DOI 10.1007/s00454-026-00845-7.
- Author manuscript: https://people.maths.ox.ac.uk/lackenby/AlgorithmsSurfaces13jan26.pdf.
- Journal: https://link.springer.com/article/10.1007/s00454-026-00845-7.
- Theorems 1.1–1.2 compute geometric intersection and isotopy of normal 1-manifolds in poly(|T|,log w_1,log w_2), with variable surface topology. Theorem 1.3 normalises a standard 1-manifold in poly(|T|,simp(C),log w(C)). Theorem 3.4 extracts component vectors with a similar simplification-number parameter.
- Uniform dependence on |T| is substantive; earlier “polynomial” results can hold topology fixed. For normalization, an argument that ignores simp(C) is incomplete, as it can be large despite small log weight. The procedure may remove inessential components, so it is not an unconditional isotopy preserving every component.

## Original implementation / proof recommendations

1. State a complete bit model. Let t be tetrahedra, m live constraints or arc types, B the largest integer bit length, and k the proposed ambiguity parameter. An arithmetic operation on B-bit rationals is not constant time. Verify all dynamically produced B stay controlled.
2. A fast presolver should return an exact zero certificate or a feasible rational witness. Keep the proof of feasibility separate from the heuristic that chooses the next quad.
3. Distinguish local quad compatibility, connectedness, boundary essentiality, and primitiveness. gcd=1 alone does not imply a normal surface is connected; the extreme-ray hypothesis is what powers Burton–Ozlen Lemma 7.
4. Distinguish preservation of a homology class from preservation of the boundary pattern / embedding. AHT is a component engine, not a black box for all topological data needed by a hierarchy.
5. Every parameterized QP corollary needs a theorem bounding the parameter on every input and after every reduction. Bounded k on test data is an empirical result only.
6. Stop complexity accounting at a bounded budget with UNKNOWN if a required bound is not proved; only checked positive/negative certificates may change the recognition answer. A budgeted wrapper does not itself turn an exponential exact solver into a total QP decider.
7. A reduction in LP node count and an end-to-end speedup are different measurements. Benchmarks should report arithmetic cost, rational bit growth, propagation work, and the distribution of knot types, including hard unknots and nontrivial knots with weak classical invariants.

