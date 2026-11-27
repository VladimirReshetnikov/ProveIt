# Independent adversarial review: exact symplectic compression law

**Outcome:** The general formula, its support criterion, conditional intersection law, first correction, and the exact two-plane example survived independent derivation and the finite checks described below. I found no mathematical gap in these statements under their stated hypotheses. This is a mathematical/source-code review, not a Lean formalization or a certification of publication priority.

## 1. Scope of the review

The ambient space is a nondegenerate alternating space V of dimension 2n over F_q, for an arbitrary prime power q. The target and source frames Y:F_q^a -> V and X_0:F_q^b -> V are injective, with fixed alternating Gram matrices H_1,H_0 of ranks 2s_1,2s_0. The source is moved by a uniform symplectic element. The observed matrix is M=Y^T J X.

The hypotheses must include injectivity, alternating forms (in particular zero diagonals in characteristic two), and realizability a-s_1<=n, b-s_0<=n when the data are specified by Gram matrices rather than by actual frames. These ensure the probability denominator is positive.

## 2. An independent derivation of the main counting argument

For fixed M, form Gamma=[[H_1,M],[-M^T,H_0]] on E=E_1 direct-sum E_0. Let its rank be 2s and radical R have dimension r=a+b-2s. A pair of frames with these pairings is exactly a linear map F:E -> V such that F^*J=Gamma and F restricts injectively to both summands.

Its kernel L is contained in R: if F(v)=0, then Gamma(v,w)=J(Fv,Fw)=0 for every w. The two injectivity conditions are exactly L intersect E_i = 0. Conversely, any such L and any isometric injection E/L -> V produce precisely one permissible F. The quotient has dimension a+b-dim L and alternating rank 2s.

There is **no additional automorphism or GL factor** at this step. L is a concrete subspace of the fixed domain and E/L is its canonical quotient. E_n(d,s) counts maps out of that quotient, not isometry classes of images. Dividing by its automorphism group would undercount.

To fix Y, one may first count independent uniform pairs (Y,X) and then divide by E_n(a,s_1)E_n(b,s_0). This is justified even when H_1 is degenerate. Witt extension for nondegenerate alternating ambient spaces makes the symplectic group transitive on embeddings with a prescribed Gram matrix. Coupling (Y,X) with (hY,hX) preserves the cross pairings, and hX has the same uniform law as X. A direct elementary version follows by completing the nondegenerate part and the radical of a subspace to a symplectic basis.

Let R_i=R intersect E_i, of dimensions t_i. They are disjoint. Choose a complementary c-space to R_0 direct-sum R_1 inside R. For a transverse ell-subspace L, its intersection with R_0 direct-sum R_1 is a k-dimensional graph of an isomorphism between k-subspaces of R_0,R_1. This gives

    [t_0 choose k]_q [t_1 choose k]_q |GL_k(q)|.

Choose its image D in the c-dimensional complement, of dimension ell-k. After fixing the graph and D, the remaining choices are linear maps D -> (R_0 direct-sum R_1)/graph. There are

    q^((ell-k)(t_0+t_1-k))

such maps. No further transversality restriction appears: any intersection with E_i must lie in R_i and hence in the already controlled graph. This independently gives the stated T_ell formula, and therefore the exact likelihood.

## 3. Independent derivation of the frame count

Split the source alternating space into s symplectic pairs and a radical of dimension d-2s. For each symplectic pair in a remaining 2N-dimensional nondegenerate space, the first vector has q^(2N)-1 choices and its partner with pairing one has q^(2N-1) choices. Pass to the symplectic orthogonal complement and repeat.

After embedding the 2s-dimensional nondegenerate part, choose an ordered independent isotropic frame in a 2(n-s)-dimensional complement. After i choices the next vector has

    q^(2(n-s)-i)-q^i

choices. This is possible exactly when d-2s<=n-s. Multiplication and collection of powers gives

    E_n(d,s)=q^(2nd-binomial(d,2))
             product_(j=n-d+s+1)^n (1-q^(-2j)),

with feasibility d-s<=n. This verifies both the exponent and every product endpoint in the proposed formula.

## 4. Support and intersection law

The largest dimension of an L in R disjoint from both R_i is

    ell_max = c+min(t_0,t_1) = r-max(t_0,t_1).

The graph construction attains every dimension between zero and this maximum. The quotient embeds iff ell>=a+b-s-n. A feasible ell therefore exists iff

    s+max(t_0,t_1)<=n.

This verifies the sharp support criterion and the minimal ambient dimension 2[s+max(t_0,t_1)]. It also verifies the conditional intersection formula: because both coordinate restrictions of F are injective, dim ker F equals dim(im Y intersect im X). Every permissible kernel of a fixed dimension has the same number E_n(a+b-ell,s) of quotient embeddings, so the asserted uniformity of relation subspaces conditional on dimension is valid.

## 5. Characteristic-two and endpoint audit

- The argument is about alternating bilinear forms, not quadratic forms. Witt extension and alternating normal form apply in characteristic two; no division by two occurs anywhere.
- In characteristic two, skew symmetry alone is insufficient. A symmetric matrix with nonzero diagonal is not an admissible alternating Gram matrix. The theorem correctly requires zero diagonal.
- Zero-dimensional sources, targets, and ambient space use empty products equal to one. If a=0 or b=0, there is only one observed matrix and its probability is one.
- Infeasible combined Gram data produce zero probability through the E_n feasibility condition; the denominator still remains positive because the individual frames are assumed realizable.
- At n=1,a=b=2,H_1=H_0=J_2, the only attainable matrices have determinant one, each with probability 1/[q(q^2-1)]. The exact two-plane formula has this endpoint.
- The Schur complement sign is correct: for invertible H_1 the residual is H_0+M^T H_1^(-1)M. With H_1=H_0=J_2 this is (1-det M)J_2.

## 6. Quantitative review

Let z=q^(-2n), d=a+b, and C(u,z)=product_(j=0)^(u-1)(1-q^(2j)z). Factoring the exact law yields the rational identity

    q^(ab)P_n(M)
      = [sum_ell T_ell q^(d ell-ell(ell+1)/2) z^ell C(d-ell-s,z)]
        /[C(a-s_1,z)C(b-s_0,z)].

Since the denominator has constant term one, its Taylor coefficient is exactly

    K(M)=q^(d-1)T_1-A_q(d-s)+A_q(a-s_1)+A_q(b-s_0),

where A_q(u)=sum_(j=0)^(u-1)q^(2j). Counting radical lines gives

    T_1=(q^r-q^t_0-q^t_1+1)/(q-1).

This independently verifies the first-correction and total-variation expansions. The remainder is uniform over M for **fixed** q,a,b,H_1,H_0 because that matrix set is finite. No claim of uniformity for growing frame dimensions follows without additional bounds.

There is no hidden positive-dimension degeneracy in the leading term. For nonzero u,v, the scalar u^T Mv pairs a fixed nonzero vector with a uniform nonzero vector in V. Its distribution differs from uniform by exact TV

    (q-1)/[q(q^(2n)-1)].

This lower-bounds the full matrix TV. Hence K is not identically zero when a,b>=1, and the fixed-parameter rate q^(-2n) is always sharp. Equivalently, for every nontrivial additive character, the rank-one Fourier coefficient is exactly -1/(q^(2n)-1).

For two symplectic planes, the critical numerator is E_n(4,1)+(q+1)E_n(3,1)+E_n(2,1); off determinant one it is E_n(4,2). Substitution gives exactly the two likelihoods and TV claimed in `asymptotics.tex`. All quadratic terms cancel in the critical likelihood numerator; this cancellation was checked symbolically as well as by hand.

## 7. Independent finite and symbolic verification

`audit_symplectic_counts.py` directly enumerates source frames, with a separate finite-field implementation, and compares the observed matrix counts with the formula. It checks 5,574 prescribed-Gram frames and all 1,213 matrix cases across fourteen cases. These include F_2, F_3, F_4=F_2[x]/(x^2+x+1), isotropic and nondegenerate two-dimensional frames, mixed types, three-dimensional degenerate frames, rectangular compressions, and impossible outputs. Every frame count, matrix probability, normalization, and support criterion passed. Results: `results/independent_frame_audit.json`.

`check_asymptotics.py` uses integer polynomials and exact rational arithmetic, with no floating-point calculations. For all 388 two-by-two matrices arising from the four choices H_i in {0,J_2} over F_2 and F_3, it checks the coefficient K by formal differentiation, its zero total mass, its scalar marginal, and exact likelihood evaluation at n=2. For the two-plane case it verifies the entire rational-function identity by cross-multiplying polynomials, and verifies the TV at n=1,2,3. All checks passed. Results: `results/asymptotics.json`.

The tests supplement the proof; they do not replace it. All scripts use the Python standard library. `check_asymptotics.py` imports the finite-field/counting helpers from `audit_symplectic_counts.py`, so both files must be included together.

## 8. Presentation and novelty cautions

The mathematical result is unconditional finite symplectic linear algebra. Its connection to the GRH source is the finite-field compression mechanism, not a dependence on the truth of RH. The exact arbitrary-source/arbitrary-target law is substantially stronger than a rank tail estimate or a first moment, and it identifies the precise Gram invariants that suffice for likelihood and intersection statistics.

The ingredients are classical. The formula may be related to intersection numbers of symplectic orbit configurations; this proof review does not establish that the closed law or its first correction has never appeared in that literature. Publication-priority wording should reflect the separate literature search.

The stated O((a+b)^2) number of scalar summands is a count of terms in the Gaussian sum. It is not a bit-complexity claim independent of q or n: exact integer sizes and matrix-rank computations also contribute to computational cost.
