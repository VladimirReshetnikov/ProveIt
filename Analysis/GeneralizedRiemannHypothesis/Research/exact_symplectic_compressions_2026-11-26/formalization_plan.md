# Formalization plan

This is a proof outline and dependency map, not a compiled Lean artifact. No theorem in this package is claimed kernel-checked. The finite enumeration scripts are independent numerical checks of the formulas.

## Recommended mathematical representation

Work over a finite field `K`, with `q = Fintype.card K`. Use finite-dimensional `K`-vector spaces, an alternating bilinear form `omega` on `V`, and an explicit nondegeneracy hypothesis. Treat the source and target as abstract spaces `U` and `W` with linear embeddings into `V`; the matrix presentation is a corollary after selecting bases.

Retain a separate zero-diagonal or alternating hypothesis in characteristic two. Do not replace it by skew symmetry alone.

## Dependency order

1. **Alternating-space decomposition.** Split a finite-dimensional alternating space into a nondegenerate summand and its radical. Prove that its rank is even and that it has a symplectic completion of dimension `dimension + radical_dimension`.

2. **Extension of subspace isometries.** Prove Witt extension for possibly degenerate subspaces of a nondegenerate alternating space. The paper's basis-completion proof avoids division by two. This gives transitivity of the symplectic group on injective frames with a fixed Gram matrix.

3. **Embedding count.** Count symplectic pairs successively, then independent isotropic radical vectors. Establish the integer-product expression for `E_N(k,s)` before rewriting it as a rational-looking product. This avoids unnecessary field coercions in cardinality arguments.

4. **Two-subspace avoidance count.** For disjoint `A,B <= R`, partition `d`-subspaces `D` by `j = dim(D meet (A+B))`. Identify this intersection with the graph of an isomorphism between two `j`-subspaces; identify the remaining freedom with linear maps into a quotient. Apply Gaussian-binomial and general-linear-group cardinalities.

5. **Concatenated-kernel equivalence.** A pair `(X,Y)` with prescribed pairings is equivalent to a kernel `D <= rad G` meeting neither summand, together with an injective isometry from `(U direct_sum W)/D` to `V`. Prove this as an actual equivalence of finite types. The quotient rank remains the rank of `G` because `D` lies in its radical.

6. **Uniform fibre cardinality.** Use the group action to show every first frame has the same number of extensions, preserving the chosen domain kernel. Divide total cardinalities to obtain the point probability, then the conditional intersection law.

7. **Support and minimal realization.** Use positivity of the integer products and the exact range of `d`. The final inequality is elementary arithmetic. Construct a maximal admissible kernel to prove attainment of the minimum ambient dimension.

8. **Fixed-dimension asymptotics.** Rewrite the likelihood as a rational function of `t=q^(-2N)`. Its denominator is nonzero near zero. Compute its constant and linear terms using finite products, then take the finite sum of absolute values defining total variation. The scalar marginal proves positivity of the leading coefficient.

9. **Nondegenerate complementary case.** Split `V = im X direct_sum (im X)^perp`. The forced component has Gram `-M^T F^(-1) M`; hence the residual form is `H + M^T F^(-1) M`. Count all residual maps by their kernels. Nonsingularity of `H` gives injectivity of the full frame automatically.

10. **Optimal likelihood event.** Prove the two sign inequalities for residual corank zero and positive even corank. In a finite probability space, the set where one mass exceeds the other attains total variation. This identifies the exact optimal residual singularity test.

11. **Finite Fourier estimate.** Express additive characters of alternating matrices using upper-triangular coordinates, so characteristic two is covered. Average `psi(x^T C y)` over independent row pairs. Its value is `q^(-rank C)`. Apply finite Plancherel and the alternating-rank count to get the explicit total-variation bound.

12. **Boundary limits.** Prove convergence and positivity of the two infinite products using summable deficits. Combine the Fourier approximation with the exact optimal-test formula. Use a union bound over projective lines for the rank-only distance.

## Statements that should be kept separate

- The exact law is valid for any prime power and every admissible ambient dimension.
- The sharp `q^(-2N)` expansion fixes `q,a,b,F,H` while `N` increases.
- The positive limiting constant fixes `q` but requires both `b -> infinity` and `a-b -> infinity`, with ambient dimension `a+b` and both restricted forms nonsingular.
- The uniform positive lower bound for complementary dimensions needs only `a,b -> infinity`; it does not compute the exact limit along square blocks.
- The support criterion assumes the observation comes from injective maps on each coordinate summand. Replacing this by injectivity of the concatenation would discard the overlap terms and change the theorem.

## Computational certificates

The integer/rational evaluator can be translated into executable Lean definitions independently of the abstract proof. A useful first milestone is a kernel-checked verification of the finite examples and the support arithmetic, followed by the finite-type equivalence in item 5. Numerical agreement alone should never be used as an axiom for the general theorem.
