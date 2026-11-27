# Lean formalization plan

## Present status

The paper contains conventional mathematical proofs and exact finite checks. Its new theorems have **not been formalized or kernel checked in Lean**. No Lean executable was available in this environment. The Python computations verify finite instances and implementation agreement; they do not replace the general proofs. This document is an architecture for a future formalization and contains no purported Lean proofs or placeholder axioms.

## 1. Finite linear-algebra model

Work over a finite field `F` of cardinality `q`, with no restriction on its characteristic. Let `V` have dimension `2n` and a nondegenerate alternating bilinear form. For each block, let `E_i` have dimension `d_i` and a fixed alternating form `H_i` of rank `2s_i`. Define a frame as an injective linear map from `E_i` to `V` preserving its given form. An isotropic frame is the special case `H_i = 0`.

Use alternating forms explicitly: skew symmetry alone is insufficient in characteristic two. Initially develop the statements with finite vector spaces and linear maps; introduce matrices only for executable instances and coordinate expressions. The finite set of tuples of frames carries the uniform probability mass function. The observation space consists of all alternating forms on the direct sum `E = ⨁ E_i` whose diagonal restrictions are the specified `H_i`.

Core prerequisites are rank-nullity, radicals and quotient forms, symplectic bases, finite-field cardinalities, and extension of an isometry between subspaces of a nondegenerate alternating space. Existing library coverage must be checked before selecting actual module paths or theorem names.

## 2. Embedding count

For a formed space of dimension `a` and alternating rank `2s`, prove the number `Emb_n(a,s)` of isometric injections into `V`.

Split the domain into a nondegenerate `2s`-dimensional summand and an `(a−2s)`-dimensional radical. Count embeddings of the first summand using transitivity of the symplectic group and its stabilizer. Count the radical images as ordered independent isotropic vectors in the orthogonal complement. This gives an integer product formula and the zero criterion `a−s > n`.

Derive the paper's expression with the finite products `η_m = ∏_{h=1}^m (1−q^(−2h))` afterward, as an identity in the rationals. Keeping the initial proof in natural-number cardinalities avoids division and zero-denominator issues in the combinatorial layer.

## 3. Exact joint law and support

For an observed Gram form `Γ` on `E`, let `R` be its radical, of dimension `r`, and put `T_i = R ∩ E_i`, of dimension `t_i`. If `Γ` has rank `2s`, any realizing linear map `E → V` has a kernel `K ⊆ R`. Injectivity on every block is exactly `K ∩ T_i = {0}`. For a fixed such kernel, realizations are in bijection with isometric injections of the induced formed quotient `E/K`.

Formalize the subspace-lattice Möbius identity and the Gaussian coefficient count of subspaces. Since the `T_i` lie in distinct direct summands, choices of subspaces inside them have additive dimensions. Inclusion-exclusion then proves the displayed formula for `T_ℓ`, the number of admissible kernels of dimension `ℓ`. Sum `T_ℓ Emb_n(D−ℓ,s)` and divide by the product of individual frame counts. This establishes each point probability, including all zero-probability observations.

For the support theorem, separately prove that the largest dimension of a subspace of `R` avoiding every `T_i` is `r − max_i t_i`. The upper bound is rank-nullity. For attainment, map each `T_i` injectively into a common space of dimension `max_i t_i`, combine these maps on their direct sum, and extend to `R`; the map is surjective because one `T_i` has maximal dimension. Its kernel gives the required subspace. Combine this with the embedding criterion to obtain exactly `s + max_i t_i ≤ n`.

## 4. Uniform radical moment

Prove `q^(dim rad Γ) = |{x ∈ E : Γx = 0}|` and exchange two finite sums. Partition the vectors `x` into zero, vectors supported on exactly one block, and vectors supported on at least two blocks.

For support in one block `i`, solvability first requires `H_i x_i = 0`, and the off-diagonal blocks impose `D−d_i` independent linear equations. For support in at least two blocks, prove that the linear map from the off-diagonal entries to `Γx` has image the hyperplane annihilating `x`, and thus rank `D−1`. The fixed diagonal contribution lies in that hyperplane because the forms are alternating. Counting the fibers gives the paper's exact moment `M = E_uniform[q^nullity]` for arbitrary diagonal forms.

This linear-map lemma is a useful independent milestone: it supplies the exact moment without requiring the full joint probability formula. Under the paper's balance condition `d_i−s_i ≤ D/2`, elementary estimates give the stated bound `M ≤ q+1+k`.

## 5. Total-variation thresholds

Develop finite total variation as both half the sum of absolute probability differences and the sum of deficits relative to the uniform law.

For `c = 2n−D ≥ 0`, retain only the term with globally injective realization (`K = 0`) in the exact count. Bound its likelihood ratio below using the finite product inequality `∏(1−u_j) ≥ 1−Σu_j`. Averaging the resulting deficit bound uses the radical moment and yields `TV ≤ min(1, M q^(−c)/(q²−1))`. Treat infeasible globally injective forms explicitly; the parity of the alternating rank makes the claimed pointwise lower bound nonpositive in that case.

For `w = D−2n > 0`, every realizable observation has radical dimension at least `w`. Apply the finite Markov bound to the nonnegative variable `q^nullity−1` under the uniform law. This proves `TV ≥ max(0, 1−(M−1)/(q^w−1))`.

The balanced-block asymptotic threshold is then a consequence of these finite inequalities. The numerical example requires only exact rational arithmetic after instantiating them; no floating-point limit argument is needed.

## 6. Forest independence

First prove that the law of a cross-Gram block against a random frame is independent of the particular fixed frame of the other prescribed type. This follows from symplectic isometry extension and the induced bijection on the finite set of random frames.

For a forest of observed pairs, remove a leaf. Conditional on all other frames, its edge has the same fixed marginal law and is independent of the remaining observations. Express this as a finite-sum factorization, then induct on the number of edges. This proves joint independence for every forest. In particular, the three edge matrices from three frames are pairwise independent. The whole triangle need not be independent, as the exact-law and rank-obstruction results show.

## 7. Suggested dependency order and verification boundary

1. Alternating forms, radical quotients, and finite symplectic frame counts.
2. Admissible-kernel bijection and exact support criterion.
3. Gaussian coefficients, subspace Möbius inversion, and the exact joint law.
4. The off-diagonal linear-map lemma and exact radical moment.
5. Finite total variation, the two explicit bounds, and the balanced threshold.
6. Symplectic transitivity, leaf elimination, and forest independence.
7. Rational numerical certificates and small matrix examples.

The accompanying exhaustive checker covers prime fields of orders two and three, including nonisotropic diagonal forms. General prime-power fields, arbitrary dimensions, and all asymptotic statements are covered by the written proofs and remain future formalization work. The general theorems do not use RH or GRH: their connection to the project is through the finite symplectic compression mechanism developed in the repository.
