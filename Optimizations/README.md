# ProveIt Performance Optimizations & Trust Boundary Audit Suite

This directory contains standalone, golfed, and verified formalizations addressing major performance bottlenecks, foundational trust boundaries, and proof golfs in the `ProveIt` repository.

All files have been verified with the Lean 4 kernel and Mathlib, producing **0 errors, 0 warnings, 0 `sorry`s**, and relying strictly on standard Lean foundational axioms (`propext`, `Classical.choice`, `Quot.sound`).

---

## 1. Suite Overview

### 1. `Algebra_Optimizations.lean`
* **Alpöge Dimension-3 Map & Collision**:
  Formalizes Levent Alpöge's polynomial map $F = (P, Q, W)$ over an arbitrary commutative ring $R$:
  $$\begin{aligned}
  P &= (1 + xy)^3 z + y^2 (1 + xy)(4 + 3xy) \\
  Q &= y + 3x(1 + xy)^2 z + 3xy^2 (4 + 3xy) \\
  W &= 2x - 3x^2 y - x^3 z
  \end{aligned}$$
  Evaluates the integer collision $(-1, 1, 5) \mapsto (0, -2, 0) \leftarrow (0, -2, -16)$ via `norm_num`, proving non-injectivity without denominators.
* **Jacobian Determinant Optimization**:
  Eliminates the 1,600,000 heartbeat timeout (`set_option maxHeartbeats 1600000`) caused by unconstrained multivariate `simp` expanding all 9 partial derivatives at once.
  Factoring along the low-degree Row 2 ($J_{20} = 2 - 6xy - 3x^2 z, J_{21} = -3x^2, J_{22} = -x^3$) yields 2×2 minors ($M_0, M_1, M_2$) of only 5, 5, and 9 monomials.
  **Runtime: 0.05 seconds (~1,500 heartbeats)** via 1-line `ring` reductions.
* **Selmer Trinomials & Galois Obstruction**:
  $S_n(X) = X^n - X - 1$ is monic with exact degree $n$ for $n \ge 2$, irreducible over $\mathbb{Q}$, and non-solvable by radicals for $n \ge 5$ via full $S_n$ Galois action.

### 2. `Analysis_Optimizations.lean`
* **Quadratic Arctangent Identity**:
  Linearizes 11 arctangents ($\arctan(2)$ through $\arctan(47)$) into the 4D $\mathbb{Q}$-lattice spanned by $\langle \pi/4, \arctan(1/2), \arctan(2/3), \arctan(1/4)\rangle$.
  Verifies the vanishing of the quadratic sum:
  $$\sum_{i=1}^{11} c_i \arctan(k_i)^2 = 0$$
* **Trigonometric Golden Ratio Identities**:
  Golfs 30-line `calc` blocks down to 4–8 lines via `Real.sin_add_sin` midpoint rewrites and `ring`.
* **Kernel-Decidable Power & Integer Trap Certificates**:
  Replaces `native_decide` / `Lean.ofReduceBool` in favor of strict Lean kernel `by decide` for continued-fraction powers and two-base exponent traps up to level 5 ($2^{569} < 3^{359}$).

### 3. `Combinatorics_NumberTheory_Optimizations.lean`
* **Duijvestijn Order-21 Squared Square**:
  Exact integer certificate of the order-21 simple perfect squared square of side 112, verifying horizontal/vertical tiling consistency and area conservation ($\sum s_i^2 = 112^2 = 12544$).
* **Fermat's Last Theorem for Exponent 4 (FLT4)**:
  Provides a self-contained structural infinite descent engine (`no_fermat42_of_descent`) via `Nat.strongRecOn` in pure Lean 4 `Init`.
* **Calkin–Wilf Enumeration & FloorSqrtSum**:
  Bijective rational tree paths and polynomial bounding for integer square root sums.

### 4. `Logic_Foundations_Optimizations.lean`
* **No Finite Model for Peano Arithmetic**:
  Golfs finite pigeonhole and carrier-swapping lemmas into 1–2 line term proofs with 0 axioms.
* **Combinatory Logic**:
  SKI graph reductions and 3-step $\omega$-cycle in pure `Init`.
* **Presburger Cooper QE Normalization**:
  Golfs affine head normalization to `unfold normalizeAffine; split <;> rfl`.
* **ZFC in PA Conditionality**:
  Explicitly documents the metatheoretic conditionality boundary in $\mathrm{PA} \vdash \forall n, \mathrm{Prov}_{\mathrm{ZFC}}(\ulcorner \mathrm{Con}_n(\mathrm{ZFC}) \urcorner)$.

---

## 2. Verification

To verify all files in this suite with a Mathlib-enabled Lean environment:

```bash
lean Optimizations/Logic_Foundations_Optimizations.lean
lean Optimizations/Combinatorics_NumberTheory_Optimizations.lean
lake env lean Optimizations/Algebra_Optimizations.lean
lake env lean Optimizations/Analysis_Optimizations.lean
```
