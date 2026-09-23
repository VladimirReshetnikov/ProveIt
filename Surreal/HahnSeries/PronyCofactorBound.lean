import Surreal.Algebra.PronyPade
import Surreal.HahnSeries.ChartIsometry
import Surreal.HahnSeries.PolynomialValuation
import Mathlib.Algebra.BigOperators.WithTop
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.RingTheory.HahnSeries.Valuation

/-!
# The exact cofactor correction system and the uniform cofactor estimate

This file proves `prony:lem:cofactorbound`, together with the exact correction system
`prony:eq:Bsystem` and the ansatz `prony:eq:Ph`, of
`docs/surcomplex/prony-reconstruction-at-surreal-scales/article.tex`.

## Field part

Over an arbitrary field `K`, let `a` be distinct nodes and `w` nonzero weights. Let `P` be the
node polynomial, `Q_i = P/(X - a_i)` the cofactors, `p_i = Q_i(a_i)` and `c_i = w_i p_i²`
(`cofactorWeight`). The perturbed moments are `m̂ = m + ε`, so `L̂ = L + ΔL` with
`ΔL(X^k) = ε_k` (`momentLinear_add`). For `P̂ = P + ∑ b_j Q_j` (`perturbedPoly`) put
`u_i = c_i b_i` (`scaledCoords`), `B_ij = ΔL(Q_i Q_j)/c_j` (`corrMatrix`) and
`g_i = ΔL(P Q_i)` (`corrRhs`).

* `momentLinear_perturbedPoly_mul_cofactor`: the identity `L̂(P̂ Q_i) = ((I + B) u)_i + g_i`.
  It is exact, not a first-order approximation.
* `annihilates_iff_corrSystem`: `L̂(P̂ q) = 0` for every `q` of degree `< n` if and only if
  `(I + B) u = -g`. This uses that the cofactors span the polynomials of degree `< n`
  (`annihilates_iff_cofactor`). Testing on `1, X, …, X^{n-1}` is equivalent
  (`annihilates_iff_X_pow`).
* `momentLinear_perturbed_cofactor_mul`: in the cofactor basis the perturbed Hankel form is
  `(I + B) diag(c_i)`. With the change of basis `cofactorCoeffMatrix_mul_hankel`,
  `det_hankel_ne_zero_of_det_ne_zero` shows that invertibility of `I + B` implies
  invertibility of the perturbed Hankel matrix.
* `existsUnique_perturbedPoly`: every monic polynomial of degree `n` has unique cofactor
  coordinates, so the ansatz `prony:eq:Ph` misses no monic annihilator.

## Hahn part

Work over `R((t^Γ))`, with `R` any field and `Γ` any linearly ordered abelian group. The source
takes `R = ℝ` or `ℂ` and `Γ` nontrivial. Neither restriction is used, and divisibility of `Γ`
is not needed. The nodes are assumed integral, as in the source. `nodeLoss a w i` is
`E_i = v(w_i) + 2 d_i` with `d_i = ∑_{j ≠ i} v(a_i - a_j)`, and `orderTop_cofactorWeight` is
`v(c_i) = E_i`.

* `le_orderTop_of_one_add_mulVec`: if every entry of `B` has positive valuation and
  `(I + B) u = g`, then `v(u_i) ≥ κ` for all `i` whenever `v(g_i) ≥ κ` for all `i`. The proof
  is the ultrametric inequality at a coordinate of least valuation. It replaces the adjugate
  and Neumann-series arguments of the source. With `g = 0` it gives invertibility of `I + B`
  (`det_one_add_ne_zero`). Applied to the columns of `(I + B)⁻¹` it gives the source's
  integrality of the entries of `(I + B)⁻¹` (`orderTop_inv_one_add_nonneg`).
* `le_orderTop_corrMatrix`, `orderTop_corrMatrix_pos`, `le_orderTop_corrRhs`: `Q_i Q_j` and
  `P Q_i` have integral coefficients, so `v(B_ij) ≥ κ - E_j > 0` and `v(g_i) ≥ κ`.
* `cofactorbound_system` (`prony:lem:cofactorbound`): suppose `v(ε_k) ≥ κ` for `k < 2n` and
  `κ > E_j` for every `j`. Then the system `(I + B) u = -g` has a unique solution. Every
  solution satisfies `v(u_i) ≥ κ` and `v(u_i/c_i) ≥ κ - E_i`.
* `cofactorbound` gives the same statement in the cofactor coordinates `b` of `P̂`. There is a
  unique `b` with `L̂(P̂ q) = 0` for all `q` of degree `< n`. It satisfies `v(c_i b_i) ≥ κ` and
  `v(b_i) ≥ κ - E_i` (`prony:eq:bprecision`).
* `det_hankel_perturbed_ne_zero` and `eq_perturbedPoly_of_annihilates`: the perturbed Hankel
  matrix is invertible, and `P̂` is the unique monic annihilator of degree `n`.

Nothing in `prony:lem:cofactorbound` or `prony:eq:Bsystem` remains pending. This file does not
formalize the root localization `prony:lem:localroots` or the main theorem `prony:thm:main`,
which use the bound.
-/

namespace Surreal.PronyBound

open Matrix Polynomial Finset Surreal.Prony

noncomputable section

section Field

variable {K : Type*} [Field K] {n : ℕ}

/-- `prony:eq:Ph`: the monic polynomial `P̂ = P + ∑ b_j Q_j` in cofactor coordinates `b`. -/
def perturbedPoly (a b : Fin n → K) : K[X] :=
  nodePoly a + ∑ j, C (b j) * cofactor a j

/-- The diagonal values `c_i = w_i p_i²` of `prony:eq:cofactor`, with `p_i = Q_i(a_i)`. -/
def cofactorWeight (a w : Fin n → K) (i : Fin n) : K :=
  w i * (cofactor a i).eval (a i) ^ 2

/-- `prony:eq:Bsystem`: the scaled unknowns `u_i = c_i b_i`. -/
def scaledCoords (a w b : Fin n → K) (i : Fin n) : K :=
  cofactorWeight a w i * b i

/-- `prony:eq:Bsystem`: the correction matrix `B_ij = ΔL(Q_i Q_j)/c_j`, where `ΔL` is the
moment functional of the perturbation `ε`. -/
def corrMatrix (a w : Fin n → K) (ε : ℕ → K) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j => momentLinear ε (cofactor a i * cofactor a j) / cofactorWeight a w j

/-- `prony:eq:Bsystem`: the right-hand side `g_i = ΔL(P Q_i)`. -/
def corrRhs (a : Fin n → K) (ε : ℕ → K) (i : Fin n) : K :=
  momentLinear ε (nodePoly a * cofactor a i)

theorem cofactorWeight_ne_zero {a w : Fin n → K} (ha : Function.Injective a)
    (hw : ∀ i, w i ≠ 0) (i : Fin n) : cofactorWeight a w i ≠ 0 :=
  mul_ne_zero (hw i) (pow_ne_zero 2 (eval_cofactor_self_ne_zero ha i))

/-- The moment functional is additive in the moment sequence: `L̂ = L + ΔL`. -/
theorem momentLinear_add (m ε : ℕ → K) (f : K[X]) :
    momentLinear (m + ε) f = momentLinear m f + momentLinear ε f := by
  rw [momentLinear_eq_sum _ _ (Nat.lt_succ_self _), momentLinear_eq_sum m _ (Nat.lt_succ_self _),
    momentLinear_eq_sum ε _ (Nat.lt_succ_self _), ← Finset.sum_add_distrib]
  simp only [Pi.add_apply, mul_add]

theorem momentLinear_C_mul (m : ℕ → K) (c : K) (f : K[X]) :
    momentLinear m (C c * f) = c * momentLinear m f := by
  rw [C_mul', map_smul, smul_eq_mul]

theorem momentLinear_perturbedPoly_mul (m : ℕ → K) (a b : Fin n → K) (f : K[X]) :
    momentLinear m (perturbedPoly a b * f) =
      momentLinear m (nodePoly a * f) + ∑ j, b j * momentLinear m (cofactor a j * f) := by
  rw [perturbedPoly, add_mul, map_add, Finset.sum_mul, map_sum]
  simp only [mul_assoc, momentLinear_C_mul]

/-- `prony:eq:Bsystem`, exact form. Testing `P̂ = P + ∑ b_j Q_j` against `Q_i` with the
perturbed functional `L̂ = L + ΔL` gives `c_i b_i + ∑_j ΔL(Q_i Q_j) b_j + ΔL(P Q_i)`, that is,
`((I + B) u)_i + g_i`. -/
theorem momentLinear_perturbedPoly_mul_cofactor {a w : Fin n → K} (ha : Function.Injective a)
    (hw : ∀ i, w i ≠ 0) (ε : ℕ → K) (b : Fin n → K) (i : Fin n) :
    momentLinear (moment a w + ε) (perturbedPoly a b * cofactor a i) =
      ((1 + corrMatrix a w ε) *ᵥ scaledCoords a w b) i + corrRhs a ε i := by
  have h1 : ∑ j, b j * momentLinear (moment a w) (cofactor a j * cofactor a i) =
      scaledCoords a w b i := by
    simp only [momentLinear_moment, momentFunctional_cofactor_mul, mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, scaledCoords, cofactorWeight]
    ring
  have h2 : ∑ j, corrMatrix a w ε i j * scaledCoords a w b j =
      ∑ j, b j * momentLinear ε (cofactor a j * cofactor a i) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [corrMatrix, of_apply, scaledCoords, ← mul_assoc,
      div_mul_cancel₀ _ (cofactorWeight_ne_zero ha hw j), mul_comm (cofactor a i), mul_comm]
  rw [momentLinear_add, momentLinear_perturbedPoly_mul, momentLinear_perturbedPoly_mul, h1,
    momentLinear_moment, momentFunctional_nodePoly_mul, add_mulVec, one_mulVec, Pi.add_apply]
  simp only [mulVec, dotProduct]
  rw [h2, corrRhs]
  ring

/-- Annihilation of all polynomials of degree `< n` is tested on `1, X, …, X^{n-1}`. -/
theorem annihilates_iff_X_pow (Λ : K[X] →ₗ[K] K) (F : K[X]) :
    (∀ q : K[X], q.degree < n → Λ (F * q) = 0) ↔ ∀ r < n, Λ (F * X ^ r) = 0 := by
  refine ⟨fun h r hr => h _ ?_, fun h q hq => ?_⟩
  · rw [degree_X_pow]
    exact WithBot.coe_lt_coe.mpr hr
  · by_cases hq0 : q = 0
    · rw [hq0, mul_zero, map_zero]
    rw [q.as_sum_range_C_mul_X_pow' ((natDegree_lt_iff_degree_lt hq0).mpr hq), Finset.mul_sum,
      map_sum]
    refine Finset.sum_eq_zero fun r hr => ?_
    rw [mul_left_comm, C_mul', map_smul, h r (Finset.mem_range.mp hr), smul_zero]

theorem natDegree_cofactor_lt (a : Fin n → K) (i : Fin n) : (cofactor a i).natDegree < n := by
  have hi := i.2
  rw [natDegree_cofactor]
  omega

/-- The cofactors of distinct nodes span the polynomials of degree `< n`, so annihilation of
that space is tested on the cofactors. -/
theorem annihilates_iff_cofactor {a : Fin n → K} (ha : Function.Injective a)
    (Λ : K[X] →ₗ[K] K) (F : K[X]) :
    (∀ q : K[X], q.degree < n → Λ (F * q) = 0) ↔ ∀ i, Λ (F * cofactor a i) = 0 := by
  refine ⟨fun h i => h _ ?_, fun h q hq => ?_⟩
  · rw [degree_eq_natDegree (cofactor_monic a i).ne_zero]
    exact WithBot.coe_lt_coe.mpr (natDegree_cofactor_lt a i)
  · rw [eq_sum_C_mul_cofactor ha hq, Finset.mul_sum, map_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [mul_left_comm, C_mul', map_smul, h j, smul_zero]

/-- `prony:eq:Bsystem`: `P̂ = P + ∑ b_j Q_j` annihilates every polynomial of degree `< n`
for the perturbed functional if and only if `(I + B) u = -g`, where `u_i = c_i b_i`. -/
theorem annihilates_iff_corrSystem {a w : Fin n → K} (ha : Function.Injective a)
    (hw : ∀ i, w i ≠ 0) (ε : ℕ → K) (b : Fin n → K) :
    (∀ q : K[X], q.degree < n →
        momentLinear (moment a w + ε) (perturbedPoly a b * q) = 0) ↔
      (1 + corrMatrix a w ε) *ᵥ scaledCoords a w b = -corrRhs a ε := by
  rw [annihilates_iff_cofactor ha]
  simp only [momentLinear_perturbedPoly_mul_cofactor ha hw]
  refine ⟨fun h => funext fun i => ?_, fun h i => ?_⟩
  · rw [Pi.neg_apply, eq_neg_iff_add_eq_zero]
    exact h i
  · rw [h, Pi.neg_apply, neg_add_cancel]

/-- `prony:eq:Bsystem`: in the cofactor basis the perturbed Hankel bilinear form is
`(I + B) diag(c_i)`. -/
theorem momentLinear_perturbed_cofactor_mul {a w : Fin n → K} (ha : Function.Injective a)
    (hw : ∀ i, w i ≠ 0) (ε : ℕ → K) (i j : Fin n) :
    momentLinear (moment a w + ε) (cofactor a i * cofactor a j) =
      ((1 + corrMatrix a w ε) * diagonal (cofactorWeight a w)) i j := by
  rw [momentLinear_add, momentLinear_moment, momentFunctional_cofactor_mul, add_mul, one_mul,
    Matrix.add_apply, mul_diagonal, diagonal_apply, corrMatrix, of_apply,
    div_mul_cancel₀ _ (cofactorWeight_ne_zero ha hw j)]
  split_ifs with hij
  · subst hij
    rfl
  · rfl

/-- The coefficient matrix `T_ir = [X^r] Q_i` of the cofactors in the monomial basis. -/
def cofactorCoeffMatrix (a : Fin n → K) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i r => (cofactor a i).coeff r

/-- The moment functional as a bilinear form in the monomial coordinates. -/
theorem momentLinear_mul_eq_sum (m : ℕ → K) {f g : K[X]} (hf : f.natDegree < n)
    (hg : g.natDegree < n) :
    momentLinear m (f * g) = ∑ r : Fin n, ∑ s : Fin n, f.coeff r * m (r + s) * g.coeff s := by
  conv_lhs => rw [f.as_sum_range_C_mul_X_pow' hf, g.as_sum_range_C_mul_X_pow' hg]
  rw [Finset.sum_mul_sum, map_sum, Finset.sum_range]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [map_sum, Finset.sum_range]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [show C (f.coeff r) * X ^ (r : ℕ) * (C (g.coeff s) * X ^ (s : ℕ)) =
      C (f.coeff r * g.coeff s) * X ^ ((r : ℕ) + s) by rw [C_mul, pow_add]; ring,
    momentLinear_C_mul_X_pow]
  ring

/-- Change of basis: `T H Tᵀ` is the Gram matrix `(L(Q_i Q_j))` of the cofactors. -/
theorem cofactorCoeffMatrix_mul_hankel (a : Fin n → K) (m : ℕ → K) :
    cofactorCoeffMatrix a * hankel n m * (cofactorCoeffMatrix a)ᵀ =
      Matrix.of fun i j => momentLinear m (cofactor a i * cofactor a j) := by
  ext i j
  rw [of_apply, momentLinear_mul_eq_sum m (natDegree_cofactor_lt a i) (natDegree_cofactor_lt a j),
    mul_apply, Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [mul_apply, Finset.sum_mul]
  rfl

/-- `prony:eq:Bsystem`: invertibility of `I + B` implies invertibility of the perturbed Hankel
matrix, since `T H Tᵀ = (I + B) diag(c_i)`. -/
theorem det_hankel_ne_zero_of_det_ne_zero {a w : Fin n → K} (ha : Function.Injective a)
    (hw : ∀ i, w i ≠ 0) (ε : ℕ → K) (hB : (1 + corrMatrix a w ε).det ≠ 0) :
    (hankel n (moment a w + ε)).det ≠ 0 := by
  have h := cofactorCoeffMatrix_mul_hankel a (moment a w + ε)
  have hG : (Matrix.of fun i j => momentLinear (moment a w + ε) (cofactor a i * cofactor a j)) =
      (1 + corrMatrix a w ε) * diagonal (cofactorWeight a w) := by
    ext i j
    rw [of_apply, momentLinear_perturbed_cofactor_mul ha hw]
  rw [hG] at h
  have hdet := congrArg Matrix.det h
  rw [det_mul, det_mul, det_transpose, det_mul, det_diagonal] at hdet
  intro h0
  rw [h0, mul_zero, zero_mul] at hdet
  exact mul_ne_zero hB (Finset.prod_ne_zero_iff.mpr fun i _ => cofactorWeight_ne_zero ha hw i)
    hdet.symm

theorem perturbedPoly_monic (a b : Fin n → K) : (perturbedPoly a b).Monic := by
  refine (nodePoly_monic a).add_of_left ?_
  rw [degree_eq_natDegree (nodePoly_monic a).ne_zero, natDegree_nodePoly]
  exact degree_sum_C_mul_cofactor_lt a b

theorem natDegree_perturbedPoly (a b : Fin n → K) : (perturbedPoly a b).natDegree = n := by
  rw [perturbedPoly, natDegree_add_eq_left_of_degree_lt, natDegree_nodePoly]
  rw [degree_eq_natDegree (nodePoly_monic a).ne_zero, natDegree_nodePoly]
  exact degree_sum_C_mul_cofactor_lt a b

/-- The ansatz `prony:eq:Ph` misses nothing: every monic polynomial of degree `n` is
`P + ∑ b_j Q_j` for unique cofactor coordinates `b`. -/
theorem existsUnique_perturbedPoly {a : Fin n → K} (ha : Function.Injective a) {F : K[X]}
    (hF : F.Monic) (hFd : F.natDegree = n) : ∃! b : Fin n → K, perturbedPoly a b = F := by
  have hdeg : (F - nodePoly a).degree < n := by
    have h := degree_sub_lt (p := F) (q := nodePoly a)
      (by rw [degree_eq_natDegree hF.ne_zero, degree_eq_natDegree (nodePoly_monic a).ne_zero,
        hFd, natDegree_nodePoly]) hF.ne_zero
      (by rw [hF.leadingCoeff, (nodePoly_monic a).leadingCoeff])
    rwa [degree_eq_natDegree hF.ne_zero, hFd] at h
  refine ⟨fun j => (F - nodePoly a).eval (a j) / (cofactor a j).eval (a j), ?_, ?_⟩
  · simp only [perturbedPoly]
    rw [← eq_sum_C_mul_cofactor ha hdeg, add_sub_cancel]
  · intro b hb
    funext j
    have h := congrArg (fun f => (f - nodePoly a).eval (a j)) hb
    simp only [perturbedPoly, add_sub_cancel_left, eval_sum_C_mul_cofactor] at h
    show b j = (F - nodePoly a).eval (a j) / (cofactor a j).eval (a j)
    rw [← h, mul_div_cancel_right₀ _ (eval_cofactor_self_ne_zero ha j)]

/-- A square linear system with nonzero determinant has exactly one solution. -/
theorem existsUnique_mulVec_eq {M : Matrix (Fin n) (Fin n) K} (hM : M.det ≠ 0)
    (y : Fin n → K) : ∃! u, M *ᵥ u = y := by
  have hdet : IsUnit M.det := isUnit_iff_ne_zero.mpr hM
  refine ⟨M⁻¹ *ᵥ y, ?_, fun u hu => ?_⟩
  · show M *ᵥ (M⁻¹ *ᵥ y) = y
    rw [mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]
  · rw [← hu, mulVec_mulVec, nonsing_inv_mul _ hdet, one_mulVec]

/-- The change of unknowns `u_i = c_i b_i` is bijective for a regular configuration. -/
theorem existsUnique_scaledCoords {a w : Fin n → K} (ha : Function.Injective a)
    (hw : ∀ i, w i ≠ 0) {p : (Fin n → K) → Prop} (h : ∃! u, p u) :
    ∃! b, p (scaledCoords a w b) := by
  obtain ⟨u, hu, huniq⟩ := h
  have hsc : scaledCoords a w (fun i => u i / cofactorWeight a w i) = u := by
    funext i
    exact mul_div_cancel₀ _ (cofactorWeight_ne_zero ha hw i)
  refine ⟨fun i => u i / cofactorWeight a w i, ?_, fun b hb => funext fun i => ?_⟩
  · show p (scaledCoords a w fun i => u i / cofactorWeight a w i)
    rwa [hsc]
  · rw [← huniq _ hb]
    exact (mul_div_cancel_left₀ _ (cofactorWeight_ne_zero ha hw i)).symm

theorem natDegree_cofactor_mul_cofactor_lt (a : Fin n → K) (i j : Fin n) :
    (cofactor a i * cofactor a j).natDegree < 2 * n := by
  have hi := i.2
  refine natDegree_mul_le.trans_lt ?_
  rw [natDegree_cofactor, natDegree_cofactor]
  omega

theorem natDegree_nodePoly_mul_cofactor_lt (a : Fin n → K) (i : Fin n) :
    (nodePoly a * cofactor a i).natDegree < 2 * n := by
  have hi := i.2
  refine natDegree_mul_le.trans_lt ?_
  rw [natDegree_nodePoly, natDegree_cofactor]
  omega

end Field

section Hahn

open scoped _root_.HahnSeries

variable {Γ R : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [Field R]
  {n : ℕ}

omit [AddCommGroup Γ] [IsOrderedAddMonoid Γ] in
/-- Strict ultrametric lower bound for a finite sum of Hahn series; the non-strict form is
`Surreal.ChartIsometry.le_orderTop_finset_sum`. -/
theorem lt_orderTop_sum {ι : Type*} {s : Finset ι} {f : ι → R⟦Γ⟧} {g : WithTop Γ}
    (hg : g ≠ ⊤) (hf : ∀ i ∈ s, g < (f i).orderTop) : g < (∑ i ∈ s, f i).orderTop :=
  Finset.sum_induction f (fun x => g < x.orderTop)
    (fun _ _ hx hy => (lt_min hx hy).trans_le _root_.HahnSeries.min_orderTop_le_orderTop_add)
    (by simpa [lt_top_iff_ne_top] using hg) hf

/-- The ultrametric estimate behind `prony:lem:cofactorbound`: if every entry of `B` has
positive valuation, `(I + B) u = g` and `v(g_i) ≥ κ` for every `i`, then `v(u_i) ≥ κ` for
every `i`. At a coordinate of least valuation, `u_i = g_i - ∑_j B_ij u_j` would otherwise
have valuation strictly larger than its own. -/
theorem le_orderTop_of_one_add_mulVec {B : Matrix (Fin n) (Fin n) R⟦Γ⟧}
    (hB : ∀ i j, 0 < (B i j).orderTop) {u g : Fin n → R⟦Γ⟧} {κ : WithTop Γ}
    (hg : ∀ i, κ ≤ (g i).orderTop) (hu : (1 + B) *ᵥ u = g) (i : Fin n) :
    κ ≤ (u i).orderTop := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨i₀, -, hmin⟩ := Finset.exists_min_image Finset.univ (fun j => (u j).orderTop)
    ⟨i, Finset.mem_univ i⟩
  have hμκ : (u i₀).orderTop < κ := (hmin i (Finset.mem_univ i)).trans_lt hlt
  have hμ : (u i₀).orderTop ≠ ⊤ := (hμκ.trans_le le_top).ne
  have hrow : u i₀ = g i₀ - ∑ j, B i₀ j * u j := by
    have h := congrFun hu i₀
    rw [add_mulVec, one_mulVec, Pi.add_apply] at h
    simp only [mulVec, dotProduct] at h
    rw [← h, add_sub_cancel_right]
  have hsum : (u i₀).orderTop < (∑ j, B i₀ j * u j).orderTop := by
    refine lt_orderTop_sum hμ fun j _ => ?_
    rw [_root_.HahnSeries.orderTop_mul, add_comm]
    calc (u i₀).orderTop = (u i₀).orderTop + 0 := (add_zero _).symm
      _ < (u i₀).orderTop + (B i₀ j).orderTop := WithTop.add_lt_add_left hμ (hB i₀ j)
      _ ≤ (u j).orderTop + (B i₀ j).orderTop := by
        gcongr
        exact hmin j (Finset.mem_univ j)
  have hlt' : (u i₀).orderTop < (u i₀).orderTop := by
    conv_rhs => rw [hrow]
    exact (lt_min (hμκ.trans_le (hg i₀)) hsum).trans_le
      _root_.HahnSeries.min_orderTop_le_orderTop_sub
  exact lt_irrefl _ hlt'

/-- A matrix `I + B` whose perturbation has positive-valuation entries is invertible. -/
theorem det_one_add_ne_zero {B : Matrix (Fin n) (Fin n) R⟦Γ⟧}
    (hB : ∀ i j, 0 < (B i j).orderTop) : (1 + B).det ≠ 0 := by
  intro h0
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  refine hv0 (funext fun i => ?_)
  have h := le_orderTop_of_one_add_mulVec hB (κ := ⊤) (fun _ => by simp) hv i
  simpa using h

/-- The integrality of `(I + B)⁻¹` asserted in the proof of `prony:lem:cofactorbound`: if every
entry of `B` has positive valuation, every entry of `(I + B)⁻¹` has valuation `≥ 0`. Column `j`
of the inverse solves `(I + B) u = e_j`, so `le_orderTop_of_one_add_mulVec` applies with
`κ = 0`. -/
theorem orderTop_inv_one_add_nonneg {B : Matrix (Fin n) (Fin n) R⟦Γ⟧}
    (hB : ∀ i j, 0 < (B i j).orderTop) (i j : Fin n) : 0 ≤ ((1 + B)⁻¹ i j).orderTop := by
  have hdet : IsUnit (1 + B).det := isUnit_iff_ne_zero.mpr (det_one_add_ne_zero hB)
  have hu : (1 + B) *ᵥ ((1 + B)⁻¹ *ᵥ Pi.single j 1) = Pi.single j 1 := by
    rw [mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]
  have hs : ∀ l, (0 : WithTop Γ) ≤ ((Pi.single j 1 : Fin n → R⟦Γ⟧) l).orderTop := by
    intro l
    rw [Pi.single_apply]
    split_ifs <;> simp
  have h := le_orderTop_of_one_add_mulVec hB hs hu i
  rwa [mulVec_single_one] at h

/-- Polynomials with integral coefficients are closed under multiplication. -/
theorem coeff_orderTop_nonneg_mul {f g : R⟦Γ⟧[X]} (hf : ∀ r, 0 ≤ (f.coeff r).orderTop)
    (hg : ∀ r, 0 ≤ (g.coeff r).orderTop) (r : ℕ) : 0 ≤ ((f * g).coeff r).orderTop := by
  rw [coeff_mul]
  refine Surreal.ChartIsometry.le_orderTop_finset_sum _ _ fun x _ => ?_
  rw [_root_.HahnSeries.orderTop_mul]
  exact add_nonneg (hf _) (hg _)

/-- A product of factors `X - a_j` over integral nodes has integral coefficients; compare the
multiset form `Surreal.HahnSeries.coeff_orderTop_nonneg_multiset_prod`. -/
theorem coeff_orderTop_nonneg_prod {a : Fin n → R⟦Γ⟧} (ha0 : ∀ i, 0 ≤ (a i).orderTop)
    (s : Finset (Fin n)) (r : ℕ) : 0 ≤ ((∏ j ∈ s, (X - C (a j))).coeff r).orderTop := by
  revert r
  refine Finset.prod_induction _ (fun f : R⟦Γ⟧[X] => ∀ r, 0 ≤ (f.coeff r).orderTop)
    (fun f g hf hg => coeff_orderTop_nonneg_mul hf hg) (fun r => ?_) (fun j _ r => ?_)
  · rw [coeff_one]
    split_ifs <;> simp
  · rw [coeff_sub, coeff_X, coeff_C]
    refine (le_min ?_ ?_).trans _root_.HahnSeries.min_orderTop_le_orderTop_sub
    · split_ifs <;> simp
    · split_ifs
      · exact ha0 j
      · simp

/-- The moment functional of a perturbation of valuation `≥ κ` on an integral polynomial of
degree `< N` has valuation `≥ κ`. -/
theorem le_orderTop_momentLinear {ε : ℕ → R⟦Γ⟧} {f : R⟦Γ⟧[X]} {N : ℕ} {κ : WithTop Γ}
    (hf : ∀ r, 0 ≤ (f.coeff r).orderTop) (hN : f.natDegree < N)
    (hε : ∀ r < N, κ ≤ (ε r).orderTop) : κ ≤ (momentLinear ε f).orderTop := by
  rw [momentLinear_eq_sum ε f hN]
  refine Surreal.ChartIsometry.le_orderTop_finset_sum _ _ fun r hr => ?_
  rw [_root_.HahnSeries.orderTop_mul]
  calc κ = 0 + κ := (zero_add κ).symm
    _ ≤ _ := add_le_add (hf r) (hε r (Finset.mem_range.mp hr))

/-- The node loss `E_i = v(w_i) + 2 d_i` of `prony:eq:geometry`, where
`d_i = ∑_{j ≠ i} v(a_i - a_j)`. It is defined with `HahnSeries.order`, which is `0` on the zero
series, so it is the source's `E_i` only for nonzero weights and distinct nodes; there it
equals `v(c_i)` by `orderTop_cofactorWeight`. -/
def nodeLoss (a w : Fin n → R⟦Γ⟧) (i : Fin n) : Γ :=
  (w i).order + 2 • ∑ j ∈ univ.erase i, (a i - a j).order

/-- `v(c_i) = E_i`, stated after `prony:eq:cofactor`. -/
theorem orderTop_cofactorWeight {a w : Fin n → R⟦Γ⟧} (ha : Function.Injective a)
    (hw : ∀ i, w i ≠ 0) (i : Fin n) : (cofactorWeight a w i).orderTop = nodeLoss a w i := by
  have hQ : (cofactor a i).eval (a i) = ∏ j ∈ univ.erase i, (a i - a j) := by
    rw [cofactor, eval_prod]
    simp only [eval_sub, eval_X, eval_C]
  have hs : ∑ j ∈ univ.erase i, ((a i - a j).order : WithTop Γ) =
      ∑ j ∈ univ.erase i, (a i - a j).orderTop :=
    Finset.sum_congr rfl fun j hj => _root_.HahnSeries.order_eq_orderTop_of_ne_zero
      (sub_ne_zero.mpr (ha.ne (Finset.ne_of_mem_erase hj).symm))
  rw [cofactorWeight, hQ, _root_.HahnSeries.orderTop_mul, Surreal.HahnSeries.orderTop_pow,
    Surreal.HahnSeries.orderTop_finset_prod, nodeLoss, WithTop.coe_add, WithTop.coe_nsmul,
    WithTop.coe_sum, hs, _root_.HahnSeries.order_eq_orderTop_of_ne_zero (hw i)]

theorem coe_sub_le_of_le_add {κ E : Γ} {x : WithTop Γ} (h : (κ : WithTop Γ) ≤ x + E) :
    ((κ - E : Γ) : WithTop Γ) ≤ x := by
  induction x using WithTop.recTopCoe with
  | top => exact le_top
  | coe x =>
    rw [← WithTop.coe_add, WithTop.coe_le_coe] at h
    exact WithTop.coe_le_coe.mpr (sub_le_iff_le_add.mpr h)

variable {a w : Fin n → R⟦Γ⟧} {ε : ℕ → R⟦Γ⟧} {κ : Γ}

/-- The proof of `prony:lem:cofactorbound`: `Q_i Q_j` is integral of degree `< 2n`, so
`v(B_ij) ≥ κ - E_j`. -/
theorem le_orderTop_corrMatrix (ha0 : ∀ i, 0 ≤ (a i).orderTop) (ha : Function.Injective a)
    (hw : ∀ i, w i ≠ 0) (hε : ∀ r < 2 * n, (κ : WithTop Γ) ≤ (ε r).orderTop) (i j : Fin n) :
    ((κ - nodeLoss a w j : Γ) : WithTop Γ) ≤ (corrMatrix a w ε i j).orderTop := by
  have hL : (κ : WithTop Γ) ≤ (momentLinear ε (cofactor a i * cofactor a j)).orderTop :=
    le_orderTop_momentLinear (coeff_orderTop_nonneg_mul (coeff_orderTop_nonneg_prod ha0 _)
      (coeff_orderTop_nonneg_prod ha0 _)) (natDegree_cofactor_mul_cofactor_lt a i j) hε
  have hmul : corrMatrix a w ε i j * cofactorWeight a w j =
      momentLinear ε (cofactor a i * cofactor a j) := by
    rw [corrMatrix, of_apply, div_mul_cancel₀ _ (cofactorWeight_ne_zero ha hw j)]
  rw [← hmul, _root_.HahnSeries.orderTop_mul, orderTop_cofactorWeight ha hw j] at hL
  exact coe_sub_le_of_le_add hL

/-- The proof of `prony:lem:cofactorbound`: `v(B_ij) ≥ κ - E_j > 0`. -/
theorem orderTop_corrMatrix_pos (ha0 : ∀ i, 0 ≤ (a i).orderTop) (ha : Function.Injective a)
    (hw : ∀ i, w i ≠ 0) (hε : ∀ r < 2 * n, (κ : WithTop Γ) ≤ (ε r).orderTop)
    (hκ : ∀ j, nodeLoss a w j < κ) (i j : Fin n) : 0 < (corrMatrix a w ε i j).orderTop :=
  (WithTop.coe_lt_coe.mpr (sub_pos.mpr (hκ j))).trans_le (le_orderTop_corrMatrix ha0 ha hw hε i j)

/-- The proof of `prony:lem:cofactorbound`: `P Q_i` is integral of degree `< 2n`, so
`v(g_i) ≥ κ`. -/
theorem le_orderTop_corrRhs {κ : WithTop Γ} (ha0 : ∀ i, 0 ≤ (a i).orderTop)
    (hε : ∀ r < 2 * n, κ ≤ (ε r).orderTop) (i : Fin n) : κ ≤ (corrRhs a ε i).orderTop :=
  le_orderTop_momentLinear (coeff_orderTop_nonneg_mul (coeff_orderTop_nonneg_prod ha0 _)
    (coeff_orderTop_nonneg_prod ha0 _)) (natDegree_nodePoly_mul_cofactor_lt a i) hε

/-- `prony:lem:cofactorbound`, for the system `prony:eq:Bsystem` in the unknowns `u`. Let the
nodes be integral and distinct and the weights nonzero. Suppose `v(ε_k) ≥ κ` for `k < 2n`
and `κ > E_j` for every `j`. Then `(I + B) u = -g` has a unique solution, and every solution
satisfies `v(u_i) ≥ κ` and `v(u_i/c_i) ≥ κ - E_i`. -/
theorem cofactorbound_system (ha0 : ∀ i, 0 ≤ (a i).orderTop) (ha : Function.Injective a)
    (hw : ∀ i, w i ≠ 0) (hε : ∀ r < 2 * n, (κ : WithTop Γ) ≤ (ε r).orderTop)
    (hκ : ∀ j, nodeLoss a w j < κ) :
    (∃! u : Fin n → R⟦Γ⟧, (1 + corrMatrix a w ε) *ᵥ u = -corrRhs a ε) ∧
      ∀ u : Fin n → R⟦Γ⟧, (1 + corrMatrix a w ε) *ᵥ u = -corrRhs a ε → ∀ i,
        (κ : WithTop Γ) ≤ (u i).orderTop ∧
          ((κ - nodeLoss a w i : Γ) : WithTop Γ) ≤ (u i / cofactorWeight a w i).orderTop := by
  have hB := orderTop_corrMatrix_pos ha0 ha hw hε hκ
  have hdet : (1 + corrMatrix a w ε).det ≠ 0 := det_one_add_ne_zero hB
  refine ⟨existsUnique_mulVec_eq hdet _, fun u hu i => ?_⟩
  have hui : (κ : WithTop Γ) ≤ (u i).orderTop :=
    le_orderTop_of_one_add_mulVec hB (fun l => by
      rw [Pi.neg_apply, _root_.HahnSeries.orderTop_neg]
      exact le_orderTop_corrRhs ha0 hε l) hu i
  have hdiv : u i / cofactorWeight a w i * cofactorWeight a w i = u i :=
    div_mul_cancel₀ _ (cofactorWeight_ne_zero ha hw i)
  have hval : (u i / cofactorWeight a w i).orderTop + (cofactorWeight a w i).orderTop =
      (u i).orderTop := by
    rw [← _root_.HahnSeries.orderTop_mul, hdiv]
  rw [orderTop_cofactorWeight ha hw i] at hval
  refine ⟨hui, coe_sub_le_of_le_add ?_⟩
  rw [hval]
  exact hui

/-- `prony:lem:cofactorbound` with `prony:eq:bprecision`, in the cofactor coordinates of
`prony:eq:Ph`. Under the hypotheses of `cofactorbound_system`, exactly one `b` makes
`P̂ = P + ∑ b_j Q_j` annihilate every polynomial of degree `< n` for the perturbed functional.
Every such `b` satisfies `v(c_i b_i) ≥ κ` and `v(b_i) ≥ κ - E_i`. -/
theorem cofactorbound (ha0 : ∀ i, 0 ≤ (a i).orderTop) (ha : Function.Injective a)
    (hw : ∀ i, w i ≠ 0) (hε : ∀ r < 2 * n, (κ : WithTop Γ) ≤ (ε r).orderTop)
    (hκ : ∀ j, nodeLoss a w j < κ) :
    (∃! b : Fin n → R⟦Γ⟧, ∀ q : R⟦Γ⟧[X], q.degree < n →
        momentLinear (moment a w + ε) (perturbedPoly a b * q) = 0) ∧
      ∀ b : Fin n → R⟦Γ⟧, (∀ q : R⟦Γ⟧[X], q.degree < n →
          momentLinear (moment a w + ε) (perturbedPoly a b * q) = 0) → ∀ i,
        (κ : WithTop Γ) ≤ (scaledCoords a w b i).orderTop ∧
          ((κ - nodeLoss a w i : Γ) : WithTop Γ) ≤ (b i).orderTop := by
  obtain ⟨hex, hbd⟩ := cofactorbound_system ha0 ha hw hε hκ
  simp only [annihilates_iff_corrSystem ha hw]
  refine ⟨existsUnique_scaledCoords ha hw hex, fun b hb i => ?_⟩
  obtain ⟨h1, h2⟩ := hbd _ hb i
  refine ⟨h1, ?_⟩
  rwa [scaledCoords, mul_div_cancel_left₀ _ (cofactorWeight_ne_zero ha hw i)] at h2

/-- The consequence of `prony:eq:Bsystem` used in the proof of `prony:thm:main`: under the
hypotheses of `prony:lem:cofactorbound` the perturbed Hankel matrix is invertible. -/
theorem det_hankel_perturbed_ne_zero (ha0 : ∀ i, 0 ≤ (a i).orderTop)
    (ha : Function.Injective a) (hw : ∀ i, w i ≠ 0)
    (hε : ∀ r < 2 * n, (κ : WithTop Γ) ≤ (ε r).orderTop) (hκ : ∀ j, nodeLoss a w j < κ) :
    (hankel n (moment a w + ε)).det ≠ 0 :=
  det_hankel_ne_zero_of_det_ne_zero ha hw ε
    (det_one_add_ne_zero (orderTop_corrMatrix_pos ha0 ha hw hε hκ))

/-- Under the hypotheses of `prony:lem:cofactorbound`, the corrected polynomial
`P̂ = P + ∑ b_j Q_j` is the unique monic annihilator of degree `n` of the perturbed
moments. -/
theorem eq_perturbedPoly_of_annihilates (ha0 : ∀ i, 0 ≤ (a i).orderTop)
    (ha : Function.Injective a) (hw : ∀ i, w i ≠ 0)
    (hε : ∀ r < 2 * n, (κ : WithTop Γ) ≤ (ε r).orderTop) (hκ : ∀ j, nodeLoss a w j < κ)
    {b : Fin n → R⟦Γ⟧} (hb : ∀ q : R⟦Γ⟧[X], q.degree < n →
      momentLinear (moment a w + ε) (perturbedPoly a b * q) = 0)
    {F : R⟦Γ⟧[X]} (hF : F.Monic) (hFd : F.natDegree = n)
    (hFann : ∀ r < n, momentLinear (moment a w + ε) (F * X ^ r) = 0) :
    F = perturbedPoly a b := by
  have hH := det_hankel_perturbed_ne_zero ha0 ha hw hε hκ
  have hPann := (annihilates_iff_X_pow _ _).mp hb
  exact monic_annihilator_unique _ hH hF hFd hFann (perturbedPoly_monic a b)
    (natDegree_perturbedPoly a b) hPann

end Hahn

end

end Surreal.PronyBound
