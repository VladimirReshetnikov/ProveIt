import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.List.FinRange
import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.RingTheory.Derivation.Lie
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Top-degree mixed differences and symmetric polarization

This file proves `tail:lem:difference` in
`docs/surreal/tail-spans-and-differential-transcendence/article.tex`, both in the operator form
`tail:eq:diffidentity` and in the value form used in the proof of `tail:prop:orbit`.

For a polynomial `P` in the variables `X_i`, `i ∈ σ`, and a vector `u : σ → R`, the difference
operator is `Δ_u P(X) = P(X + u) - P(X)` (`diffOp`, via the translation `translate`), and the
directional derivative `D_u` (`dirDeriv`) is the derivation sending `X_i` to the constant `u_i`.
For finitely many variables `D_u = ∑ᵢ uᵢ ∂ᵢ` (`dirDeriv_eq_sum_pderiv`). The iterated operators
`Δ_{u_1} ⋯ Δ_{u_D}` and `D_{u_1} ⋯ D_{u_D}` are `iterDiff u` and `iterDirDeriv u`, and `P_D` is
`homogeneousComponent D P`.

Proved, for `P` of total degree at most `D` (the source assumes `P ≠ 0` of degree exactly `D`):

* `iterDiff_eq_iterDirDeriv`: `Δ_{u_1} ⋯ Δ_{u_D} P = D_{u_1} ⋯ D_{u_D} P_D`, the first equality
  of `tail:eq:diffidentity`, over any commutative ring and any set of variables;
* `iterDiff_eq_C`, `iterDirDeriv_homogeneousComponent_eq_C`: both sides are constant
  polynomials, so the result does not depend on `X`;
* `eval_iterDiff`, `alternatingSum_eq_coeff_iterDirDeriv`: the value form
  `∑_{J ⊆ {1, …, D}} (-1)^{D - |J|} P(x + ∑_{j ∈ J} u_j) = D_{u_1} ⋯ D_{u_D} P_D` at every
  base point `x`, again over any commutative ring;
* `polarization P D`, the `D`-linear form `T = (D!)⁻¹ D_{u_1} ⋯ D_{u_D} P_D` over a field, with
  `iterDirDeriv_eq_C_factorial_mul_polarization` (the second equality
  `D_{u_1} ⋯ D_{u_D} P_D = D! T(u_1, …, u_D)`), `iterDiff_eq_factorial_mul_polarization` (the
  whole of `tail:eq:diffidentity`), `alternatingSum_eq_factorial_mul_polarization` (the value
  form with `D! T`), `polarization_comp_perm` (symmetry), `polarization_diagonal`
  (`T(x, …, x) = P_D(x)` for every `x`), and `eq_polarization_of_symmetric` (uniqueness of the
  symmetric polarization, through the polarization formula `alternatingSum_diagonal_eq`);
* `iterDiff_zero`, `iterDirDeriv_zero`: for `D = 0` the (empty) operator products are the
  identity; `polarization_zero`: for `D = 0`, `T = P_0`;
* `mixedDifference_of_charZero`: the statement in the source's setting of characteristic zero;
* `homogeneousComponent_eq_zero_of_polarization_eq_zero`: over an infinite field, `T = 0`
  forces `P_D = 0`, the step used at the end of the proof of `tail:prop:orbit`.

The polarization statements assume only that `D!` is nonzero in the field, which is what the
division by `D!` needs; the source's characteristic-zero hypothesis implies it. The first
equality and the value form need no hypothesis on the ring at all. The proof does not use the
Taylor expansion `Δ_u = ∑ D_u^m / m!` of the source, which needs the division. Instead it shows
that `Δ_u` lowers the total degree by one and acts on the top homogeneous component as `D_u`
(`diffOp_step`), by induction over products of variables.

Nothing in `tail:lem:difference` is pending. The source's polynomial identity
`P_D(X) = T(X, …, X)` is stated only pointwise, as `T(x, …, x) = P_D(x)` for every point `x`
(`polarization_diagonal`); no expansion of `T(X, …, X)` as a polynomial is stated. Over an
infinite field, such as one of characteristic zero, the pointwise identity determines `P_D`
(see `homogeneousComponent_eq_zero_of_polarization_eq_zero`).
-/

namespace Surreal.TailSpan

open MvPolynomial

section Operators

variable {σ R : Type*} [CommRing R]

/-- Translation `P(X) ↦ P(X + u)` of a polynomial by a vector `u`. -/
noncomputable def translate (u : σ → R) : MvPolynomial σ R →ₐ[R] MvPolynomial σ R :=
  aeval fun i => X i + C (u i)

theorem translate_X (u : σ → R) (i : σ) : translate u (X i) = X i + C (u i) :=
  aeval_X _ _

theorem translate_C (u : σ → R) (c : R) : translate u (C c) = C c :=
  (translate u).commutes c

theorem eval_translate (u x : σ → R) (P : MvPolynomial σ R) :
    eval x (translate u P) = eval (x + u) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp, translate_X]

/-- The difference operator `Δ_u P(X) = P(X + u) - P(X)`. -/
noncomputable def diffOp (u : σ → R) : Module.End R (MvPolynomial σ R) :=
  (translate u).toLinearMap - 1

theorem diffOp_apply (u : σ → R) (P : MvPolynomial σ R) :
    diffOp u P = translate u P - P := rfl

/-- The directional derivative `D_u`: the derivation sending `X i` to the constant `u i`. -/
noncomputable def dirDeriv (u : σ → R) : Derivation R (MvPolynomial σ R) (MvPolynomial σ R) :=
  mkDerivation R fun i => C (u i)

theorem dirDeriv_X (u : σ → R) (i : σ) : dirDeriv u (X i) = C (u i) :=
  mkDerivation_X _ _ _

theorem dirDeriv_C (u : σ → R) (c : R) : dirDeriv u (C c) = 0 :=
  derivation_C _ c

/-- `Q` vanishes, or its total degree is at most `m - j`. -/
private def LowDeg (j m : ℕ) (Q : MvPolynomial σ R) : Prop :=
  Q = 0 ∨ Q.totalDegree + j ≤ m

private theorem lowDeg_add {j m : ℕ} {P Q : MvPolynomial σ R} (hP : LowDeg j m P)
    (hQ : LowDeg j m Q) : LowDeg j m (P + Q) := by
  rcases hP with rfl | hP
  · simpa using hQ
  rcases hQ with rfl | hQ
  · rw [add_zero]
    exact Or.inr hP
  refine Or.inr ?_
  have h := totalDegree_add P Q
  have h' := max_le (show P.totalDegree ≤ m - j by omega) (show Q.totalDegree ≤ m - j by omega)
  omega

private theorem lowDeg_mul {j k l a b c : ℕ} {P Q : MvPolynomial σ R} (hP : LowDeg j a P)
    (hQ : LowDeg k b Q) (h : a + b + l ≤ c + j + k) : LowDeg l c (P * Q) := by
  rcases hP with rfl | hP
  · simp [LowDeg]
  rcases hQ with rfl | hQ
  · simp [LowDeg]
  exact Or.inr (by have := totalDegree_mul P Q; omega)

private theorem lowDeg_mono {j j' m m' : ℕ} {P : MvPolynomial σ R} (hP : LowDeg j m P)
    (h : m + j' ≤ m' + j) : LowDeg j' m' P := by
  rcases hP with rfl | hP
  · exact Or.inl rfl
  exact Or.inr (by omega)

private theorem lowDeg_of_isHomogeneous {m : ℕ} {P : MvPolynomial σ R} (hP : P.IsHomogeneous m) :
    LowDeg 0 m P :=
  Or.inr (by simpa using hP.totalDegree_le)

private theorem totalDegree_le_of_lowDeg {m : ℕ} {P : MvPolynomial σ R} (hP : LowDeg 0 m P) :
    P.totalDegree ≤ m := by
  rcases hP with rfl | hP
  · simp
  · simpa using hP

/-- The translate of a homogeneous `A` of degree `a` is `A + D_u A` up to degree `a - 2`,
together with Euler's identity at the point `u`. -/
private def Good (u : σ → R) (A : MvPolynomial σ R) (a : ℕ) : Prop :=
  A.IsHomogeneous a ∧ (dirDeriv u A).IsHomogeneous (a - 1) ∧ LowDeg 1 a (dirDeriv u A) ∧
    LowDeg 2 a (translate u A - A - dirDeriv u A) ∧ eval u (dirDeriv u A) = a * eval u A

private theorem good_zero (u : σ → R) (m : ℕ) : Good u 0 m := by
  refine ⟨isHomogeneous_zero _ _ _, ?_, Or.inl (map_zero _), Or.inl (by simp), by simp⟩
  rw [map_zero]
  exact isHomogeneous_zero _ _ _

private theorem good_C (u : σ → R) (c : R) : Good u (C c) 0 := by
  refine ⟨isHomogeneous_C _ _, ?_, Or.inl (dirDeriv_C u c), Or.inl ?_, ?_⟩
  · rw [dirDeriv_C]
    exact isHomogeneous_zero _ _ _
  · rw [dirDeriv_C, translate_C]
    ring
  · simp

private theorem good_X (u : σ → R) (i : σ) : Good u (X i) 1 := by
  refine ⟨isHomogeneous_X _ _, ?_, Or.inr ?_, Or.inl ?_, ?_⟩
  · rw [dirDeriv_X]
    exact isHomogeneous_C _ _
  · simp [dirDeriv_X]
  · rw [dirDeriv_X, translate_X]
    ring
  · simp [dirDeriv_X]

private theorem good_add {u : σ → R} {A B : MvPolynomial σ R} {a : ℕ} (hA : Good u A a)
    (hB : Good u B a) : Good u (A + B) a := by
  obtain ⟨hA1, hA2, hA3, hA4, hA5⟩ := hA
  obtain ⟨hB1, hB2, hB3, hB4, hB5⟩ := hB
  refine ⟨hA1.add hB1, ?_, ?_, ?_, ?_⟩
  · rw [map_add]
    exact hA2.add hB2
  · rw [map_add]
    exact lowDeg_add hA3 hB3
  · have : translate u (A + B) - (A + B) - dirDeriv u (A + B) =
        (translate u A - A - dirDeriv u A) + (translate u B - B - dirDeriv u B) := by
      rw [map_add, map_add]
      ring
    rw [this]
    exact lowDeg_add hA4 hB4
  · rw [map_add, map_add, map_add, hA5, hB5]
    ring

private theorem isHomogeneous_mul_pred {a b : ℕ} {A B : MvPolynomial σ R}
    (hA : A.IsHomogeneous a) (hB : B.IsHomogeneous (b - 1)) (hB' : LowDeg 1 b B) :
    (A * B).IsHomogeneous (a + b - 1) := by
  rcases hB' with rfl | hB'
  · rw [mul_zero]
    exact isHomogeneous_zero _ _ _
  · have : a + b - 1 = a + (b - 1) := by omega
    rw [this]
    exact hA.mul hB

private theorem good_mul {u : σ → R} {A B : MvPolynomial σ R} {a b : ℕ} (hA : Good u A a)
    (hB : Good u B b) : Good u (A * B) (a + b) := by
  obtain ⟨hA1, hA2, hA3, hA4, hA5⟩ := hA
  obtain ⟨hB1, hB2, hB3, hB4, hB5⟩ := hB
  have hD : dirDeriv u (A * B) = A * dirDeriv u B + B * dirDeriv u A := by
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  have hA0 := lowDeg_of_isHomogeneous hA1
  have hB0 := lowDeg_of_isHomogeneous hB1
  refine ⟨hA1.mul hB1, ?_, ?_, ?_, ?_⟩
  · rw [hD]
    refine (isHomogeneous_mul_pred hA1 hB2 hB3).add ?_
    rw [add_comm a b]
    exact isHomogeneous_mul_pred hB1 hA2 hA3
  · rw [hD]
    exact lowDeg_add (lowDeg_mul hA0 hB3 (by omega)) (lowDeg_mul hB0 hA3 (by omega))
  · have key : translate u (A * B) - A * B - dirDeriv u (A * B) =
        A * (translate u B - B - dirDeriv u B) + dirDeriv u A * dirDeriv u B +
          dirDeriv u A * (translate u B - B - dirDeriv u B) +
          (translate u A - A - dirDeriv u A) * B +
          (translate u A - A - dirDeriv u A) * dirDeriv u B +
          (translate u A - A - dirDeriv u A) * (translate u B - B - dirDeriv u B) := by
      rw [hD, map_mul]
      ring
    rw [key]
    refine lowDeg_add (lowDeg_add (lowDeg_add (lowDeg_add (lowDeg_add ?_ ?_) ?_) ?_) ?_) ?_
    · exact lowDeg_mul hA0 hB4 (by omega)
    · exact lowDeg_mul hA3 hB3 (by omega)
    · exact lowDeg_mul hA3 hB4 (by omega)
    · exact lowDeg_mul hA4 hB0 (by omega)
    · exact lowDeg_mul hA4 hB3 (by omega)
    · exact lowDeg_mul hA4 hB4 (by omega)
  · rw [hD, map_add, map_mul, map_mul, hA5, hB5, map_mul]
    push_cast
    ring

private theorem good_X_pow (u : σ → R) (i : σ) (e : ℕ) : Good u (X i ^ e) e := by
  induction e with
  | zero => simpa using good_C u (1 : R)
  | succ e ih => simpa [pow_succ] using good_mul ih (good_X u i)

private theorem good_monomial (u : σ → R) (s : σ →₀ ℕ) (c : R) :
    Good u (monomial s c) s.degree := by
  induction s using Finsupp.induction with
  | zero => simpa [← C_apply] using good_C u c
  | single_add i e s _ _ ih =>
    rw [monomial_single_add, map_add, Finsupp.degree_single]
    exact good_mul (good_X_pow u i e) ih

private theorem good_of_isHomogeneous (u : σ → R) {m : ℕ} {Q : MvPolynomial σ R}
    (hQ : Q.IsHomogeneous m) : Good u Q m := by
  rw [Q.as_sum]
  refine Finset.sum_induction _ (fun P => Good u P m) (fun _ _ => good_add) (good_zero u m) ?_
  intro s hs
  have hdeg : s.degree = m := by
    by_contra h
    exact (mem_support_iff.mp hs) (hQ.coeff_eq_zero h)
  simpa [hdeg] using good_monomial u s (coeff s Q)

/-- One difference lowers the total degree by one and acts on the top component as `D_u`. -/
theorem diffOp_step (u : σ → R) {n : ℕ} {Q : MvPolynomial σ R} (hQ : Q.totalDegree ≤ n + 1) :
    (diffOp u Q).totalDegree ≤ n ∧
      homogeneousComponent n (diffOp u Q) = dirDeriv u (homogeneousComponent (n + 1) Q) := by
  have piece : ∀ m ≤ n + 1, ∀ A : MvPolynomial σ R, A.IsHomogeneous m →
      LowDeg 0 n (diffOp u A) ∧
        homogeneousComponent n (diffOp u A) = dirDeriv u (homogeneousComponent (n + 1) A) := by
    intro m hm A hA
    obtain ⟨hA1, hA2, hA3, hA4, -⟩ := good_of_isHomogeneous u hA
    have hsplit : diffOp u A = dirDeriv u A + (translate u A - A - dirDeriv u A) := by
      rw [diffOp_apply]
      ring
    refine ⟨?_, ?_⟩
    · rw [hsplit]
      exact lowDeg_add (lowDeg_mono hA3 (by omega)) (lowDeg_mono hA4 (by omega))
    · have hE : homogeneousComponent n (translate u A - A - dirDeriv u A) = 0 := by
        rcases hA4 with h | h
        · rw [h, map_zero]
        · exact homogeneousComponent_eq_zero _ _ (by omega)
      rw [hsplit, map_add, hE, add_zero]
      rcases Nat.lt_or_ge m (n + 1) with hlt | hge
      · have h1 : homogeneousComponent (n + 1) A = 0 :=
          homogeneousComponent_eq_zero _ _ (lt_of_le_of_lt hA1.totalDegree_le hlt)
        rw [h1, map_zero]
        rcases hA3 with h | h
        · rw [h, map_zero]
        · exact homogeneousComponent_eq_zero _ _ (by omega)
      · have hmn : m = n + 1 := by omega
        subst hmn
        rw [homogeneousComponent_eq_self hA1, homogeneousComponent_eq_self (by simpa using hA2)]
  rw [← sum_homogeneousComponent Q]
  simp only [map_sum]
  refine ⟨totalDegree_finsetSum_le fun m hm => totalDegree_le_of_lowDeg
      (piece m (by simp at hm; omega) _ (homogeneousComponent_isHomogeneous m Q)).1, ?_⟩
  exact Finset.sum_congr rfl fun m hm =>
    (piece m (by simp at hm; omega) _ (homogeneousComponent_isHomogeneous m Q)).2

/-- The iterated difference `Δ_{u_0} ⋯ Δ_{u_{D-1}}`. -/
noncomputable def iterDiff {D : ℕ} (u : Fin D → σ → R) : Module.End R (MvPolynomial σ R) :=
  (List.ofFn fun j => diffOp (u j)).prod

/-- The iterated directional derivative `D_{u_0} ⋯ D_{u_{D-1}}`. -/
noncomputable def iterDirDeriv {D : ℕ} (u : Fin D → σ → R) : Module.End R (MvPolynomial σ R) :=
  (List.ofFn fun j => (dirDeriv (u j) : Module.End R (MvPolynomial σ R))).prod

theorem iterDiff_zero (u : Fin 0 → σ → R) : iterDiff u = 1 := by
  simp [iterDiff]

theorem iterDiff_succ {D : ℕ} (u : Fin (D + 1) → σ → R) :
    iterDiff u = diffOp (u 0) * iterDiff fun j => u j.succ := by
  rw [iterDiff, List.ofFn_succ, List.prod_cons]
  rfl

theorem iterDirDeriv_zero (u : Fin 0 → σ → R) : iterDirDeriv u = 1 := by
  simp [iterDirDeriv]

theorem iterDirDeriv_succ {D : ℕ} (u : Fin (D + 1) → σ → R) :
    iterDirDeriv u =
      (dirDeriv (u 0) : Module.End R (MvPolynomial σ R)) * iterDirDeriv fun j => u j.succ := by
  rw [iterDirDeriv, List.ofFn_succ, List.prod_cons]
  rfl

/-- `D` differences lower the total degree by `D` and act on the top component as the
corresponding directional derivatives. -/
theorem iterDiff_aux : ∀ (D : ℕ) (u : Fin D → σ → R) (k : ℕ) (P : MvPolynomial σ R),
    P.totalDegree ≤ k + D → (iterDiff u P).totalDegree ≤ k ∧
      homogeneousComponent k (iterDiff u P) = iterDirDeriv u (homogeneousComponent (k + D) P)
  | 0, u, k, P, hP => by
    rw [iterDiff_zero, iterDirDeriv_zero]
    exact ⟨hP, rfl⟩
  | D + 1, u, k, P, hP => by
    obtain ⟨h1, h2⟩ := iterDiff_aux D (fun j => u j.succ) (k + 1) P (by omega)
    obtain ⟨h3, h4⟩ := diffOp_step (u 0) h1
    rw [iterDiff_succ, iterDirDeriv_succ, Module.End.mul_apply, Module.End.mul_apply]
    refine ⟨h3, ?_⟩
    rw [h4, h2, show k + 1 + D = k + (D + 1) by omega]
    rfl

/-- `tail:lem:difference`, first equality of `tail:eq:diffidentity`, over any commutative
ring: if `P` has total degree at most `D`, then `Δ_{u_1} ⋯ Δ_{u_D} P = D_{u_1} ⋯ D_{u_D} P_D`,
where `P_D` is the homogeneous component of degree `D`. -/
theorem iterDiff_eq_iterDirDeriv {D : ℕ} (u : Fin D → σ → R) {P : MvPolynomial σ R}
    (hP : P.totalDegree ≤ D) : iterDiff u P = iterDirDeriv u (homogeneousComponent D P) := by
  obtain ⟨h1, h2⟩ := iterDiff_aux D u 0 P (by omega)
  rw [zero_add] at h2
  rw [← h2, homogeneousComponent_zero]
  exact totalDegree_eq_zero_iff_eq_C.mp (by omega)

/-- `tail:lem:difference`: `D_{u_1} ⋯ D_{u_D} P_D` is a constant polynomial. -/
theorem iterDirDeriv_homogeneousComponent_eq_C {D : ℕ} (u : Fin D → σ → R)
    (P : MvPolynomial σ R) :
    iterDirDeriv u (homogeneousComponent D P) =
      C (coeff 0 (iterDirDeriv u (homogeneousComponent D P))) := by
  have hH := homogeneousComponent_isHomogeneous D P
  have h := iterDiff_eq_iterDirDeriv u hH.totalDegree_le
  rw [homogeneousComponent_eq_self hH] at h
  rw [← h]
  exact totalDegree_eq_zero_iff_eq_C.mp
    (by
      have := (iterDiff_aux D u 0 (homogeneousComponent D P)
        (by have := hH.totalDegree_le; omega)).1
      omega)

/-- `tail:lem:difference`: the iterated difference is independent of `X`, namely the constant
polynomial with value the constant coefficient of `D_{u_1} ⋯ D_{u_D} P_D`. -/
theorem iterDiff_eq_C {D : ℕ} (u : Fin D → σ → R) {P : MvPolynomial σ R}
    (hP : P.totalDegree ≤ D) :
    iterDiff u P = C (coeff 0 (iterDirDeriv u (homogeneousComponent D P))) := by
  rw [iterDiff_eq_iterDirDeriv u hP]
  exact iterDirDeriv_homogeneousComponent_eq_C u P

private theorem sum_finset_fin_succ {M : Type*} [AddCommMonoid M] {D : ℕ}
    (f : Finset (Fin (D + 1)) → M) :
    ∑ J, f J = ∑ J : Finset (Fin D), f (J.map (Fin.succEmb D)) +
      ∑ J : Finset (Fin D), f (insert 0 (J.map (Fin.succEmb D))) := by
  have huniv : (Finset.univ : Finset (Fin (D + 1))) =
      insert 0 (Finset.univ.map (Fin.succEmb D)) := by
    ext j
    refine Fin.cases ?_ (fun i => ?_) j <;> simp
  have h0 : (0 : Fin (D + 1)) ∉ Finset.univ.map (Fin.succEmb D) := by simp
  have hpow : (Finset.univ.map (Fin.succEmb D)).powerset =
      Finset.univ.image fun J : Finset (Fin D) => J.map (Fin.succEmb D) := by
    ext t
    simp [Finset.subset_map_iff, eq_comm]
  rw [← Finset.powerset_univ (α := Fin (D + 1)), huniv, Finset.sum_powerset_insert h0, hpow,
    Finset.sum_image (Finset.map_injective _).injOn,
    Finset.sum_image (Finset.map_injective _).injOn]

/-- `tail:lem:difference`, value form: `Δ_{u_1} ⋯ Δ_{u_D} P` evaluated at `x` is the
alternating sum of the values of `P` at the points `x + ∑_{j ∈ J} u_j`, `J ⊆ {1, …, D}`. -/
theorem eval_iterDiff : ∀ {D : ℕ} (u : Fin D → σ → R) (x : σ → R) (P : MvPolynomial σ R),
    eval x (iterDiff u P) =
      ∑ J : Finset (Fin D), (-1) ^ (D - J.card) * eval (x + ∑ j ∈ J, u j) P
  | 0, u, x, P => by
    simp [iterDiff_zero, Subsingleton.elim (default : Finset (Fin 0)) ∅]
  | D + 1, u, x, P => by
    rw [iterDiff_succ, Module.End.mul_apply, diffOp_apply, map_sub, eval_translate,
      eval_iterDiff (fun j => u j.succ) (x + u 0) P, eval_iterDiff (fun j => u j.succ) x P,
      sum_finset_fin_succ, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun J _ => ?_
    have hJ : J.card ≤ D := by simpa using Finset.card_le_univ J
    have h0 : (0 : Fin (D + 1)) ∉ J.map (Fin.succEmb D) := by simp
    rw [Finset.card_insert_of_notMem h0, Finset.sum_insert h0, Finset.card_map, Finset.sum_map,
      show D + 1 - J.card = D - J.card + 1 by omega,
      show D + 1 - (J.card + 1) = D - J.card by omega, pow_succ]
    simp only [Fin.coe_succEmb, add_assoc]
    ring

/-- `tail:lem:difference`, value form over any commutative ring: for `P` of total degree at
most `D`, the alternating sum over the cube spanned by `u_1, …, u_D` at any base point `x` is
the constant `D_{u_1} ⋯ D_{u_D} P_D`. -/
theorem alternatingSum_eq_coeff_iterDirDeriv {D : ℕ} (u : Fin D → σ → R) (x : σ → R)
    {P : MvPolynomial σ R} (hP : P.totalDegree ≤ D) :
    ∑ J : Finset (Fin D), (-1) ^ (D - J.card) * eval (x + ∑ j ∈ J, u j) P =
      coeff 0 (iterDirDeriv u (homogeneousComponent D P)) := by
  rw [← eval_iterDiff, iterDiff_eq_C u hP, eval_C]

/-- `D_u = ∑ᵢ uᵢ ∂ᵢ` in finitely many variables. -/
theorem dirDeriv_eq_sum_pderiv [Fintype σ] (u : σ → R) : dirDeriv u = ∑ i, u i • pderiv i := by
  classical
  refine derivation_ext fun j => ?_
  have hsum : ⇑(∑ i, u i • pderiv i : Derivation R (MvPolynomial σ R) (MvPolynomial σ R)) =
      ∑ i, ⇑(u i • pderiv i : Derivation R (MvPolynomial σ R) (MvPolynomial σ R)) :=
    map_sum Derivation.coeFnAddMonoidHom _ _
  rw [hsum, Finset.sum_apply]
  simp [dirDeriv_X, pderiv_X, Pi.single_apply, smul_eq_C_mul]

theorem dirDeriv_add (u v : σ → R) : dirDeriv (u + v) = dirDeriv u + dirDeriv v :=
  derivation_ext fun i => by simp [dirDeriv_X]

theorem dirDeriv_smul (c : R) (u : σ → R) : dirDeriv (c • u) = c • dirDeriv u :=
  derivation_ext fun i => by simp [dirDeriv_X, smul_eq_C_mul]

/-- The directional derivative `D_u` depends linearly on the direction `u`. -/
noncomputable def dirDerivLinear : (σ → R) →ₗ[R] Module.End R (MvPolynomial σ R) where
  toFun u := dirDeriv u
  map_add' u v := by
    rw [dirDeriv_add]
    rfl
  map_smul' c u := by
    rw [dirDeriv_smul]
    rfl

/-- Directional derivatives commute. -/
theorem dirDeriv_commute (u v : σ → R) :
    Commute (dirDeriv u : Module.End R (MvPolynomial σ R)) (dirDeriv v) := by
  have h : ⁅dirDeriv u, dirDeriv v⁆ = 0 :=
    derivation_ext fun i => by simp [Derivation.commutator_apply, dirDeriv_X]
  refine LinearMap.ext fun Q => ?_
  have hQ := Derivation.congr_fun h Q
  rw [Derivation.commutator_apply, Derivation.zero_apply, sub_eq_zero] at hQ
  exact hQ

/-- The iterated directional derivative is symmetric in the directions. -/
theorem iterDirDeriv_comp_perm {D : ℕ} (u : Fin D → σ → R) (τ : Equiv.Perm (Fin D)) :
    iterDirDeriv (u ∘ τ) = iterDirDeriv u :=
  (τ.ofFn_comp_perm fun j => (dirDeriv (u j) : Module.End R (MvPolynomial σ R))).prod_eq'
    (List.pairwise_ofFn.mpr fun _ _ _ => dirDeriv_commute _ _)

/-- For `Q` homogeneous of degree `m`, `D_x^m Q = m! Q(x)`. -/
theorem pow_dirDeriv_of_isHomogeneous (x : σ → R) :
    ∀ (m : ℕ) {Q : MvPolynomial σ R}, Q.IsHomogeneous m →
      ((dirDeriv x : Module.End R (MvPolynomial σ R)) ^ m) Q = C ((m.factorial : R) * eval x Q)
  | 0, Q, hQ => by
    rw [pow_zero, Module.End.one_apply, Nat.factorial_zero, Nat.cast_one, one_mul]
    have h := totalDegree_eq_zero_iff_eq_C.mp ((totalDegree_zero_iff_isHomogeneous σ).mpr hQ)
    rw [h, eval_C]
  | m + 1, Q, hQ => by
    obtain ⟨-, hD, -, -, hE⟩ := good_of_isHomogeneous x hQ
    have hD' : (dirDeriv x Q).IsHomogeneous m := by simpa using hD
    rw [pow_succ, Module.End.mul_apply]
    change ((dirDeriv x : Module.End R (MvPolynomial σ R)) ^ m) (dirDeriv x Q) = _
    rw [pow_dirDeriv_of_isHomogeneous x m hD', hE, Nat.factorial_succ]
    congr 1
    push_cast
    ring

/-- The polarization formula: for a symmetric `D`-linear form `S`, the alternating sum of the
diagonal values `S(v, …, v)` at the vertices `v = ∑_{j ∈ J} u_j` of the cube is
`D! S(u_1, …, u_D)`. -/
theorem alternatingSum_diagonal_eq {V : Type*} [AddCommGroup V] [Module R V] {D : ℕ}
    (S : MultilinearMap R (fun _ : Fin D => V) R)
    (hS : ∀ (u : Fin D → V) (τ : Equiv.Perm (Fin D)), S (u ∘ τ) = S u) (u : Fin D → V) :
    ∑ J : Finset (Fin D), (-1) ^ (D - J.card) * S (fun _ => ∑ j ∈ J, u j) =
      (D.factorial : R) * S u := by
  classical
  have hexp : ∀ J : Finset (Fin D), S (fun _ => ∑ j ∈ J, u j) =
      ∑ r : Fin D → Fin D, if ∀ k, r k ∈ J then S (u ∘ r) else 0 := by
    intro J
    rw [S.map_sum_finset (fun _ => u) (fun _ => J), ← Finset.sum_filter]
    exact Finset.sum_congr (by ext r; simp [Fintype.mem_piFinset]) fun r _ => rfl
  have hsign : ∀ r : Fin D → Fin D,
      ∑ J : Finset (Fin D), (if ∀ k, r k ∈ J then (-1 : R) ^ (D - J.card) else 0) =
        if Function.Surjective r then 1 else 0 := by
    intro r
    set A : Finset (Fin D) := Finset.univ.image r with hA
    rw [Fintype.sum_bijective compl compl_involutive.bijective _
      (fun J => if J ∈ Aᶜ.powerset then (-1 : R) ^ J.card else 0) ?_]
    · rw [Finset.sum_ite_mem, Finset.univ_inter]
      have hcast : ∑ J ∈ Aᶜ.powerset, (-1 : R) ^ J.card =
          ((∑ J ∈ Aᶜ.powerset, (-1 : ℤ) ^ J.card : ℤ) : R) := by
        push_cast
        rfl
      rw [hcast, Finset.sum_powerset_neg_one_pow_card]
      have hsurj : Aᶜ = ∅ ↔ Function.Surjective r := by
        rw [Finset.compl_eq_empty_iff, Finset.eq_univ_iff_forall]
        simp [hA, Function.Surjective]
      by_cases h : Function.Surjective r
      · simp [hsurj.mpr h, h]
      · rw [if_neg (mt hsurj.mp h), if_neg h, Int.cast_zero]
    · intro J
      have hc : Jᶜ.card = D - J.card := by rw [Finset.card_compl, Fintype.card_fin]
      have hsub : (∀ k, r k ∈ J) ↔ Jᶜ ∈ Aᶜ.powerset := by
        rw [Finset.mem_powerset, Finset.compl_subset_compl]
        simp [hA, Finset.image_subset_iff]
      by_cases h : ∀ k, r k ∈ J
      · rw [if_pos h, if_pos (hsub.mp h), hc]
      · rw [if_neg h, if_neg (mt hsub.mpr h)]
  have hterm : ∀ r : Fin D → Fin D, ∑ J : Finset (Fin D),
      (-1 : R) ^ (D - J.card) * (if ∀ k, r k ∈ J then S (u ∘ r) else 0) =
        if Function.Surjective r then S (u ∘ r) else 0 := by
    intro r
    calc ∑ J : Finset (Fin D), (-1 : R) ^ (D - J.card) * (if ∀ k, r k ∈ J then S (u ∘ r) else 0)
        = (∑ J : Finset (Fin D), (if ∀ k, r k ∈ J then (-1 : R) ^ (D - J.card) else 0)) *
            S (u ∘ r) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun J _ => ?_
          split_ifs <;> simp
      _ = _ := by
          rw [hsign r]
          split_ifs <;> simp
  simp_rw [hexp, Finset.mul_sum]
  rw [Finset.sum_comm, Finset.sum_congr rfl fun r _ => hterm r, ← Finset.sum_filter]
  have hperm : ∑ r ∈ Finset.univ.filter (fun r : Fin D → Fin D => Function.Surjective r),
      S (u ∘ r) = ∑ τ : Equiv.Perm (Fin D), S (u ∘ τ) := by
    symm
    refine Finset.sum_bij (fun τ _ => ⇑τ) (fun τ _ => by simpa using τ.surjective)
      (fun τ₁ _ τ₂ _ h => Equiv.ext (congrFun h)) (fun r hr => ?_) (fun τ _ => rfl)
    have hr' : Function.Surjective r := by simpa using hr
    exact ⟨Equiv.ofBijective r (Finite.surjective_iff_bijective.mp hr'), Finset.mem_univ _, rfl⟩
  rw [hperm, Finset.sum_congr rfl fun τ _ => hS u τ, Finset.sum_const, Finset.card_univ,
    Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]

end Operators

section Polarization

variable {σ K : Type*} [Field K]

/-- The linear functional `E ↦ (E Q)(0)`, the constant coefficient of `E Q`. -/
private noncomputable def evalConst (Q : MvPolynomial σ K) :
    Module.End K (MvPolynomial σ K) →ₗ[K] K where
  toFun E := coeff 0 (E Q)
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

/-- The polarization `T` of the degree-`D` component `P_D` of `P`, normalized by `D!`:
`T(u_1, …, u_D) = (D!)⁻¹ (D_{u_1} ⋯ D_{u_D} P_D)`. -/
noncomputable def polarization (P : MvPolynomial σ K) (D : ℕ) :
    MultilinearMap K (fun _ : Fin D => σ → K) K :=
  (D.factorial : K)⁻¹ • (evalConst (homogeneousComponent D P)).compMultilinearMap
    ((MultilinearMap.mkPiAlgebraFin K D (Module.End K (MvPolynomial σ K))).compLinearMap
      fun _ => dirDerivLinear)

theorem polarization_apply (P : MvPolynomial σ K) {D : ℕ} (u : Fin D → σ → K) :
    polarization P D u =
      (D.factorial : K)⁻¹ * coeff 0 (iterDirDeriv u (homogeneousComponent D P)) := by
  simp [polarization, evalConst, iterDirDeriv, MultilinearMap.mkPiAlgebraFin_apply,
    dirDerivLinear]

/-- For `D = 0` the polarization is the constant term `P_0`. -/
theorem polarization_zero (P : MvPolynomial σ K) (u : Fin 0 → σ → K) :
    polarization P 0 u = coeff 0 P := by
  rw [polarization_apply, iterDirDeriv_zero, Module.End.one_apply, homogeneousComponent_zero,
    coeff_zero_C, Nat.factorial_zero, Nat.cast_one, inv_one, one_mul]

/-- `tail:lem:difference`, second equality of `tail:eq:diffidentity`: when `D!` is invertible,
`D_{u_1} ⋯ D_{u_D} P_D = D! T(u_1, …, u_D)`, a constant polynomial. -/
theorem iterDirDeriv_eq_C_factorial_mul_polarization {D : ℕ} (hD : (D.factorial : K) ≠ 0)
    (P : MvPolynomial σ K) (u : Fin D → σ → K) :
    iterDirDeriv u (homogeneousComponent D P) = C ((D.factorial : K) * polarization P D u) := by
  rw [polarization_apply, mul_inv_cancel_left₀ hD]
  exact iterDirDeriv_homogeneousComponent_eq_C u P

/-- `tail:lem:difference`, the identity `tail:eq:diffidentity`: for `P` of total degree at most
`D` and `D!` invertible,
`Δ_{u_1} ⋯ Δ_{u_D} P = D_{u_1} ⋯ D_{u_D} P_D = D! T(u_1, …, u_D)`. -/
theorem iterDiff_eq_factorial_mul_polarization {D : ℕ} (hD : (D.factorial : K) ≠ 0)
    (u : Fin D → σ → K) {P : MvPolynomial σ K} (hP : P.totalDegree ≤ D) :
    iterDiff u P = iterDirDeriv u (homogeneousComponent D P) ∧
      iterDirDeriv u (homogeneousComponent D P) = C ((D.factorial : K) * polarization P D u) :=
  ⟨iterDiff_eq_iterDirDeriv u hP, iterDirDeriv_eq_C_factorial_mul_polarization hD P u⟩

/-- `tail:lem:difference`: the polarization `T` is symmetric. -/
theorem polarization_comp_perm (P : MvPolynomial σ K) {D : ℕ} (u : Fin D → σ → K)
    (τ : Equiv.Perm (Fin D)) : polarization P D (u ∘ τ) = polarization P D u := by
  rw [polarization_apply, polarization_apply, iterDirDeriv_comp_perm]

/-- `tail:lem:difference`: the polarization restricts to `P_D` on the diagonal,
`T(x, …, x) = P_D(x)`. -/
theorem polarization_diagonal {D : ℕ} (hD : (D.factorial : K) ≠ 0) (P : MvPolynomial σ K)
    (x : σ → K) : polarization P D (fun _ => x) = eval x (homogeneousComponent D P) := by
  have hpow : iterDirDeriv (fun _ : Fin D => x) =
      (dirDeriv x : Module.End K (MvPolynomial σ K)) ^ D := by
    simp only [iterDirDeriv, List.ofFn_const, List.prod_replicate]
  rw [polarization_apply, hpow,
    pow_dirDeriv_of_isHomogeneous x D (homogeneousComponent_isHomogeneous D P), coeff_zero_C,
    inv_mul_cancel_left₀ hD]

/-- `tail:lem:difference`: `T` is the unique symmetric `D`-linear form with
`T(x, …, x) = P_D(x)` for all `x`, when `D!` is invertible. -/
theorem eq_polarization_of_symmetric {D : ℕ} (hD : (D.factorial : K) ≠ 0)
    (P : MvPolynomial σ K) (S : MultilinearMap K (fun _ : Fin D => σ → K) K)
    (hS : ∀ (u : Fin D → σ → K) (τ : Equiv.Perm (Fin D)), S (u ∘ τ) = S u)
    (hdiag : ∀ x, S (fun _ => x) = eval x (homogeneousComponent D P)) :
    S = polarization P D := by
  ext u
  apply mul_left_cancel₀ hD
  rw [← alternatingSum_diagonal_eq S hS u,
    ← alternatingSum_diagonal_eq (polarization P D) (polarization_comp_perm P) u]
  simp only [hdiag, polarization_diagonal hD]

/-- `tail:lem:difference`, value form used in `tail:prop:orbit`: for `P` of total degree at
most `D` and every base point `x`,
`∑_{J ⊆ {1, …, D}} (-1)^{D - |J|} P(x + ∑_{j ∈ J} u_j) = D! T(u_1, …, u_D)`. -/
theorem alternatingSum_eq_factorial_mul_polarization {D : ℕ} (hD : (D.factorial : K) ≠ 0)
    (u : Fin D → σ → K) (x : σ → K) {P : MvPolynomial σ K} (hP : P.totalDegree ≤ D) :
    ∑ J : Finset (Fin D), (-1) ^ (D - J.card) * eval (x + ∑ j ∈ J, u j) P =
      (D.factorial : K) * polarization P D u := by
  rw [alternatingSum_eq_coeff_iterDirDeriv u x hP, polarization_apply, mul_inv_cancel_left₀ hD]

/-- Over an infinite field with `D!` invertible, the polarization vanishes only when `P_D` does;
this is the step `T = 0 ⇒ P_D = 0` of `tail:prop:orbit`. The hypothesis `Infinite K` is
implied by the source's characteristic zero; mathematically `D! ≠ 0` alone would suffice. -/
theorem homogeneousComponent_eq_zero_of_polarization_eq_zero [Infinite K] {D : ℕ}
    (hD : (D.factorial : K) ≠ 0) {P : MvPolynomial σ K} (h : polarization P D = 0) :
    homogeneousComponent D P = 0 :=
  (homogeneousComponent_isHomogeneous D P).eq_zero_of_forall_eval_eq_zero fun x => by
    rw [← polarization_diagonal hD, h, zero_apply]

/-- `tail:lem:difference` in the source's setting, a field of characteristic zero: for `P` of
total degree at most `D`, the identity `tail:eq:diffidentity` holds with the symmetric
polarization `T` of `P_D`, and so does its value form at every base point `x`. -/
theorem mixedDifference_of_charZero [CharZero K] {D : ℕ} (u : Fin D → σ → K)
    {P : MvPolynomial σ K} (hP : P.totalDegree ≤ D) :
    iterDiff u P = iterDirDeriv u (homogeneousComponent D P) ∧
      iterDirDeriv u (homogeneousComponent D P) = C ((D.factorial : K) * polarization P D u) ∧
      ∀ x : σ → K, ∑ J : Finset (Fin D), (-1) ^ (D - J.card) * eval (x + ∑ j ∈ J, u j) P =
        (D.factorial : K) * polarization P D u := by
  have hD : (D.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr D.factorial_ne_zero
  exact ⟨iterDiff_eq_iterDirDeriv u hP, iterDirDeriv_eq_C_factorial_mul_polarization hD P u,
    fun x => alternatingSum_eq_factorial_mul_polarization hD u x hP⟩

end Polarization

end Surreal.TailSpan
