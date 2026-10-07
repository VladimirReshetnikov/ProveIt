import OAI.Combinatorics.Progressions.Estimates.BooleanCubeModeWitness

namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open MvPolynomial
open scoped BigOperators Classical

variable {α K R : Type*} [Fintype α] [DecidableEq α] [CommRing R]

noncomputable def affineSite (root : K → R) (difference : α → K → R)
    (s : Finset α) : Option K → R
  | none => 1
  | some k => root k + ∑ i ∈ s, difference i k

noncomputable def frameCoordinate (root : K → R) (difference : α → K → R)
    (q : α → MvPolynomial (Option K) R) : Variable α K → MvPolynomial (Option K) R
  | none => X none
  | some (.inl i) => q i
  | some (.inr k) => X (some k) - C (root k) * X none - ∑ i, C (difference i k) * q i

noncomputable def liftCoordinate (root : K → R) (difference : α → K → R) :
    Option K → MvPolynomial (Variable α K) R
  | none => X none
  | some k => C (root k) * X none + ∑ i, C (difference i k) * X (some (.inl i)) + X (some (.inr k))

noncomputable def frameProjection (root : K → R) (difference : α → K → R)
    (q : α → MvPolynomial (Option K) R) :
    MvPolynomial (Variable α K) R →ₐ[R] MvPolynomial (Option K) R :=
  aeval (frameCoordinate root difference q)

noncomputable def frameLift (root : K → R) (difference : α → K → R) :
    MvPolynomial (Option K) R →ₐ[R] MvPolynomial (Variable α K) R :=
  aeval (liftCoordinate root difference)

omit [DecidableEq α] in
theorem frameProjection_lift (root : K → R) (difference : α → K → R)
    (q : α → MvPolynomial (Option K) R) (P : MvPolynomial (Option K) R) :
    frameProjection root difference q (frameLift root difference P) = P := by
  have he : (frameProjection root difference q).comp (frameLift root difference) = AlgHom.id R _ := by
    apply algHom_ext
    intro v
    cases v with
    | none => simp [frameProjection, frameLift, liftCoordinate, frameCoordinate]
    | some k =>
      simp only [AlgHom.comp_apply, frameLift, aeval_X, liftCoordinate, frameProjection,
        map_add, map_sum, map_mul, aeval_C, algebraMap_eq, aeval_X, frameCoordinate, AlgHom.id_apply]
      ring
  exact AlgHom.congr_fun he P

omit [DecidableEq α] in
theorem liftCoordinate_homogeneous (root : K → R) (difference : α → K → R) (v : Option K) :
    (liftCoordinate root difference v).IsHomogeneous 1 := by
  cases v with
  | none => exact isHomogeneous_X R _
  | some k =>
    have hs : (∑ i, C (difference i k) * X (some (.inl i)) :
        MvPolynomial (Variable α K) R).IsHomogeneous 1 :=
      IsHomogeneous.sum _ _ _ (fun i _ => (isHomogeneous_X R _).C_mul (difference i k))
    exact (((isHomogeneous_X R _).C_mul (root k)).add hs).add (isHomogeneous_X R _)

omit [DecidableEq α] in
theorem frameLift_homogeneous (root : K → R) (difference : α → K → R)
    {P : MvPolynomial (Option K) R} {h : ℕ} (hP : P.IsHomogeneous h) :
    (frameLift root difference P).IsHomogeneous h := by
  simpa only [frameLift, Nat.one_mul] using
    hP.aeval (liftCoordinate root difference) (liftCoordinate_homogeneous root difference)

omit [DecidableEq α] in
theorem frameCoordinate_homogeneous (root : K → R) (difference : α → K → R)
    (q : α → MvPolynomial (Option K) R) (hq : ∀ i, (q i).IsHomogeneous 1) (v : Variable α K) :
    (frameCoordinate root difference q v).IsHomogeneous 1 := by
  cases v with
  | none => exact isHomogeneous_X R _
  | some v =>
    cases v with
    | inl i => exact hq i
    | inr k =>
      apply ((isHomogeneous_X R _).sub ((isHomogeneous_X R _).C_mul (root k))).sub
      exact IsHomogeneous.sum _ _ _ (fun i _ => (hq i).C_mul (difference i k))

theorem frameCoordinate_eval (root : K → R) (difference : α → K → R)
    (q : α → MvPolynomial (Option K) R)
    (hq : ∀ i s, eval (affineSite root difference s) (q i) = if i ∈ s then 1 else 0)
    (s : Finset α) (v : Variable α K) :
    eval (affineSite root difference s) (frameCoordinate root difference q v) = site s v := by
  cases v with
  | none => simp [frameCoordinate, affineSite, site]
  | some v =>
    cases v with
    | inl i => exact hq i s
    | inr k =>
      simp only [frameCoordinate, map_sub, map_mul, map_sum, eval_X, eval_C, affineSite,
        hq, mul_one, mul_ite, mul_zero, site]
      simp

theorem frameProjection_eval (root : K → R) (difference : α → K → R)
    (q : α → MvPolynomial (Option K) R)
    (hq : ∀ i s, eval (affineSite root difference s) (q i) = if i ∈ s then 1 else 0)
    (s : Finset α) (P : MvPolynomial (Variable α K) R) :
    eval (affineSite root difference s) (frameProjection root difference q P) = eval (site s) P := by
  have he : (aeval (affineSite root difference s)).comp (frameProjection root difference q) =
      aeval (site (β := K) s) := by
    apply algHom_ext
    intro v
    simpa only [AlgHom.comp_apply, frameProjection, aeval_X, aeval_eq_eval] using
      frameCoordinate_eval root difference q hq s v
  exact AlgHom.congr_fun he P

end Erdos3.BooleanCubeKernel

end

end OAI
