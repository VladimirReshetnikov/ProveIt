/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Linear.BooleanJetMatrixFactor

namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open MvPolynomial
open scoped BigOperators Classical

theorem normalSpan_high_jet_zero {α β R : Type*} [Fintype α] [DecidableEq α] [CommRing R]
    {h : ℕ} {P : MvPolynomial (Variable α β) R} (hP : P ∈ normalSpan h)
    (s : Finset α) (hs : h < s.card) :
    booleanCoefficient (fun t => eval (site t) P) s = 0 := by
  change ((coefficientLinear s).comp siteEvaluation) P = 0
  induction hP using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨t, ht, rfl⟩ := hP
    change booleanCoefficient (fun u => eval (site u) (normalMonomial h t)) s = 0
    rw [normalMonomial_jet, ite_eq_right]
    intro he
    subst t
    omega
  | zero => exact map_zero _
  | add P Q _ _ hP hQ => rw [map_add, hP, hQ, add_zero]
  | smul a P _ hP => rw [map_smul, hP, smul_zero]

theorem homogeneous_high_jet_zero {α β R : Type*} [Fintype α] [DecidableEq α] [CommRing R]
    {h : ℕ} {P : MvPolynomial (Variable α β) R} (hP : P.IsHomogeneous h)
    (s : Finset α) (hs : h < s.card) :
    booleanCoefficient (fun t => eval (site t) P) s = 0 := by
  obtain ⟨A, hA, B, hB, rfl⟩ := Submodule.mem_sup.mp (homogeneous_mem_reductionSpace hP)
  simp_rw [map_add, vanishingSpan_eval_zero hA, zero_add]
  exact normalSpan_high_jet_zero hB s hs

theorem frameLift_eval_site {α K R : Type*} [Fintype α] [DecidableEq α] [CommRing R]
    (root : K → R) (D : α → K → R) (P : MvPolynomial (Option K) R) (s : Finset α) :
    eval (site s) (frameLift root D P) = eval (affineSite root D s) P := by
  have he : (aeval (site (β := K) s)).comp (frameLift root D) =
      aeval (affineSite root D s) := by
    apply algHom_ext
    intro v
    cases v with
    | none => simp [frameLift, liftCoordinate, site, affineSite]
    | some k =>
      simp [frameLift, liftCoordinate, site, affineSite, Finset.sum_ite_mem]
  exact AlgHom.congr_fun he P

theorem boundedSiteMatrix_high_jet_zero {α K : Type*}
    [Fintype α] [DecidableEq α] [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) (h : ℕ)
    (e : VectorPolynomial.BoundedCoefficientExponent K h) (s : Finset α) (hs : h < s.card) :
    booleanCoefficient (fun t => VectorPolynomial.boundedSiteMatrix h
      (integerAffineCube root D) t e) s = 0 := by
  let d : α → K → ℤ := D
  change booleanCoefficient (fun t => VectorPolynomial.boundedSiteMatrix h
    (integerAffineCube root d) t e) s = 0
  have hp := homogeneous_high_jet_zero
    (frameLift_homogeneous root d (homogenizingMonomial_homogeneous (R := ℤ) h e.val e.property)) s hs
  simp_rw [frameLift_eval_site] at hp
  convert hp using 1
  apply congrArg (fun f => booleanCoefficient f s)
  funext t
  simp [homogenizingMonomial, affineSite, VectorPolynomial.boundedSiteMatrix,
    MvPolynomial.eval_rename, MvPolynomial.eval_monomial, integerAffineCube, Finsupp.prod]

end Erdos3.BooleanCubeKernel

end

end OAI
