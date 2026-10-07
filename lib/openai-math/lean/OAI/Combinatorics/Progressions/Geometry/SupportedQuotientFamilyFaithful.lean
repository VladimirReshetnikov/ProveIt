import OAI.Combinatorics.Progressions.Lattices.SupportedQuotientLatticeFaithful

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {α ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s t : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L)

theorem realQuotientFamily_lattice_detect
    (I : α → LieIdeal ℚ L) (hI : ∀ a, F.layer (t + 1) ≤ (I a).toSubmodule)
    (S : α → Set ι) (hspan : ∀ a, (I a).toSubmodule = Submodule.span ℚ (b '' S a))
    (hcover : ∀ i, ∃ a, i ∉ S a)
    (Γ : Subgroup F.Group) (N : ℕ) (hgrid : bchSubgroupCoordinates b Γ = scaledIntegerGrid N)
    (g : F.realification.Group)
    (hg : ∀ a, F.realQuotientStepHom (I a) (hI a) g ∈
      (Γ.map (F.quotientStepHom (I a) (hI a))).map realificationHom) :
    g ∈ Γ.map realificationHom := by
  classical
  have hcoords (a : α) := F.realQuotientStep_integral_coordinates b (I a) (hI a)
    (S a) (hspan a) Γ N hgrid g (hg a)
  choose z hz using hcoords
  choose a ha using hcover
  apply (mem_realification_integral_lattice_iff b Γ N hgrid g).mpr
  exact ⟨fun i => z (a i) ⟨i, ha i⟩, fun i => hz (a i) ⟨i, ha i⟩⟩

omit [Fintype ι] in
theorem realQuotientFamily_joint_injective
    (I : α → LieIdeal ℚ L) (hI : ∀ a, F.layer (t + 1) ≤ (I a).toSubmodule)
    (S : α → Set ι) (hspan : ∀ a, (I a).toSubmodule = Submodule.span ℚ (b '' S a))
    (hcover : ∀ i, ∃ a, i ∉ S a) :
    Function.Injective (fun g : F.realification.Group => fun a => F.realQuotientStepHom (I a) (hI a) g) := by
  intro g h heq
  apply NilpotentLieBCHGroup.ext
  apply (b.baseChange ℝ).repr.injective
  ext i
  obtain ⟨a, ha⟩ := hcover i
  have hc := congrArg (fun v : (F.quotientLie (I a) (hI a)).realification.Group =>
    ((supportedQuotientBasis b (I a).toSubmodule (S a) (hspan a)).baseChange ℝ).repr
      v.coord ⟨i, ha⟩) (congrFun heq a)
  change ((supportedQuotientBasis b (I a).toSubmodule (S a) (hspan a)).baseChange ℝ).repr
    ((I a).toSubmodule.mkQ.baseChange ℝ g.coord) ⟨i, ha⟩ =
    ((supportedQuotientBasis b (I a).toSubmodule (S a) (hspan a)).baseChange ℝ).repr
      ((I a).toSubmodule.mkQ.baseChange ℝ h.coord) ⟨i, ha⟩ at hc
  simpa only [realSupportedQuotientBasis_repr_mk] using hc

end Erdos3.NilpotentLieFiltration

end

end OAI
