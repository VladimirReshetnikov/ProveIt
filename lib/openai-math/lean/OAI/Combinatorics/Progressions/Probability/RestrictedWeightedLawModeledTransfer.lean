/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.AveragedModeledPatchTransfer

namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def finiteProbabilityTest {Ω U : Type*} [Fintype U]
    (law : FiniteProbabilityWeights U) (ψ : U → Ω) : (Ω → ℂ) →ₗ[ℂ] ℂ where
  toFun v := law.complexMean (fun u => v (ψ u))
  map_add' v z := by
    simp only [FiniteProbabilityWeights.complexMean, Pi.add_apply, mul_add,
      Finset.sum_add_distrib]
  map_smul' c v := by
    change (∑ u, (law.weight u : ℂ) * (c * v (ψ u))) =
      c * ∑ u, (law.weight u : ℂ) * v (ψ u)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    ring

theorem finiteProbabilityTest_real {Ω U : Type*} [Fintype U]
    (law : FiniteProbabilityWeights U) (ψ : U → Ω) (v : Ω → ℝ) :
    (finiteProbabilityTest law ψ (fun x => (v x : ℂ))).re =
      law.mean (fun u => v (ψ u)) := by
  change (law.complexMean (fun u => (v (ψ u) : ℂ))).re = _
  rw [law.complexMean_ofReal, Complex.ofReal_re]

theorem exists_weightedLaw_averaged_buffered_score
    {H Ω U I : Type*} [Fintype H] [Fintype Ω] [Fintype U] [Fintype I] {m : ℕ}
    (law : FiniteProbabilityWeights H) (productive : Finset H)
    (χ : PatchKernel m) (x : Ω → Fin m → ℝ)
    (T : Ω → (Fin m → ℤ) → ℝ) (G : H → Ω → (Fin m → ℤ) → ℝ)
    (f : Ω → ℝ) (lam : ℝ) (localLaw : H → FiniteProbabilityWeights U)
    (ψ : H → U → Ω) (e : Ω → ℂ) (J : I → Ω → ℂ) (c : I → ℂ)
    (hmodel : (fun u => (bufferedScalarScore χ x T f lam u : ℂ)) =
      (∑ i, c i • J i) + e) {τ ρ : ℝ}
    (hτ : 0 < τ) (hρ : 0 < ρ) (hmass : τ ≤ law.mass productive)
    (hmean : law.mean (fun h =>
      (∑ i, ‖c i‖ * ‖(𝔼 u, (G h u (nearestIntegerLift (x u)) : ℂ) * J i u) -
        (localLaw h).complexMean (fun a => J i (ψ h a))‖) +
      ‖𝔼 u, (G h u (nearestIntegerLift (x u)) : ℂ) * e u‖ +
      ‖(localLaw h).complexMean (fun a => e (ψ h a))‖) ≤ τ * ρ / 8)
    (hscore : ∀ h ∈ productive, ρ ≤ (localLaw h).mean
      (fun a => bufferedScalarScore χ x T f lam (ψ h a))) :
    ∃ h ∈ productive, ρ / 2 ≤ 𝔼 u, (f u - lam) * ∑' b,
      χ.value (fun i => x u i - (b i : ℝ)) * G h u b * T u b := by
  let A := fun h => finiteWeightedTest id
    (fun u => (G h u (nearestIntegerLift (x u)) : ℂ))
  let B := fun h => finiteProbabilityTest (localLaw h) (ψ h)
  have hmean' : law.mean (fun h =>
      (∑ i, ‖c i‖ * ‖A h (J i) - B h (J i)‖) + ‖A h e‖ + ‖B h e‖) ≤
      τ * ρ / 8 := hmean
  have hscore' : ∀ h ∈ productive,
      ρ ≤ (B h (fun u => (bufferedScalarScore χ x T f lam u : ℂ))).re := by
    intro h hh
    exact (hscore h hh).trans_eq (finiteProbabilityTest_real (localLaw h) (ψ h) _).symm
  obtain ⟨h, hh, hs⟩ := exists_productive_averaged_model_transfer law productive A B
    _ e J c hmodel hτ hρ hmass hmean' hscore'
  refine ⟨h, hh, ?_⟩
  simpa only [A, finiteWeightedTest_real, id_eq, bufferedScalarScore_weighted] using hs

open MvPolynomial
open scoped NNReal

theorem exists_weightedLaw_averaged_modeled_discounted_patch
    {H σ Ω U I : Type*} [Fintype H] [Fintype Ω] [Fintype U] [Fintype I]
    {s d E m : ℕ} (law : FiniteProbabilityWeights H) (productive : Finset H)
    (w : Fin d → ℕ) (hw : ∀ j, 1 ≤ w j) (hws : ∀ j, w j ≤ s) (hmono : Monotone w)
    (P : Fin d → MvPolynomial σ ℝ) (hP : ∀ j, P j ∈ weightedSupportLE (fun _ : σ => 1) (w j))
    (p : Fin m → ℕ) (B : WeightedParameterPatch (σ ⊕ Fin m) (Sum.elim (fun _ => 1) p) s E)
    (χ : PatchKernel m) (F : H → (Fin m → ℤ) → (Fin m → ℝ) → ℝ)
    (L C : ℝ≥0) (hC : 1 ≤ C)
    (hF : ∀ h ∈ productive, ∀ β, LipschitzWith L (F h β))
    (hFbound : ∀ h ∈ productive, ∀ β y, F h β y ∈ Set.Icc (0 : ℝ) C)
    (M : Fin m → Fin d → ℤ) (K : ℝ≥0)
    (hM : ∀ i, (∑ j, |(M i j : ℝ)|) ≤ K) (hweight : ∀ i j, M i j ≠ 0 → w j ≤ p i)
    (hinvariant : ∀ h ∈ productive, ∀ c k, F h (recoveredIntegerLift M c k) = F h c)
    (q : ℕ) (hq : 8 ≤ q) (hmesh : 16 * (K : ℝ) ≤ q)
    (t : Ω → σ → ℝ) (f : Ω → ℝ) (G : H → Ω → (Fin m → ℤ) → ℝ) {lam δ ε : ℝ}
    (hf : ∀ u, 0 ≤ f u) (hlam : 0 ≤ lam) (hδ : 0 ≤ δ)
    (hdiscount : (1 + δ) * (1 - ε) ≤ 1 - δ)
    (hlower : ∀ h ∈ productive, ∀ u β, (1 - δ) *
      F h β (fun i => realIntegerMatrix M (fun j => aeval (t u) (P j)) i - (β i : ℝ)) ≤ G h u β)
    (hupper : ∀ h ∈ productive, ∀ u β, G h u β ≤ (1 + δ) *
      F h β (fun i => realIntegerMatrix M (fun j => aeval (t u) (P j)) i - (β i : ℝ)))
    (localLaw : H → FiniteProbabilityWeights U) (ψ : H → U → Ω) (e : Ω → ℂ) (J : I → Ω → ℂ) (c : I → ℂ)
    (hmodel : (fun u => (bufferedScalarScore χ
      (fun u => realIntegerMatrix M (fun j => aeval (t u) (P j)))
      (fun u b => B.value (Sum.elim (t u) (fun i => (b i : ℝ)))) f lam u : ℂ)) =
        (∑ i, c i • J i) + e)
    {τ ρ : ℝ} (hτ : 0 < τ) (hρ : 0 < ρ) (hmass : τ ≤ law.mass productive)
    (hmean : law.mean (fun h =>
      (∑ i, ‖c i‖ * ‖(𝔼 u, (G h u (nearestIntegerLift
        (realIntegerMatrix M (fun j => aeval (t u) (P j)))) : ℂ) * J i u) -
        (localLaw h).complexMean (fun a => J i (ψ h a))‖) +
      ‖𝔼 u, (G h u (nearestIntegerLift
        (realIntegerMatrix M (fun j => aeval (t u) (P j)))) : ℂ) * e u‖ +
      ‖(localLaw h).complexMean (fun a => e (ψ h a))‖) ≤ τ * ρ / 8)
    (hscore : ∀ h ∈ productive, ρ ≤ (localLaw h).mean (fun a => bufferedScalarScore χ
      (fun u => realIntegerMatrix M (fun j => aeval (t u) (P j)))
      (fun u b => B.value (Sum.elim (t u) (fun i => (b i : ℝ)))) f lam (ψ h a))) :
    ∃ Q : PolynomialPatch σ s (d + E),
      Q.kernel.lip ≤ (q : ℝ≥0) * (2 * (q : ℝ≥0) ^ d + 1) +
        (χ.lip + L / C) * K + B.kernel.lip ∧
      (ρ / 2) / ((1 + δ) * (C : ℝ) * (q : ℝ) ^ d) ≤
        𝔼 u, (f u - (1 - ε) * lam) * Q.value (t u) := by
  obtain ⟨h, hh, hs⟩ := exists_weightedLaw_averaged_buffered_score law productive χ
    (fun u => realIntegerMatrix M (fun j => aeval (t u) (P j)))
    (fun u b => B.value (Sum.elim (t u) (fun i => (b i : ℝ)))) G
    f lam localLaw ψ e J c hmodel hτ hρ hmass hmean hscore
  exact exists_discounted_recovered_patch w hw hws hmono P hP p B χ (F h) L C hC
    (hF h hh) (hFbound h hh) M K hM hweight (hinvariant h hh) q hq hmesh
    t f (G h) hf hlam hδ hdiscount (hlower h hh) (hupper h hh) hs

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

theorem exists_restricted_weightedLaw_buffered_score
    {H Ω U I : Type*} [Fintype H] [Fintype Ω] [Fintype U] [Fintype I] {m : ℕ}
    (law : FiniteProbabilityWeights H) (productive : Finset H)
    (χ : PatchKernel m) (x : Ω → Fin m → ℝ)
    (T : Ω → (Fin m → ℤ) → ℝ) (G : H → Ω → (Fin m → ℤ) → ℝ)
    (f : Ω → ℝ) (lam : ℝ) (localLaw : H → FiniteProbabilityWeights U)
    (ψ : H → U → Ω) (e : Ω → ℂ) (J : I → Ω → ℂ) (c : I → ℂ)
    (hmodel : (fun u => (bufferedScalarScore χ x T f lam u : ℂ)) =
      (∑ i, c i • J i) + e) {τ ρ : ℝ}
    (hτ : 0 < τ) (hρ : 0 < ρ) (hmass : τ ≤ law.mass productive)
    (hmean : law.mean (fun h => if h ∈ productive then
      (∑ i, ‖c i‖ * ‖(𝔼 u, (G h u (nearestIntegerLift (x u)) : ℂ) * J i u) -
        (localLaw h).complexMean (fun a => J i (ψ h a))‖) +
      ‖𝔼 u, (G h u (nearestIntegerLift (x u)) : ℂ) * e u‖ +
      ‖(localLaw h).complexMean (fun a => e (ψ h a))‖ else 0) ≤ τ * ρ / 8)
    (hscore : ∀ h ∈ productive, ρ ≤ (localLaw h).mean
      (fun a => bufferedScalarScore χ x T f lam (ψ h a))) :
    ∃ h ∈ productive, ρ / 2 ≤ 𝔼 u, (f u - lam) * ∑' b,
      χ.value (fun i => x u i - (b i : ℝ)) * G h u b * T u b := by
  classical
  let A := fun h => if h ∈ productive then finiteWeightedTest id
    (fun u => (G h u (nearestIntegerLift (x u)) : ℂ)) else 0
  let B := fun h => if h ∈ productive then finiteProbabilityTest (localLaw h) (ψ h) else 0
  have hmean' : law.mean (fun h =>
      (∑ i, ‖c i‖ * ‖A h (J i) - B h (J i)‖) + ‖A h e‖ + ‖B h e‖) ≤
      τ * ρ / 8 := by
    convert hmean using 1
    apply congrArg law.mean
    funext h
    by_cases hh : h ∈ productive
    · simp only [A, B, ite_eq_left hh]
      rfl
    · simp [A, B, hh]
  have hscore' : ∀ h ∈ productive,
      ρ ≤ (B h (fun u => (bufferedScalarScore χ x T f lam u : ℂ))).re := by
    intro h hh
    simpa only [B, ite_eq_left hh] using
      (hscore h hh).trans_eq (finiteProbabilityTest_real (localLaw h) (ψ h) _).symm
  obtain ⟨h, hh, hs⟩ := exists_productive_averaged_model_transfer law productive A B
    _ e J c hmodel hτ hρ hmass hmean' hscore'
  refine ⟨h, hh, ?_⟩
  simpa only [A, ite_eq_left hh, finiteWeightedTest_real, id_eq, bufferedScalarScore_weighted] using hs

open MvPolynomial
open scoped NNReal

theorem exists_restricted_weightedLaw_modeled_discounted_patch
    {H σ Ω U I : Type*} [Fintype H] [Fintype Ω] [Fintype U] [Fintype I]
    {s d E m : ℕ} (law : FiniteProbabilityWeights H) (productive : Finset H)
    (w : Fin d → ℕ) (hw : ∀ j, 1 ≤ w j) (hws : ∀ j, w j ≤ s) (hmono : Monotone w)
    (P : Fin d → MvPolynomial σ ℝ) (hP : ∀ j, P j ∈ weightedSupportLE (fun _ : σ => 1) (w j))
    (p : Fin m → ℕ) (B : WeightedParameterPatch (σ ⊕ Fin m) (Sum.elim (fun _ => 1) p) s E)
    (χ : PatchKernel m) (F : H → (Fin m → ℤ) → (Fin m → ℝ) → ℝ)
    (L C : ℝ≥0) (hC : 1 ≤ C)
    (hF : ∀ h ∈ productive, ∀ β, LipschitzWith L (F h β))
    (hFbound : ∀ h ∈ productive, ∀ β y, F h β y ∈ Set.Icc (0 : ℝ) C)
    (M : Fin m → Fin d → ℤ) (K : ℝ≥0)
    (hM : ∀ i, (∑ j, |(M i j : ℝ)|) ≤ K) (hweight : ∀ i j, M i j ≠ 0 → w j ≤ p i)
    (hinvariant : ∀ h ∈ productive, ∀ c k, F h (recoveredIntegerLift M c k) = F h c)
    (q : ℕ) (hq : 8 ≤ q) (hmesh : 16 * (K : ℝ) ≤ q)
    (t : Ω → σ → ℝ) (f : Ω → ℝ) (G : H → Ω → (Fin m → ℤ) → ℝ) {lam δ ε : ℝ}
    (hf : ∀ u, 0 ≤ f u) (hlam : 0 ≤ lam) (hδ : 0 ≤ δ)
    (hdiscount : (1 + δ) * (1 - ε) ≤ 1 - δ)
    (hlower : ∀ h ∈ productive, ∀ u β, (1 - δ) *
      F h β (fun i => realIntegerMatrix M (fun j => aeval (t u) (P j)) i - (β i : ℝ)) ≤ G h u β)
    (hupper : ∀ h ∈ productive, ∀ u β, G h u β ≤ (1 + δ) *
      F h β (fun i => realIntegerMatrix M (fun j => aeval (t u) (P j)) i - (β i : ℝ)))
    (localLaw : H → FiniteProbabilityWeights U) (ψ : H → U → Ω) (e : Ω → ℂ) (J : I → Ω → ℂ) (c : I → ℂ)
    (hmodel : (fun u => (bufferedScalarScore χ
      (fun u => realIntegerMatrix M (fun j => aeval (t u) (P j)))
      (fun u b => B.value (Sum.elim (t u) (fun i => (b i : ℝ)))) f lam u : ℂ)) =
        (∑ i, c i • J i) + e)
    {τ ρ : ℝ} (hτ : 0 < τ) (hρ : 0 < ρ) (hmass : τ ≤ law.mass productive)
    (hmean : law.mean (fun h => if h ∈ productive then
      (∑ i, ‖c i‖ * ‖(𝔼 u, (G h u (nearestIntegerLift
        (realIntegerMatrix M (fun j => aeval (t u) (P j)))) : ℂ) * J i u) -
        (localLaw h).complexMean (fun a => J i (ψ h a))‖) +
      ‖𝔼 u, (G h u (nearestIntegerLift
        (realIntegerMatrix M (fun j => aeval (t u) (P j)))) : ℂ) * e u‖ +
      ‖(localLaw h).complexMean (fun a => e (ψ h a))‖ else 0) ≤ τ * ρ / 8)
    (hscore : ∀ h ∈ productive, ρ ≤ (localLaw h).mean (fun a => bufferedScalarScore χ
      (fun u => realIntegerMatrix M (fun j => aeval (t u) (P j)))
      (fun u b => B.value (Sum.elim (t u) (fun i => (b i : ℝ)))) f lam (ψ h a))) :
    ∃ Q : PolynomialPatch σ s (d + E),
      Q.kernel.lip ≤ (q : ℝ≥0) * (2 * (q : ℝ≥0) ^ d + 1) +
        (χ.lip + L / C) * K + B.kernel.lip ∧
      (ρ / 2) / ((1 + δ) * (C : ℝ) * (q : ℝ) ^ d) ≤
        𝔼 u, (f u - (1 - ε) * lam) * Q.value (t u) := by
  obtain ⟨h, hh, hs⟩ := exists_restricted_weightedLaw_buffered_score law productive χ
    (fun u => realIntegerMatrix M (fun j => aeval (t u) (P j)))
    (fun u b => B.value (Sum.elim (t u) (fun i => (b i : ℝ)))) G
    f lam localLaw ψ e J c hmodel hτ hρ hmass hmean hscore
  exact exists_discounted_recovered_patch w hw hws hmono P hP p B χ (F h) L C hC
    (hF h hh) (hFbound h hh) M K hM hweight (hinvariant h hh) q hq hmesh
    t f (G h) hf hlam hδ hdiscount (hlower h hh) (hupper h hh) hs

end Erdos3

end

end OAI
