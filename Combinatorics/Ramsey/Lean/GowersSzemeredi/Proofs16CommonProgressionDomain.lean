import GowersSzemeredi.Proofs16ProgressionParameterDensity
import GowersSzemeredi.Proofs16SelectedCommonBohr

/-! A common proper progression for the selected maps, together with a
dense translated parameter set and full-domain normalized extensions. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem selected_common_proper_progression {N m : Nat} [NeZero N]
    (I : Finset (Fin m)) (E : Fin m → Finset (ZMod N))
    (L : Fin m → ZMod N → ZMod N) (S : Fin m → Finset (ZMod N))
    (V : Finset (ZMod N)) {rho R nu w : Real}
    (hrho : 0 < rho) (hnu : 0 < nu) (hV : nu * N ≤ V.card)
    (hw : 0 ≤ w) (hwidth : Real.exp (-w) ≤ rho)
    (hE : ∀ i ∈ I, (E i).Nonempty)
    (hS : ∀ i ∈ I, ((S i).card : Real) ≤ R)
    (hB : ∀ i ∈ I, IsBHomomorphism (E i) (bohr (S i) rho) (L i)) :
    ∃ (T : Finset (ZMod N)) (Q : OAI.Erdos3.BohrProgression.CyclicCenteredGAP N)
      (t : ZMod N) (W : Finset (ZMod N)) (psi : Fin m → ZMod N → ZMod N),
      (T.card : Real) ≤ I.card * R ∧ Q.rank ≤ T.card + 1 ∧ Q.Proper ∧
      Q.carrier ⊆ bohr T (rho / 4) ∧ W.Nonempty ∧ W ⊆ Q.carrier ∧
      nu * (Q.carrier.card : Real) ≤ (W.card : Real) ∧
      nu * Real.exp (-(((T.card : Real) + 1) * w + 10 * ((T.card : Real) + 1)^2)) * N ≤
        (W.card : Real) ∧
      (∀ x ∈ W, t + x ∈ V) ∧
      (∀ x₁ ∈ Q.carrier, ∀ x₂ ∈ Q.carrier, ∀ x₃ ∈ Q.carrier, ∀ x₄ ∈ Q.carrier,
        x₁ + x₂ - x₃ - x₄ ∈ bohr T rho) ∧
      ∀ i ∈ I, FreimanHom 2 (bohr T rho) (psi i) ∧ psi i 0 = 0 ∧
        (∀ x ∈ bohr T rho, ∀ y ∈ bohr T rho, x + y ∈ bohr T rho →
          psi i (x + y) = psi i x + psi i y) ∧
        ∀ x ∈ E i, ∀ y ∈ E i, x - y ∈ bohr T rho →
          L i x - L i y = psi i (x - y) := by
  obtain ⟨T, a, C, psi, hT, ha, hCV, hC, hdiff, hpsi⟩ :=
    selected_common_bohr_cluster I E L S V hrho.le hnu hV hE hS hB
  obtain ⟨Q, t, W, hQr, hQp, hQB, hWne, hWQ, hW, hWglobal, hWV, hfour⟩ :=
    dense_parameters_on_proper_progression V T hnu hV hrho hw hwidth
  exact ⟨T, Q, t, W, psi, hT, hQr, hQp, hQB, hWne, hWQ, hW, hWglobal, hWV, hfour, hpsi⟩

/-- Original-domain agreement becomes an affine formula on the dense
part of a translated progression. The translation point itself need not
belong to the original domain. -/
theorem affine_on_progression_cluster {N : Nat} [NeZero N]
    (E T W : Finset (ZMod N)) (Q : OAI.Erdos3.BohrProgression.CyclicCenteredGAP N)
    (f psi : ZMod N → ZMod N) (t s : ZMod N) {rho : Real} (hrho : 0 ≤ rho)
    (hQ : Q.carrier ⊆ bohr T (rho / 4)) (hW : W ⊆ Q.carrier) (hWne : W.Nonempty)
    (hpsi : FreimanHom 2 (bohr T rho) psi) (hzero : psi 0 = 0)
    (hagree : ∀ x ∈ E, ∀ y ∈ E, x - y ∈ bohr T rho → f x - f y = psi (x - y))
    (hdom : ∀ x ∈ W, t + x + s ∈ E) :
    ∃ c : ZMod N, ∀ x ∈ W, f (t + x + s) = c + psi x := by
  obtain ⟨b, hb⟩ := hWne
  refine ⟨f (t + b + s) - psi b, ?_⟩
  intro x hx
  have hxB := hQ (hW hx)
  have hbB := hQ (hW hb)
  have hdiff := bohr_mono_radius T (show rho / 4 + rho / 4 ≤ rho by linarith)
    (bohr_sub_radius T hxB hbB)
  have heq : (t + x + s) - (t + b + s) = x - b := by ring
  have hf := hagree (t + x + s) (hdom x hx) (t + b + s) (hdom b hb)
    (by simpa only [heq] using hdiff)
  rw [heq, freiman_bohr_difference T psi hrho hpsi hzero hxB hbB] at hf
  linear_combination hf

end LeanProofs.GowersSzemeredi
