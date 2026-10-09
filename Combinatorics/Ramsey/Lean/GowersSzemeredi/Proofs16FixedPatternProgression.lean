import GowersSzemeredi.Proofs16CommonProgressionDomain
import GowersSzemeredi.Proofs16AffinePatternGeometry

/-! Fixed-pattern geometry on an actual proper progression, preserving
its dense parameter set and all local map domains. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem fixed_patterns_on_proper_progression {N m ell : Nat} [NeZero N]
    (A : Finset (ZMod N × ZMod N)) (V : Finset (ZMod N))
    (E : Fin m → Finset (ZMod N)) (L : Fin m → ZMod N → ZMod N)
    (S : Fin m → Finset (ZMod N)) (J : Fin 4 → Finset (Fin m)) (z w : ZMod N)
    {nu rho R eta width : Real} (hnu : 0 < nu) (hV : nu * N ≤ V.card)
    (hrho : 0 < rho) (hR : 0 ≤ R) (heta : 0 ≤ eta)
    (hwidth0 : 0 ≤ width) (hwidth : Real.exp (-width) ≤ rho)
    (hJ : ∀ i, (J i).card ≤ ell)
    (hS : ∀ i, ((S i).card : Real) ≤ R)
    (hB : ∀ i, IsBHomomorphism (E i) (bohr (S i) rho) (L i))
    (hdom : ∀ y ∈ V, (∀ i ∈ J 0, y + z ∈ E i) ∧ (∀ i ∈ J 2, y + w ∈ E i))
    (hgeom : ∀ y ∈ V, ∀ d ∈ bohr (patternFrequencies L J y z w) eta, (d, y) ∈ A) :
    ∃ (T F : Finset (ZMod N)) (Q : OAI.Erdos3.BohrProgression.CyclicCenteredGAP N)
      (t : ZMod N) (W : Finset (ZMod N)) (psi : Fin m → ZMod N → ZMod N),
      (T.card : Real) ≤ (2 * ell : Nat) * R ∧ F.card ≤ 4 * ell ∧
      Q.rank ≤ T.card + 1 ∧ Q.Proper ∧ Q.carrier ⊆ bohr T (rho / 4) ∧
      W.Nonempty ∧ W ⊆ Q.carrier ∧ nu * (Q.carrier.card : Real) ≤ (W.card : Real) ∧
      nu * Real.exp (-(((T.card : Real) + 1) * width + 10 * ((T.card : Real) + 1)^2)) * N ≤
        (W.card : Real) ∧
      (∀ x₁ ∈ Q.carrier, ∀ x₂ ∈ Q.carrier, ∀ x₃ ∈ Q.carrier, ∀ x₄ ∈ Q.carrier,
        x₁ + x₂ - x₃ - x₄ ∈ bohr T rho) ∧
      (∀ i ∈ J 0 ∪ J 2, FreimanHom 2 (bohr T rho) (psi i) ∧ psi i 0 = 0 ∧
        ∀ x ∈ bohr T rho, ∀ y ∈ bohr T rho, x + y ∈ bohr T rho →
          psi i (x + y) = psi i x + psi i y) ∧
      (∀ x, (varyingPatternFrequencies psi J x).card ≤ 2 * ell) ∧
      ∀ x ∈ W, t + x ∈ V ∧ ∀ d ∈ bohr F (eta / 2),
        d ∈ bohr (varyingPatternFrequencies psi J x) (eta / 2) → (d, t + x) ∈ A := by
  have hVne : V.Nonempty := by
    apply Finset.card_pos.mp
    have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
    exact_mod_cast (mul_pos hnu hN).trans_le hV
  obtain ⟨v, hv⟩ := hVne
  have hE : ∀ i ∈ J 0 ∪ J 2, (E i).Nonempty := by
    intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · exact ⟨v + z, (hdom v hv).1 i hi⟩
    · exact ⟨v + w, (hdom v hv).2 i hi⟩
  obtain ⟨T, Q, t, W, psi, hT, hQr, hQp, hQB, hWne, hWQ, hW, hWglobal, hWV, hfour, hpsi⟩ :=
    selected_common_proper_progression (J 0 ∪ J 2) E L S V hrho hnu hV hwidth0 hwidth hE
      (fun i _ => hS i) (fun i _ => hB i)
  have hconst (K : Finset (Fin m)) (s : ZMod N) (hKI : K ⊆ J 0 ∪ J 2)
      (hD : ∀ x ∈ W, ∀ i ∈ K, t + x + s ∈ E i) :
      ∃ c : Fin m → ZMod N, ∀ i ∈ K, ∀ x ∈ W, L i (t + x + s) = c i + psi i x := by
    have hex (i : Fin m) : ∃ c : ZMod N, i ∈ K → ∀ x ∈ W, L i (t + x + s) = c + psi i x := by
      by_cases hi : i ∈ K
      · obtain ⟨c, hc⟩ := affine_on_progression_cluster (E i) T W Q (L i) (psi i) t s hrho.le
          hQB hWQ hWne (hpsi i (hKI hi)).1 (hpsi i (hKI hi)).2.1
          (hpsi i (hKI hi)).2.2.2 (fun x hx => hD x hx i hi)
        exact ⟨c, fun _ => hc⟩
      · exact ⟨0, fun h => (hi h).elim⟩
    choose c hc using hex
    exact ⟨c, hc⟩
  obtain ⟨c₀, hc₀⟩ := hconst (J 0) z (Finset.subset_union_left)
    (fun x hx => (hdom (t + x) (hWV x hx)).1)
  obtain ⟨c₂, hc₂⟩ := hconst (J 2) w (Finset.subset_union_right)
    (fun x hx => (hdom (t + x) (hWV x hx)).2)
  have hJcard : (J 0 ∪ J 2).card ≤ 2 * ell := by
    have := Finset.card_union_le (J 0) (J 2)
    have := hJ 0
    have := hJ 2
    omega
  refine ⟨T, affinePatternConstants c₀ c₂ L J z w, Q, t, W, psi,
    hT.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hJcard) hR),
    affinePatternConstants_card_le c₀ c₂ L J z w hJ, hQr, hQp, hQB, hWne, hWQ, hW,
    hWglobal, hfour, ?_, varyingPatternFrequencies_card_le psi J hJ, ?_⟩
  · intro i hi
    exact ⟨(hpsi i hi).1, (hpsi i hi).2.1, (hpsi i hi).2.2.1⟩
  · intro x hx
    refine ⟨hWV x hx, fun d hc hd => hgeom (t + x) (hWV x hx) d ?_⟩
    exact pattern_bohr_of_affine L psi J c₀ c₂ x (t + x) z w d heta
      (fun i hi => hc₀ i hi x hx) (fun i hi => hc₂ i hi x hx) hc hd

end LeanProofs.GowersSzemeredi
