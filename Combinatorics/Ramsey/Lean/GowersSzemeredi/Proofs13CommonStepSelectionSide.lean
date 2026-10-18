import GowersSzemeredi.Proofs13CommonStepSelection

/-! Declarations of `Proofs13CommonStepSelection` that the final route does not use (moved here so
that the route keeps only what it uses). -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace LeanProofs.GowersSzemeredi

theorem lemma_13_6_of_short_difference_rules {N : Nat} [Fact N.Prime]
    (S : Section13Context N) (D : Stage134Data N) (E : Stage135Data N)
    (h135 : IsStage135Data S D E) (m : Nat) (Y : ZMod N → Finset (Pair N))
    (hm : 0 < m) (hsize : m * m ≤ N) (hupper : m + 1 ≤ E.Q.length)
    (hlower : section13Zeta S.alpha / 2 *
      (N : Real) ^ ((1 : Real) / (2 : Real) ^ (13 * section13Q S.alpha)) ≤ m)
    (hY : ∀ h ∈ criticalHeights S D E,
      Y h ⊆ verticalEdgeDomain S.A h ∧
      (2 : Real) ^ (-(43 : Int)) * S.alpha ^ 224 * (N : Real) ^ 2 ≤ (Y h).card)
    (hrule : ∀ h ∈ criticalHeights S D E, ∃ c : ZMod N, ∀ v ∈ Y h, ∀ w ∈ Y h,
      v.1 - w.1 ∈ section10SymmetricMultiples E.Q.step m →
        verticalPhiDifference S.phi h v - verticalPhiDifference S.phi h w =
          c * (v.1 - w.1)) :
    ∃ F : Stage136Data N, IsStage136Data S D E F ∧ F.R.length ≤ E.Q.length  := by
  obtain ⟨F, hF, _, hupper⟩ := lemma_13_6_of_short_difference_rules_with_length
    S D E h135 m Y hm hsize hupper hlower hY hrule
  exact ⟨F, hF, hupper⟩

/-- The linear frequency cover from Stage 13.4 and the simultaneous
smallness in Stage 13.5 place the prescribed step in every required Bohr set. -/
theorem stage136_common_step_mem_bohr {N : Nat} [NeZero N]
    (S : Section13Context N) (theta zeta : Real) (D : Stage134Data N)
    (E : Stage135Data N) (m : Nat) (K : ZMod N → Finset (ZMod N))
    (h134 : IsStage134Data S theta D) (h135 : IsStage135Data S D E)
    (hK : ∀ h ∈ criticalHeights S D E, ∀ r ∈ K h,
      theta * (N : Real) ^ 2 ≤ ‖fourier (verticalEdgeFiberFunction S.A h) r‖)
    (hbudget : (D.P.length : Real) ^ (-((1 : Real) / (2 : Real) ^ (11 * D.q))) ≤
      zeta / m) :
    ∀ h ∈ criticalHeights S D E, E.Q.step ∈ bohr (K h) (zeta / m) :=
  stage136_common_step_mem_bohr_at S theta zeta _ D E m K h134 h135.2.2.2.2.1 hK hbudget

/-- The complete common-step extraction from its Bohr models and numerical
budgets. The conclusion retains `|R| <= |Q|` for the later coefficient step. -/
theorem lemma_13_6_of_bohr_models_with_length {N : Nat} [Fact N.Prime]
    (S : Section13Context N) (theta zeta : Real) (D : Stage134Data N)
    (E : Stage135Data N) (m : Nat) (Y : ZMod N → Finset (Pair N))
    (K : ZMod N → Finset (ZMod N)) (psi : ZMod N → ZMod N → ZMod N)
    (h134 : IsStage134Data S theta D) (h135 : IsStage135Data S D E)
    (hm : 0 < m) (hsize : m * m ≤ N) (hupper : m + 1 ≤ E.Q.length)
    (hlower : section13Zeta S.alpha / 2 *
      (N : Real) ^ ((1 : Real) / (2 : Real) ^ (13 * section13Q S.alpha)) ≤ m)
    (hY : ∀ h ∈ criticalHeights S D E,
      Y h ⊆ verticalEdgeDomain S.A h ∧
      (2 : Real) ^ (-(43 : Int)) * S.alpha ^ 224 * (N : Real) ^ 2 ≤ (Y h).card)
    (hK : ∀ h ∈ criticalHeights S D E, ∀ r ∈ K h,
      theta * (N : Real) ^ 2 ≤ ‖fourier (verticalEdgeFiberFunction S.A h) r‖)
    (hbudget : (D.P.length : Real) ^ (-((1 : Real) / (2 : Real) ^ (11 * D.q))) ≤
      zeta / m)
    (hmodel : ∀ h ∈ criticalHeights S D E,
      HasBohrDifferenceModel (section13EdgeIndexDomain N) (verticalPhiDifference S.phi h)
        (K h) zeta (Y h) (psi h)) :
    ∃ F : Stage136Data N, IsStage136Data S D E F ∧ m ≤ F.R.length ∧ F.R.length ≤ E.Q.length :=
  lemma_13_6_of_bohr_models_at S theta zeta _ D E m Y K psi h134 h135 h135.2.2.2.2.1 hm hsize hupper
    hlower hY hK hbudget hmodel

theorem lemma_13_6_of_bohr_models {N : Nat} [Fact N.Prime]
    (S : Section13Context N) (theta zeta : Real) (D : Stage134Data N)
    (E : Stage135Data N) (m : Nat) (Y : ZMod N → Finset (Pair N))
    (K : ZMod N → Finset (ZMod N)) (psi : ZMod N → ZMod N → ZMod N)
    (h134 : IsStage134Data S theta D) (h135 : IsStage135Data S D E)
    (hm : 0 < m) (hsize : m * m ≤ N) (hupper : m + 1 ≤ E.Q.length)
    (hlower : section13Zeta S.alpha / 2 *
      (N : Real) ^ ((1 : Real) / (2 : Real) ^ (13 * section13Q S.alpha)) ≤ m)
    (hY : ∀ h ∈ criticalHeights S D E,
      Y h ⊆ verticalEdgeDomain S.A h ∧
      (2 : Real) ^ (-(43 : Int)) * S.alpha ^ 224 * (N : Real) ^ 2 ≤ (Y h).card)
    (hK : ∀ h ∈ criticalHeights S D E, ∀ r ∈ K h,
      theta * (N : Real) ^ 2 ≤ ‖fourier (verticalEdgeFiberFunction S.A h) r‖)
    (hbudget : (D.P.length : Real) ^ (-((1 : Real) / (2 : Real) ^ (11 * D.q))) ≤
      zeta / m)
    (hmodel : ∀ h ∈ criticalHeights S D E,
      HasBohrDifferenceModel (section13EdgeIndexDomain N) (verticalPhiDifference S.phi h)
        (K h) zeta (Y h) (psi h)) :
    ∃ F : Stage136Data N, IsStage136Data S D E F ∧ F.R.length ≤ E.Q.length  := by
  obtain ⟨F, hF, _, hupper⟩ := lemma_13_6_of_bohr_models_with_length
    S theta zeta D E m Y K psi h134 h135 hm hsize hupper hlower hY hK hbudget hmodel
  exact ⟨F, hF, hupper⟩

end LeanProofs.GowersSzemeredi
