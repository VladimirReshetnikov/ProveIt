import GowersSzemeredi.Proofs13UniformEdgeModels
import GowersSzemeredi.Proofs13CoefficientExtraction

/-! Assemble Stages 13.6--13.9 from the actual preceding data and explicit
numerical budgets. No row subsets, affine partitions, or coefficient models
are assumed as extra inputs. The common-step geometry needed by the next
square-grid step remains a separate obligation. -/

set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The bilinear extraction chain from the Stage 13.4--13.5 data, retaining
all mass bounds, the upper length bound, and the exact corrected exponents.
The displayed numerical assumptions are the remaining scale obligations. -/
theorem section13_bilinear_extraction_of_budgets {N : Nat} [Fact N.Prime]
    (S : Section13Context N) (D : Stage134Data N) (E : Stage135Data N) (m : Nat)
    (hαsixth : S.alpha ≤ 1 / 6)
    (h134 : IsStage134Data S (section10Lambda (S.alpha ^ 32 / 16)) D)
    (h135 : IsStage135Data S D E)
    (hm : 0 < m) (hsize : m * m ≤ N) (hupper : m + 1 ≤ E.Q.length)
    (hlower : section13Zeta S.alpha / 2 *
      (N : Real) ^ ((1 : Real) / (2 : Real) ^ (13 * section13Q S.alpha)) ≤ m)
    (hbudget : (D.P.length : Real) ^ (-((1 : Real) / (2 : Real) ^ (11 * D.q))) ≤
      section10Zeta (S.alpha ^ 32 / 16) / m)
    (hwidth : (2 : Real) ^ 135 * S.alpha ^ (-(704 : Int)) ≤
      (section13Zeta S.alpha / 2 *
        (N : Real) ^ ((1 : Real) / (2 : Real) ^ (13 * section13Q S.alpha))) ^
          ((2 : Real) ^ (-(100 : Int)) * S.alpha ^ 448)) :
    ∃ F : Stage136Data N, ∃ G : Stage137Data N, ∃ H : Stage138Data N, ∃ J : Stage139Data N,
      IsStage136Data S D E F ∧ F.R.length ≤ E.Q.length ∧
      IsStage137Data S D E F G ∧ IsStage138Data S D E G H ∧ IsStage139Data S E G H J := by
  obtain ⟨F, hF, hFupper⟩ := lemma_13_6_from_initial_stages S D E m hαsixth h134 h135
    hm hsize hupper hlower hbudget
  obtain ⟨G, hG⟩ := lemma_13_7_without_step_span_holds N S D E F hF
  have hα := S.alpha_pos
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hζ : 0 < section13Zeta S.alpha := by unfold section13Zeta; positivity
  have hGwidth : (2 : Real) ^ 135 * S.alpha ^ (-(704 : Int)) ≤ G.S.length := by
    calc
      _ ≤ (section13Zeta S.alpha / 2 *
          (N : Real) ^ ((1 : Real) / (2 : Real) ^ (13 * section13Q S.alpha))) ^
            ((2 : Real) ^ (-(100 : Int)) * S.alpha ^ 448) := hwidth
      _ ≤ (F.R.length : Real) ^ ((2 : Real) ^ (-(100 : Int)) * S.alpha ^ 448) :=
        Real.rpow_le_rpow (by positivity) hF.2.2.2.1 (by positivity)
      _ ≤ G.S.length := hG.1.2.2.2.1
  obtain ⟨H, hH⟩ := lemma_13_8_holds N S D E F G hG hGwidth
  obtain ⟨J, hJ⟩ := lemma_13_9_of_progression_length_bound S D E F G H h135 hF hG hH hFupper
  exact ⟨F, G, H, J, hF, hFupper, hG, hH, hJ⟩

end LeanProofs.GowersSzemeredi
