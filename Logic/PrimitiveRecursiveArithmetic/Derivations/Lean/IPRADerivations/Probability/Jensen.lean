import IPRADerivations.Probability.ProductPower
import IPRADerivations.Probability.SignedParts
import IPRADerivations.Probability.Lotus
import IPRADerivations.Geometry.HypercubeSplit

/-!
# Certified Jensen and conditional Jensen

Packet: `probability/expected_value_ipra_2026-11-16`, Definition `def:jensen-cert`, Theorems
`thm:jensen` and `thm:conditional-jensen`.

For a finite law `w` on `i < M` with `W = ∑ w_i ≥ 1`, an observable `X` with `S = ∑ w_i X_i`
(`μ = S/W`), values `Φ_i = φ(X_i)`, a value `c = φ(μ)` and a rational slope `s = (s⁺ − s⁻)/e` (`e ≥ 1`),
the Jensen certificate `Φ_i ≥ c + s (X_i − μ)` is taken in its cleared form (multiplied by `e W`):
  `e W c + s⁺ W X_i + s⁻ S ≤ e W Φ_i + s⁺ S + s⁻ W X_i`.

* `jensen` (`thm:jensen`): the certificate on every outcome gives `c W ≤ ∑ w_i Φ_i`, i.e.
  `φ(E X) ≤ E φ(X)`. Weighted summation turns both sides into three-term linear combinations of
  `∑ w`, `∑ w X`, `∑ w Φ` (`G3_sum`, from `ProductPower.lin3`); the slope terms cancel because
  `∑ w_i (X_i − μ) = 0`, and the positive factor `e W` is cancelled at the end.
* `conditional_jensen` (`thm:conditional-jensen`): the same on the cell `c(i) = j` of a finite
  partition, i.e. on the cell law `w_i [c(i) = j]` with cell mass `W_j ≥ 1`:
  `φ(E[X | c = j]) ≤ E[φ(X) | c = j]`; zero-mass cells carry no condition.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Probability.Jensen

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Probability.ProductPower (A1 A2 A3 A1_at A2_at A3_at lin3 shift_mul'' shift_zero')
open LeanProofs.IPRA.Probability.Expectation (inst2_mul')
open LeanProofs.IPRA.Probability.SignedParts (sbq inst2_sbq)
open LeanProofs.IPRA.Probability.Lotus (vB inst2_vB)
open LeanProofs.IPRA.Geometry.HypercubeSplit (le_cancel_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

theorem shift_add'' (a b : PTm n) : Syn.shift (a + b) = Syn.shift a + Syn.shift b := by simp [Syn.shift]

/-! ## Three-term linear bodies -/

/-- `K₁ f₁ + K₂ f₂ + K₃ f₃`, with the constants read from `⟨⟨K₁, ⟨K₂, K₃⟩⟩, p⟩`. -/
abbrev GB3 (f₁ f₂ f₃ : PTm 2) : PTm 2 := addBody (A1 f₁) (addBody (A2 f₂) (A3 f₃))

theorem G3_at (f₁ f₂ f₃ : PTm 2) (v K₁ K₂ K₃ p : PTm n) :
    Γ ⊢[PRAAx] inst2 (GB3 f₁ f₂ f₃) v (pairT (pairT K₁ (pairT K₂ K₃)) p) ≐
      K₁ * inst2 f₁ v p + (K₂ * inst2 f₂ v p + K₃ * inst2 f₃ v p) := by
  rw [inst2_addBody, inst2_addBody]
  exact congrAdd (A1_at f₁ _ _ _ _ _) (congrAdd (A2_at f₂ _ _ _ _ _) (A3_at f₃ _ _ _ _ _))

theorem G3_sum (f₁ f₂ f₃ : PTm 2) (N K₁ K₂ K₃ p : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (GB3 f₁ f₂ f₃)) N (pairT (pairT K₁ (pairT K₂ K₃)) p) ≐
      K₁ * ap2 (sumF f₁) N p + (K₂ * ap2 (sumF f₂) N p + K₃ * ap2 (sumF f₃) N p) := by
  refine lin3 f₁ f₂ f₃ _ (.allI (.impI ?_))
  rw [shift_pairT, shift_pairT, shift_pairT]
  exact G3_at f₁ f₂ f₃ _ _ _ _ _

/-! ## Certified Jensen -/

/-- `thm:jensen`: a cleared Jensen certificate at `μ = S/W` on every outcome gives `c W ≤ ∑ w_i Φ_i`. -/
theorem jensen (w X Φ : PTm 2) {M x e c sp sm : PTm n}
    (hW : Γ ⊢[PRAAx] ap2 (sumF w) M x ≐ succ (pred (ap2 (sumF w) M x)))
    (he : Γ ⊢[PRAAx] e ≐ succ (pred e))
    (hc : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift M) ⟶
      le (Syn.shift e * Syn.shift (ap2 (sumF w) M x) * Syn.shift c +
            Syn.shift sp * (Syn.shift (ap2 (sumF w) M x) * inst2 X (var 0) (Syn.shift x)) +
            Syn.shift sm * Syn.shift (ap2 (sumF (w * X)) M x))
        (Syn.shift e * Syn.shift (ap2 (sumF w) M x) * inst2 Φ (var 0) (Syn.shift x) +
            Syn.shift sp * Syn.shift (ap2 (sumF (w * X)) M x) +
            Syn.shift sm * (Syn.shift (ap2 (sumF w) M x) * inst2 X (var 0) (Syn.shift x))))) :
    Γ ⊢[PRAAx] le (c * ap2 (sumF w) M x) (ap2 (sumF (w * Φ)) M x) := by
  let W := ap2 (sumF w) M x
  let S := ap2 (sumF (w * X)) M x
  let F := ap2 (sumF (w * Φ)) M x
  have L := G3_sum (Γ := Γ) w (w * X) w M (e * W * c + sm * S) (sp * W) zero x
  have R := G3_sum (Γ := Γ) w (w * X) (w * Φ) M (sp * S) (sm * W) (e * W) x
  have mono : Γ ⊢[PRAAx] le (ap2 (sumF (GB3 w (w * X) w)) M (pairT (pairT (e * W * c + sm * S) (pairT (sp * W) zero)) x))
      (ap2 (sumF (GB3 w (w * X) (w * Φ))) M (pairT (pairT (sp * S) (pairT (sm * W) (e * W))) x)) := by
    refine sum_le_params _ _ _ _ _ (.allI (.impI ?_))
    simp only [shift_pairT]
    refine le_congr (G3_at _ _ _ _ _ _ _ _).eqSymm (G3_at _ _ _ _ _ _ _ _).eqSymm ?_
    rw [inst2_mul', inst2_mul']
    simp only [shift_add'', shift_mul'', shift_zero']
    have m := le_mul_mono (le_refl (inst2 w (var 0) (Syn.shift x))) (Prf.impE hc.allOpen.wk Prf.hyp0)
    refine le_congr ?_ ?_ m <;> (ipra_ring)
  have m2 := le_congr L R mono
  have m3 : Γ ⊢[PRAAx] le (e * (W * (c * W)) + (sp * W * S + sm * S * W)) (e * (W * F) + (sp * W * S + sm * S * W)) := by
    refine le_congr ?_ ?_ m2 <;> (ipra_ring)
  exact le_cancel_pos hW (le_cancel_pos he (le_of_add_le_add_right m3))

/-! ## Conditional Jensen -/

/-- `thm:conditional-jensen`: on the cell `c(i) = j` of a finite partition (cell law `w_i [c(i) = j]`,
cell mass `W_j = ∑_i w_i [c(i) = j] ≥ 1`, `S_j = ∑_i w_i [c(i) = j] X_i`), a cleared certificate at the
conditional mean `S_j / W_j` gives `c W_j ≤ ∑_i w_i [c(i) = j] Φ_i`, i.e.
`φ(E[X | c = j]) ≤ E[φ(X) | c = j]`. -/
theorem conditional_jensen (w cell X Φ : PTm 2) {M j x e c sp sm : PTm n}
    (hW : Γ ⊢[PRAAx] ap2 (sumF (vB w cell)) M (pairT j x) ≐ succ (pred (ap2 (sumF (vB w cell)) M (pairT j x))))
    (he : Γ ⊢[PRAAx] e ≐ succ (pred e))
    (hc : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift M) ⟶
      le (Syn.shift e * Syn.shift (ap2 (sumF (vB w cell)) M (pairT j x)) * Syn.shift c +
            Syn.shift sp * (Syn.shift (ap2 (sumF (vB w cell)) M (pairT j x)) * inst2 X (var 0) (Syn.shift x)) +
            Syn.shift sm * Syn.shift (ap2 (sumF (vB w cell * sbq X)) M (pairT j x)))
        (Syn.shift e * Syn.shift (ap2 (sumF (vB w cell)) M (pairT j x)) * inst2 Φ (var 0) (Syn.shift x) +
            Syn.shift sp * Syn.shift (ap2 (sumF (vB w cell * sbq X)) M (pairT j x)) +
            Syn.shift sm * (Syn.shift (ap2 (sumF (vB w cell)) M (pairT j x)) * inst2 X (var 0) (Syn.shift x))))) :
    Γ ⊢[PRAAx] le (c * ap2 (sumF (vB w cell)) M (pairT j x)) (ap2 (sumF (vB w cell * sbq Φ)) M (pairT j x)) := by
  refine jensen (vB w cell) (sbq X) (sbq Φ) (sp := sp) (sm := sm) hW he (.allI (.impI ?_))
  rw [shift_pairT, inst2_sbq, inst2_sbq]
  have s : (lt (var 0) (Syn.shift M) :: Γ.map Fm.shift) ⊢[PRAAx] sndT (pairT (Syn.shift j) (Syn.shift x)) ≐ Syn.shift x :=
    snd_pair _ _
  have cX := congrInst2 X (.eqRefl (var 0)) s
  have cΦ := congrInst2 Φ (.eqRefl (var 0)) s
  refine le_congr ?_ ?_ (Prf.impE hc.allOpen.wk Prf.hyp0)
  · exact congrAdd (congrAdd (.eqRefl _) (congrMul (.eqRefl _) (congrMul (.eqRefl _) cX.eqSymm))) (.eqRefl _)
  · exact congrAdd (congrAdd (congrMul (.eqRefl _) cΦ.eqSymm) (.eqRefl _))
      (congrMul (.eqRefl _) (congrMul (.eqRefl _) cX.eqSymm))

end LeanProofs.IPRA.Probability.Jensen
