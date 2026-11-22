import IPRADerivations.AnalyticNumberTheory.LogRefinement

/-!
# The elementary logarithm bounds on harmonic intervals (`pnt_ipra_constructive_2026-11-14`)

Packet: `analytic-number-theory/pnt_ipra_constructive_2026-11-14`, `contraction.tex`: "The elementary
inequalities `z/(1+z) ≤ log(1+z) ≤ z` (`z ≥ 0`) imply" the block-length bounds (`con:block-length`), and the
one-sided regularity (`con:decline`) "at rational spatial points `x ≤ y` … is simply `ψ(y)/y ≥ ψ(x)/y`
together with `1 − x/y ≤ log(y/x)`".

The packet's rational logarithm is `λ_M(a/b) = H_{Ma} − H_{Mb}` (`LogRefinement`). With a common
denominator `F`, `H_m = S(m, F)/F` where `S(m, F) = Σ_{i<m} ⌊F/(i+1)⌋` (`Harmonic.S`); put `c₀ = Mb`,
`c₀ + T = Ma`. Cleared of denominators:

* `log_lower` (`1 − b/a ≤ λ_M(a/b)`): if `c₀ + T` divides `F`, then
  `(c₀ + T) S(c₀) + F T ≤ (c₀ + T) S(c₀ + T)`, i.e. `H_{c₀+T} − H_{c₀} ≥ T/(c₀ + T)`;
* `log_upper` (`λ_M(a/b) ≤ a/b − 1`, up to the mesh): for every `F`,
  `(c₀ + 1) S(c₀ + T) ≤ (c₀ + 1) S(c₀) + T F`, i.e. `H_{c₀+T} − H_{c₀} ≤ T/(c₀ + 1)`.

Each tail term `⌊F/(c₀ + i + 1)⌋`, `i < T`, lies between `⌊F/(c₀ + T)⌋` and `⌊F/(c₀ + 1)⌋` (`term_ge`,
`term_le`, by `Harmonic.quo_anti`); only the last denominator needs to divide `F` for the lower bound.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.LogElementary

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (S hB inst2_h quo_anti)
open LeanProofs.IPRA.AnalyticNumberTheory.LogRefinement (const_le_sum quo_mul pos_of_eq shift_eq)
open LeanProofs.IPRA.Foundations.AuxiliaryEnvelope (sum_le_const)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- The tail term: `⌊F/(c₀ + i + 1)⌋`. -/
theorem off_at (i c0 F : PTm n) : Γ ⊢[PRAAx] inst2 (offB hB) i (pairT c0 F) ≐ quo F (succ (c0 + i)) := by
  rw [inst2_offB, inst2_h]
  exact congrAp2 quoF (snd_pair _ _) (congrSucc (congrAdd (fst_pair _ _) (.eqRefl _)))

/-- `F = (c₀ + T) u` and `i < T` give `u ≤ ⌊F/(c₀ + i + 1)⌋`. -/
theorem term_ge {c0 T F u i : PTm n} (hF : Γ ⊢[PRAAx] F ≐ (c0 + T) * u) (hi : Γ ⊢[PRAAx] lt i T) :
    Γ ⊢[PRAAx] le u (quo F (succ (c0 + i))) := by
  have hle : Γ ⊢[PRAAx] le (succ (c0 + i)) (c0 + T) := by ipra_le sl hi
  have a := quo_anti (F := F) (congrSucc (pred_succ (Γ := Γ) (c0 + i)).eqSymm) hle
  have hB : Γ ⊢[PRAAx] c0 + T ≐ succ (pred (c0 + T)) :=
    pos_of_eq ((eq_add_of_le hle).eqTrans (succ_add _ _))
  exact le_congr (quo_mul hB hF) (.eqRefl _) a

/-- `⌊F/(c₀ + i + 1)⌋ ≤ ⌊F/(c₀ + 1)⌋`. -/
theorem term_le (c0 i F : PTm n) : Γ ⊢[PRAAx] le (quo F (succ (c0 + i))) (quo F (succ c0)) :=
  quo_anti (congrSucc (pred_succ (Γ := Γ) c0).eqSymm) (by ipra_le 𝔞 i)

/-- `(c + 1) ⌊F/(c + 1)⌋ ≤ F`. -/
theorem mul_quo_succ (c F : PTm n) : Γ ⊢[PRAAx] le (succ c * quo F (succ c)) F := by
  have e := natEq (Prf.andE₁ (div_mod (Γ := Γ) F c))
  ipra_le 𝔞 (rem F (succ c)) with e

/-- `1 − x/y ≤ log(y/x)`: if `c₀ + T` divides `F`, then `H_{c₀+T} − H_{c₀} ≥ T/(c₀ + T)`, cleared. -/
theorem log_lower (c0 T : PTm n) {F u : PTm n} (hF : Γ ⊢[PRAAx] F ≐ (c0 + T) * u) :
    Γ ⊢[PRAAx] le ((c0 + T) * S c0 F + F * T) ((c0 + T) * S (c0 + T) F) := by
  have es := natEq (sum_split (Γ := Γ) hB c0 T F)
  have eF := natEq hF
  have cl : Γ ⊢[PRAAx] le (T * u) (ap2 (sumF (offB hB)) T (pairT c0 F)) := by
    refine const_le_sum (offB hB) (.allI (.impI ?_))
    rw [show Syn.shift (pairT c0 F) = pairT (Syn.shift c0) (Syn.shift F) by simp [Syn.shift]]
    have hF' : (lt (var 0) (Syn.shift T) :: Γ.map Fm.shift) ⊢[PRAAx]
        Syn.shift F ≐ (Syn.shift c0 + Syn.shift T) * Syn.shift u := by
      have s := shift_eq (N := T) hF
      simpa [Syn.shift] using s
    exact le_congr (.eqRefl _) (off_at _ _ _).eqSymm (term_ge hF' Prf.hyp0)
  ipra_le (𝔞 c0 + 𝔞 T) * sl cl with (𝔞 c0 + 𝔞 T) * es - 𝔞 T * eF

/-- `log(y/x) ≤ y/x − 1` on the harmonic mesh: `H_{c₀+T} − H_{c₀} ≤ T/(c₀ + 1)`, cleared, for every `F`. -/
theorem log_upper (c0 T F : PTm n) :
    Γ ⊢[PRAAx] le (succ c0 * S (c0 + T) F) (succ c0 * S c0 F + T * F) := by
  have es := natEq (sum_split (Γ := Γ) hB c0 T F)
  have cu : Γ ⊢[PRAAx] le (ap2 (sumF (offB hB)) T (pairT c0 F)) (T * quo F (succ c0)) := by
    refine sum_le_const (offB hB) (.allI (.impI ?_))
    rw [show Syn.shift (pairT c0 F) = pairT (Syn.shift c0) (Syn.shift F) by simp [Syn.shift],
      show Syn.shift (quo F (succ c0)) = quo (Syn.shift F) (succ (Syn.shift c0)) by simp [Syn.shift]]
    exact le_congr (off_at _ _ _).eqSymm (.eqRefl _) (term_le _ _ _)
  have mq := mul_quo_succ (Γ := Γ) c0 F
  ipra_le (𝔞 c0 + 1) * sl cu + 𝔞 T * sl mq with (𝔞 c0 + 1) * es

end LeanProofs.IPRA.AnalyticNumberTheory.LogElementary
