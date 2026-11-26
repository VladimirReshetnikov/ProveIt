import IPRADerivations.Analysis.Inequalities.RationalNonnegativeFloor
import IPRADerivations.Analysis.Euler.PositiveAxis.UnitTime.GaussianEulerUnitCompactTimeBounds

/-!
# Genuine compact-domain guards for original rational floor cuts

True decoded scalar margins are turned into native source predicates for
floor grid nodes and every numerical node in a floor block. All integer
cuts use the original quotient, with no externally supplied floor law.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalUnitFloorBounds

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open RationalNonnegativeFloor (index original_division)
open RationalConvexSecants (nonnegative naturalNumerator)
open RationalSupMetric (denominatorOf)
open RationalArgmin (denominator_positive)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)

def source (q G : PTm n) : Fm PTm n := le one G ⋏
  (le (denominatorOf q) (G*naturalNumerator q) ⋏
    le (G*naturalNumerator q+denominatorOf q) (G*denominatorOf q))

@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (q G : PTm n) :
    (source q G).subst σ = source (Syn.subst σ q) (Syn.subst σ G) := by
  simp [source,naturalNumerator,RationalSupMetric.numeratorOf]

theorem from_representation (q U D G : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hG : Γ ⊢[PRAAx] le one G)
    (h : Γ ⊢[PRAAx] RationalArithmetic.represents q (ZT.ofNat U) D)
    (hLow : Γ ⊢[PRAAx] le D (G*U)) (hUp : Γ ⊢[PRAAx] le (G*U+D) (G*D)) :
    Γ ⊢[PRAAx] source q G := by
  have nonneg : Γ ⊢[PRAAx] nonnegative q := GaussianRationalMetric.comparison_of_cleared _ _ _ _ _ _
    (le_refl one) hD (GaussianRationalSyntheticBounds.natCode_represents zero) h
    (le_of_eq_add (d := U) (by ipra_ring))
  have order := GaussianRationalL1.nonnegative_of_lower _ _
    (GaussianRationalSyntheticBounds.natCode_nonnegative zero) nonneg
  have signed := natEq (eq_add_of_le order)
  have represented := ZT.toZ_eq h
  have same : Γ ⊢[PRAAx] D*naturalNumerator q ≐ denominatorOf q*U := by
    apply deriveNat
    simp only [ZT.toZ_mul,ZT.toZ_ofNat] at represented
    simp only [ZT.toZ] at represented
    unfold naturalNumerator
    ipra_simps
    linear_combination -represented-𝔞 D*signed
  have low : Γ ⊢[PRAAx] le (denominatorOf q) (G*naturalNumerator q) := by
    apply RationalValueBounds.positive_cancel hD
    have s := natEq same
    ipra_le 𝔞 (denominatorOf q)*sl hLow with 𝔞 G*s
  have up : Γ ⊢[PRAAx] le (G*naturalNumerator q+denominatorOf q) (G*denominatorOf q) := by
    apply RationalValueBounds.positive_cancel hD
    have s := natEq same
    ipra_le 𝔞 (denominatorOf q)*sl hUp with -𝔞 G*s
  exact .andI hG (.andI low up)

theorem cut_positive (q G M : PTm n) (hs : Γ ⊢[PRAAx] source q G)
    (hM : Γ ⊢[PRAAx] le (two*G) M) : Γ ⊢[PRAAx] le one (index q M) := by
  have gm : Γ ⊢[PRAAx] le G M := le_trans (le_of_eq_add (d := G) (by ipra_ring)) hM
  refine .orE (zero_or_succ (index q M)) ?_ ?_
  · let Δ := (index q M ≐ zero)::Γ
    have d : Δ ⊢[PRAAx] M*naturalNumerator q ≐ rem (M*naturalNumerator q) (denominatorOf q) :=
      (original_division q M).andE₁.eqTrans ((congrAdd (congrMul (.eqRefl _) Prf.hyp0) (.eqRefl _)).eqTrans (by ipra_ring))
    have bad : Δ ⊢[PRAAx] le (denominatorOf q) (rem (M*naturalNumerator q) (denominatorOf q)) :=
      le_congr (.eqRefl _) d (le_trans hs.wk.andE₂.andE₁
        (mul_le_mul_right (naturalNumerator q) gm.wk))
    exact le_lt_absurd _ bad (original_division q M).andE₂
  · exact le_congr (.eqRefl _) Prf.hyp0.eqSymm (zero_lt_succ _)

theorem lower_margin (q G M : PTm n) (hs : Γ ⊢[PRAAx] source q G)
    (hM : Γ ⊢[PRAAx] le (two*G) M) : Γ ⊢[PRAAx] le M ((two*G)*index q M) := by
  let U := naturalNumerator q
  let D := denominatorOf q
  let I := index q M
  let R := rem (M*U) D
  have hi : Γ ⊢[PRAAx] le one I := cut_positive q G M hs hM
  have small : Γ ⊢[PRAAx] le R D := le_of_lt (original_division q M).andE₂
  have low : Γ ⊢[PRAAx] le D (G*U) := hs.andE₂.andE₁
  have eq := natEq (original_division (Γ := Γ) q M).andE₁
  have cleared : Γ ⊢[PRAAx] le (D*M) (D*((two*G)*I)) := by
    dsimp only [U,D,I,R] at hi small low ⊢
    ipra_le (𝔞 G*𝔞(denominatorOf q))*sl hi + 𝔞 G*sl small + 𝔞 M*sl low with -𝔞 G*eq
  exact RationalValueBounds.positive_cancel (denominator_positive q) cleared

theorem upper_margin (q G M : PTm n) (hs : Γ ⊢[PRAAx] source q G) : Γ ⊢[PRAAx]
    le (G*index q M+M) (G*M) := by
  let U := naturalNumerator q
  let D := denominatorOf q
  let I := index q M
  have up : Γ ⊢[PRAAx] le (G*U+D) (G*D) := hs.andE₂.andE₂
  have eq := natEq (original_division (Γ := Γ) q M).andE₁
  have cleared : Γ ⊢[PRAAx] le (D*(G*I+M)) (D*(G*M)) := by
    dsimp only [U,D,I] at up ⊢
    ipra_le 𝔞 M*sl up + 𝔞 (G*rem (M*naturalNumerator q) (denominatorOf q)) with -𝔞 G*eq
  exact RationalValueBounds.positive_cancel (denominator_positive q) cleared

theorem native_source (q G M : PTm n) (hs : Γ ⊢[PRAAx] source q G)
    (hM : Γ ⊢[PRAAx] le (two*G) M) : Γ ⊢[PRAAx]
    GaussianEulerUnitCompactTimeBounds.source (index q M) M (two*G) := by
  have hI := cut_positive q G M hs hM
  have hG : Γ ⊢[PRAAx] le one (two*G) := le_trans hs.andE₁ (le_of_eq_add (d := G) (by ipra_ring))
  have up := upper_margin (Γ := Γ) q G M hs
  have strict : Γ ⊢[PRAAx] lt (index q M) M := by
    have sum : Γ ⊢[PRAAx] le (G*index q M+one) (G*M) :=
      le_trans (add_le_add₂ (le_refl _) (le_trans hG hM)) up
    refine .orE (lt_or_le (index q M) M) Prf.hyp0 ?_
    have bad : (le M (index q M))::Γ ⊢[PRAAx] lt (G*M) (G*M) := by
      have mult := mul_le_mul_right G (Prf.hyp0 : (le M (index q M))::Γ ⊢[PRAAx] le M (index q M))
      exact le_trans (le_congr (by ipra_ring) (by ipra_ring)
        (add_le_add₂ mult (le_refl one))) sum.wk
    exact lt_irrefl _ _ bad
  have wide : Γ ⊢[PRAAx] le ((two*G)*index q M+M) ((two*G)*M) := by
    ipra_le 2*sl up + 𝔞 M
  exact .andI (.andI hI strict) (.andI hG (.andI (lower_margin q G M hs hM) wide))

theorem block_native_source (q r G M j : PTm n) (hq : Γ ⊢[PRAAx] source q G)
    (hr : Γ ⊢[PRAAx] source r G) (hM : Γ ⊢[PRAAx] le (two*G) M)
    (hLeft : Γ ⊢[PRAAx] le (index q M) j) (hRight : Γ ⊢[PRAAx] le j (index r M)) : Γ ⊢[PRAAx]
    GaussianEulerUnitCompactTimeBounds.source j M (two*G) := by
  have l := native_source q G M hq hM
  have r := native_source r G M hr hM
  exact .andI (.andI (le_trans l.andE₁.andE₁ hLeft) (lt_of_le_of_lt hRight r.andE₁.andE₂))
    (.andI l.andE₂.andE₁ (.andI
      (le_trans l.andE₂.andE₂.andE₁ (le_congr (mul_comm _ _) (mul_comm _ _) (mul_le_mul_right (two*G) hLeft)))
      (le_trans (add_le_add₂ (le_congr (mul_comm _ _) (mul_comm _ _) (mul_le_mul_right (two*G) hRight)) (le_refl M)) r.andE₂.andE₂.andE₂)))

theorem actual_rational_floor_native_unit_compact_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((source (var 0) (var 1) ⋏ le (two*var 1) (var 2)) ⟶
      GaussianEulerUnitCompactTimeBounds.source (index (var 0) (var 2)) (var 2) (two*var 1)) :=
  closeUniv 3 (.impI (native_source _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.RationalUnitFloorBounds
