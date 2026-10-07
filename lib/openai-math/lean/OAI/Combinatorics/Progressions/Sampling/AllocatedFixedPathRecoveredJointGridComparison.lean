import OAI.Combinatorics.Progressions.Dynamics.AllocatedFixedPathAnchoredNativeComparison
import OAI.Combinatorics.Progressions.Estimates.RationalInactiveJointComparisonInstances
import OAI.Combinatorics.Progressions.Estimates.RationalOutputAxisReindex
import OAI.Combinatorics.Progressions.Linear.AllocatedFixedPathKernelFrameBounds
import OAI.Combinatorics.Progressions.Sampling.AllocatedRecoveredForecastDecay

namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped Classical
variable {X : Type*} {m : ℕ} {I E : Fin m → Type*} {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (L : ℕ) (hm : 0 < m)
local notation "short" => allocatedShortAxis (I := I) U basis L
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X E short)
local notation "Aux" => (Σ j : Fin m, E j)
local notation "IntAxis" => AllocatedActiveIntegerAxis U basis L

def forecastCongruenceJointAxisEquiv : Out ≃ Aux ⊕ (X ⊕ IntAxis) where
  toFun a := match a with
    | ⟨_, .inl x⟩ => .inr (.inl x.val)
    | ⟨j, .inr (.inl e)⟩ => .inl ⟨j, e⟩
    | ⟨j, .inr (.inr i)⟩ => .inr (.inr ⟨⟨j, i.val⟩, Nat.lt_of_not_ge i.property⟩)
  invFun a := match a with
    | .inl ⟨j, e⟩ => ⟨j, .inr (.inl e)⟩
    | .inr (.inl x) => ⟨⟨0, hm⟩, .inl ⟨x, rfl⟩⟩
    | .inr (.inr a) => ⟨a.val.1, .inr (.inr ⟨a.val.2, Nat.not_le.mpr a.property⟩)⟩
  left_inv a := by
    rcases a with ⟨j, x | e | i⟩
    · rcases j with ⟨j, hj⟩
      rcases x with ⟨x, hx⟩
      change j = 0 at hx
      subst j
      rfl
    · rfl
    · rfl
  right_inv a := by
    rcases a with ⟨j, e⟩ | x | ⟨⟨j, i⟩, ha⟩ <;> rfl

theorem forecastCongruenceJointAxisEquiv_output {R : Type*}
    (u : X → R) (label : ∀ j, Fin (n j) ⊕ E j → R) :
    (fun a => forecastCongruenceOutput short u label
      ((forecastCongruenceJointAxisEquiv (E := E) U basis L hm).symm a)) =
    Sum.elim (fun a : Aux => label a.1 (.inr a.2))
      (Sum.elim u (fun a : IntAxis => label a.val.1 (.inl a.val.2))) := by
  funext a
  rcases a with ⟨j, e⟩ | x | ⟨⟨j, i⟩, ha⟩ <;> rfl

theorem forecastCongruenceJointAxisEquiv_merged_output
    (u : X → ℤ) (ks : AllocatedShortIntegerAxis U basis L → ℤ)
    (ka : IntAxis → ℤ) (deck : ∀ j, E j → ℤ) :
    (fun a => forecastCongruenceOutput short u
      (fun j => Sum.elim (fun i => forecastIntegerAxisMerge U basis L ks ka ⟨j, i⟩) (deck j))
        ((forecastCongruenceJointAxisEquiv (E := E) U basis L hm).symm a)) =
      Sum.elim (fun a : Aux => deck a.1 a.2) (Sum.elim u ka) := by
  rw [forecastCongruenceJointAxisEquiv_output]
  congr 1
  funext a
  cases a with
  | inl x => rfl
  | inr a => exact forecastIntegerAxisMerge_active U basis L ks ka a

theorem forecastCongruenceJointAxisEquiv_merged_output_mod
    (q : ℕ) (u : X → ℤ) (ks : AllocatedShortIntegerAxis U basis L → ℤ)
    (ka : IntAxis → ℤ) (deck : ∀ j, E j → ℤ) :
    (fun a => (forecastCongruenceOutput (R := ℤ) short u
      (fun j => Sum.elim (fun i => forecastIntegerAxisMerge U basis L ks ka ⟨j, i⟩) (deck j))
        ((forecastCongruenceJointAxisEquiv (E := E) U basis L hm).symm a) : ZMod q)) =
      Sum.elim (fun a : Aux => (deck a.1 a.2 : ZMod q))
        (Sum.elim (fun x => (u x : ZMod q)) (fun a => (ka a : ZMod q))) := by
  have h := forecastCongruenceJointAxisEquiv_merged_output (I := I) U basis L hm u ks ka deck
  funext a
  have ha := congrFun h a
  rw [ha]
  rcases a with ⟨j, e⟩ | x | a <;> rfl

variable [Fintype X] [∀ j, Fintype (E j)]

include hm in
theorem forecastCongruenceJointAxis_card :
    Fintype.card Out = Fintype.card Aux +
      (Fintype.card X + Fintype.card IntAxis) := by
  simpa only [Fintype.card_sum] using
    Fintype.card_congr (forecastCongruenceJointAxisEquiv (X := X) (E := E) (I := I) U basis L hm)

include hm in
theorem forecastCongruenceJointAxis_card_le :
    Fintype.card Out ≤ Fintype.card Aux +
      (Fintype.card X + Fintype.card (Σ j : Fin m, Fin (n j))) := by
  rw [forecastCongruenceJointAxis_card U basis L hm]
  exact Nat.add_le_add_left (Nat.add_le_add_left (Fintype.card_subtype_le _) _) _

theorem forecastCongruenceJointAxis_rationalInactiveForecast
    {P Ω Z : Type*} [Fintype P] [Fintype Ω]
    (inactive : FiniteProbabilityWeights P) (active : P → FiniteProbabilityWeights Ω)
    (gridPoint : P → Z) (Y : P → Ω → Out → ℤ)
    (N : ℕ) [NeZero N] (gridVolume : ℝ) (grid : Z)
    (u : X → ℤ) (ks : AllocatedShortIntegerAxis U basis L → ℤ)
    (ka : IntAxis → ℤ) (deck : ∀ j, E j → ℤ) :
    rationalInactiveForecast inactive active gridPoint Y N gridVolume grid
      (fun a => (forecastCongruenceOutput (R := ℤ) short u
        (fun j => Sum.elim (fun i => forecastIntegerAxisMerge U basis L ks ka ⟨j, i⟩)
          (deck j)) a : ZMod N)) =
    rationalInactiveForecast inactive active gridPoint
      (fun i ω a => Y i ω ((forecastCongruenceJointAxisEquiv U basis L hm).symm a))
      N gridVolume grid
      (Sum.elim (fun a : Aux => (deck a.1 a.2 : ZMod N))
        (Sum.elim (fun x => (u x : ZMod N)) (fun a => (ka a : ZMod N)))) := by
  rw [rationalInactiveForecast_axis_reindex
    (forecastCongruenceJointAxisEquiv (X := X) (E := E) (I := I) U basis L hm)]
  rw [forecastCongruenceJointAxisEquiv_merged_output_mod]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped Classical BigOperators
variable {X : Type*} [Fintype X]
variable {m : ℕ} {I E : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
variable {n : Fin m → ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (L : ℕ) (hm : 0 < m)
local notation "short" => allocatedShortAxis (I := I) U basis L
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X E short)
local notation "Aux" => (Σ j : Fin m, E j)
local notation "IntAxis" => AllocatedActiveIntegerAxis U basis L
local notation "Cont" => (Σ j : Fin m, I j)
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)
local notation "Output" => (Σ _a : {a : LayerSamplerAxis I n // ¬short a}, Unit)
local notation "Domain" => (Spatial → ℝ) × (Output → ℝ)
local notation "axis" => forecastCongruenceJointAxisEquiv (X := X) (I := I) (E := E) U basis L hm
local notation "join" => forecastJointCoordinateJoin (X := X) (I := I) U basis L

theorem forecastJoint_rational_reference
    {P Ω Z : Type*} [Fintype P] [Fintype Ω]
    (inactive : FiniteProbabilityWeights P) (active : P → FiniteProbabilityWeights Ω)
    (gridPoint : P → Z) (Y : P → Ω → Out → ℤ)
    (N q : ℕ) [NeZero N] (hq : q ∣ N) (gridVolume : ℝ)
    (density : Domain → ℝ) (hdensity : Measurable density)
    (hnonneg : ∀ y, 0 ≤ density y)
    (test : Z → (Out → ZMod q) → Domain → ℂ) :
    (∑' z, 𝔼 r : (Aux ⊕ (X ⊕ IntAxis)) → ZMod N,
      ((rationalInactiveForecast inactive active gridPoint
        (fun i ω a => Y i ω ((axis).symm a)) N gridVolume z r / gridVolume : ℝ) : ℂ) *
      ∫ p : (Cont → ℝ) × ((X ⊕ IntAxis) → ℝ),
        (density (join p.1 p.2) : ℂ) *
          test z (fun a => ZMod.castHom hq (ZMod q) (r (axis a))) (join p.1 p.2)) =
    ∑' z, 𝔼 r : Out → ZMod N,
      ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z r / gridVolume : ℝ) : ℂ) *
        ∫ y, test z (fun a => ZMod.castHom hq (ZMod q) (r a)) y
          ∂realDensityMeasure volume density := by
  apply tsum_congr
  intro z
  symm
  apply Fintype.expect_equiv (outputAxisReindexAddEquiv axis (ZMod N)).toEquiv
  intro r
  rw [rationalInactiveForecast_axis_reindex axis]
  congr 1
  rw [realDensityMeasure_integral_complex volume density hdensity hnonneg]
  rw [forecastJointCoordinateJoin_integral U basis L]
  apply integral_congr_ae
  filter_upwards [] with p
  congr 2
  funext a
  exact congrArg (ZMod.castHom hq (ZMod q)) (congrArg r ((axis).symm_apply_apply a).symm)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped Classical BigOperators NNReal
variable {X : Type*} [Fintype X]
variable {m : ℕ} {I E : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
variable {n : Fin m → ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (Lsize : ℕ) (hm : 0 < m)
local notation "short" => allocatedShortAxis (I := I) U basis Lsize
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X E short)
local notation "Aux" => (Σ j : Fin m, E j)
local notation "IntAxis" => AllocatedActiveIntegerAxis U basis Lsize
local notation "Joint" => X ⊕ IntAxis
local notation "Cont" => (Σ j : Fin m, I j)
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)
local notation "Output" => (Σ _a : {a : LayerSamplerAxis I n // ¬short a}, Unit)
local notation "Domain" => (Spatial → ℝ) × (Output → ℝ)
local notation "axis" => forecastCongruenceJointAxisEquiv (X := X) (I := I) (E := E) U basis Lsize hm
local notation "join" => forecastJointCoordinateJoin (X := X) (I := I) U basis Lsize

variable {PIndex Ω Z : Type*} [Fintype PIndex] [Fintype Ω]
variable (inactive : FiniteProbabilityWeights PIndex) (active : PIndex → FiniteProbabilityWeights Ω)
variable (gridPoint : PIndex → Z) (Y : PIndex → Ω → Sigma (AllocatedCongruenceRankOutput X E
  (allocatedShortAxis (I := I) U basis Lsize)) → ℤ)
variable (N q : ℕ) [NeZero N] (hq : q ∣ N) (gridVolume : ℝ)
variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis Lsize a}, Unit) → ℝ)) → ℝ)
variable (test : Z → (Sigma (AllocatedCongruenceRankOutput X E
  (allocatedShortAxis (I := I) U basis Lsize)) → ZMod q) →
  (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis Lsize a}, Unit) → ℝ)) → ℂ)
variable (center scale : X ⊕ AllocatedActiveIntegerAxis U basis Lsize → ℝ)

noncomputable def forecastJointOriginalGridMean : ℂ :=
  𝔼 aux : Aux → ZMod N, ∫ c : Cont → ℝ,
    (∑' z, ∑' k : Joint → ℤ,
      (density (join c (fun j => ((k j : ℝ) - center j) / scale j)) : ℂ) *
      ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z
        (fun a => Sum.elim aux (fun j => (k j : ZMod N)) (axis a)) / gridVolume : ℝ) : ℂ) *
      test z (fun a => Sum.elim (zmodPiReduction hq aux)
        (fun j => (k j : ZMod q)) (axis a))
        (join c (fun j => ((k j : ℝ) - center j) / scale j))) /
      ((∏ j, scale j : ℝ) : ℂ)

theorem forecastJointOriginalGridMean_reindexed :
    let g := fun p : (Cont → ℝ) × (Joint → ℝ) => density (join p.1 p.2)
    let φ := fun z (r : (Aux ⊕ Joint) → ZMod q) (p : (Cont → ℝ) × (Joint → ℝ)) =>
      test z (fun a => r (axis a)) (join p.1 p.2)
    let Y' := fun i ω a => Y i ω ((axis).symm a)
    forecastJointOriginalGridMean U basis Lsize hm inactive active gridPoint Y N q hq
      gridVolume density test center scale =
      (𝔼 aux : Aux → ZMod N, ∫ c : Cont → ℝ,
        (∑' z, ∑' k : Joint → ℤ,
          (g (c, fun j => ((k j : ℝ) - center j) / scale j) : ℂ) *
          ((rationalInactiveForecast inactive active gridPoint Y' N gridVolume z
            (Sum.elim aux (fun j => (k j : ZMod N))) / gridVolume : ℝ) : ℂ) *
          φ z (Sum.elim (zmodPiReduction hq aux) (fun j => (k j : ZMod q)))
            (c, fun j => ((k j : ℝ) - center j) / scale j)) /
            ((∏ j, scale j : ℝ) : ℂ)) := by
  intro g φ Y'
  have hraw :
      rationalInactiveForecast inactive active gridPoint Y N gridVolume =
        fun z r => rationalInactiveForecast inactive active gridPoint Y' N gridVolume z
          (fun a => r ((axis).symm a)) := by
    funext z r
    exact rationalInactiveForecast_axis_reindex axis inactive active gridPoint Y N gridVolume z r
  unfold forecastJointOriginalGridMean
  simp only [hraw, g, φ, Equiv.apply_symm_apply]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped Classical BigOperators NNReal
variable {X : Type*} [Fintype X]
variable {m : ℕ} {I E : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
variable {n : Fin m → ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (Lsize : ℕ) (hm : 0 < m)
local notation "short" => allocatedShortAxis (I := I) U basis Lsize
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X E short)
local notation "Aux" => (Σ j : Fin m, E j)
local notation "IntAxis" => AllocatedActiveIntegerAxis U basis Lsize
local notation "Joint" => X ⊕ IntAxis
local notation "Cont" => (Σ j : Fin m, I j)
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)
local notation "Output" => (Σ _a : {a : LayerSamplerAxis I n // ¬short a}, Unit)
local notation "Domain" => (Spatial → ℝ) × (Output → ℝ)
local notation "axis" => forecastCongruenceJointAxisEquiv (X := X) (I := I) (E := E) U basis Lsize hm
local notation "join" => forecastJointCoordinateJoin (X := X) (I := I) U basis Lsize

variable {PIndex Ω Z : Type*} [Fintype PIndex] [Fintype Ω]
variable (inactive : FiniteProbabilityWeights PIndex) (active : PIndex → FiniteProbabilityWeights Ω)
variable (gridPoint : PIndex → Z) (Y : PIndex → Ω → Sigma (AllocatedCongruenceRankOutput X E
  (allocatedShortAxis (I := I) U basis Lsize)) → ℤ)
variable (N q : ℕ) [NeZero N] (hq : q ∣ N) (gridVolume : ℝ)
variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis Lsize a}, Unit) → ℝ)) → ℝ)
variable (test : Z → (Sigma (AllocatedCongruenceRankOutput X E
  (allocatedShortAxis (I := I) U basis Lsize)) → ZMod q) →
  (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis Lsize a}, Unit) → ℝ)) → ℂ)
variable (center scale : X ⊕ AllocatedActiveIntegerAxis U basis Lsize → ℝ)

variable [NeZero q]

private theorem forecastJointOriginalGridMean_reindexed_comparison
    (hV : gridVolume ≠ 0) (cutoff : ℕ) (hcutoff : 0 < cutoff)
    {D P radius δ : ℝ} (hD : 0 ≤ D)
    (hP : ((Fintype.card Out + 2 : ℕ) : ℝ) ≤ P)
    (hdecay : ∀ i (χ : AddChar (Out → ZMod N) ℂ),
      ‖finiteImageCharacteristic (active i) (fun x j => (Y i x j : ZMod N)) χ‖ ≤
        D * (orderOf χ : ℝ) ^ (-P))
    (C L K : ℝ≥0) (hg : LipschitzWith L density) (hg0 : ∀ y, 0 ≤ density y)
    (htest : ∀ z r, LipschitzWith K (test z r))
    (hcap : ∀ y, |density y| ≤ C) (hbound : ∀ z r y, ‖test z r y‖ ≤ 1)
    (hscale : ∀ j, 0 < scale j) (hradius : 0 ≤ radius) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmesh : ∀ j, ((q * cutoff : ℕ) : ℝ) / scale j ≤ δ)
    (hsupport : ∀ y, radius < ‖y‖ → density y = 0) :
    let g := fun p : (Cont → ℝ) × (Joint → ℝ) => density (join p.1 p.2)
    let φ := fun z (r : (Aux ⊕ Joint) → ZMod q) (p : (Cont → ℝ) × (Joint → ℝ)) =>
      test z (fun a => r (axis a)) (join p.1 p.2)
    let Y' := fun i ω a => Y i ω ((axis).symm a)
    ‖(𝔼 aux : Aux → ZMod N, ∫ c : Cont → ℝ,
        (∑' z, ∑' k : Joint → ℤ,
          (g (c, fun j => ((k j : ℝ) - center j) / scale j) : ℂ) *
          ((rationalInactiveForecast inactive active gridPoint Y' N gridVolume z
            (Sum.elim aux (fun j => (k j : ZMod N))) / gridVolume : ℝ) : ℂ) *
          φ z (Sum.elim (zmodPiReduction hq aux) (fun j => (k j : ZMod q)))
            (c, fun j => ((k j : ℝ) - center j) / scale j)) /
            ((∏ j, scale j : ℝ) : ℂ)) -
      (∑' z, 𝔼 r : (Aux ⊕ Joint) → ZMod N,
      ((rationalInactiveForecast inactive active gridPoint Y' N gridVolume z r / gridVolume : ℝ) : ℂ) *
      ∫ p : (Cont → ℝ) × (Joint → ℝ), (g p : ℂ) * φ z (zmodPiReduction hq r) p
        ∂((volume : Measure (Cont → ℝ)).prod (volume : Measure (Joint → ℝ))))‖ ≤
      ((cutoff : ℝ) ^ (Fintype.card Out + 1) *
        (2 * (2 * radius + 2) ^ Fintype.card Joint * ((L : ℝ) + C * K) * δ) +
        (D / cutoff) * ((2 * radius + 2) ^ Fintype.card Joint * (L : ℝ) * δ)) *
          (2 * radius) ^ Fintype.card Cont +
        (2 * (D / cutoff)) * ∫ y, density y := by
  intro g φ Y'
  have hcard : Fintype.card Out = Fintype.card (Aux ⊕ Joint) := Fintype.card_congr axis
  have hg' : LipschitzWith L g := by
    simpa only [g, Function.comp_def, mul_one] using
      hg.comp (forecastJointCoordinateJoin_lipschitz (X := X) (I := I) U basis Lsize)
  have hφ' (z) (r : (Aux ⊕ Joint) → ZMod q) : LipschitzWith K (φ z r) := by
    simpa only [φ, Function.comp_def, mul_one] using
      (htest z (fun a => r (axis a))).comp
        (forecastJointCoordinateJoin_lipschitz (X := X) (I := I) U basis Lsize)
  have hs' (p : (Cont → ℝ) × (Joint → ℝ)) (hp : radius < ‖p‖) : g p = 0 := by
    apply hsupport
    change radius < ‖join p.1 p.2‖
    rw [forecastJointCoordinateJoin_norm]
    exact hp
  have hp' : ((Fintype.card (Aux ⊕ Joint) + 2 : ℕ) : ℝ) ≤ P := by rwa [← hcard]
  have hd' := fun i => finiteImageCharacteristic_axis_reindex_bound axis (active i) (Y i) N (hdecay i)
  have h := rationalInactive_joint_grid_comparison_instances inactive active gridPoint Y' hV q hq cutoff hcutoff
    hD hp' hd' g φ C L K hg' (fun p => hg0 _) hφ' (fun p => hcap _)
      (fun z r p => hbound _ _ _) center scale hscale hradius hδ hδ1 hmesh hs'
  have hmass : (∫ p : (Cont → ℝ) × (Joint → ℝ), g p
      ∂((volume : Measure (Cont → ℝ)).prod (volume : Measure (Joint → ℝ)))) =
      ∫ y, density y := (forecastJointCoordinateJoin_integral U basis Lsize density).symm
  exact h.trans_eq (by rw [hmass, ← hcard])

theorem forecastJointOriginalGridMean_comparison
    (hV : gridVolume ≠ 0) (cutoff : ℕ) (hcutoff : 0 < cutoff)
    {D P radius δ : ℝ} (hD : 0 ≤ D)
    (hP : ((Fintype.card Out + 2 : ℕ) : ℝ) ≤ P)
    (hdecay : ∀ i (χ : AddChar (Out → ZMod N) ℂ),
      ‖finiteImageCharacteristic (active i) (fun x j => (Y i x j : ZMod N)) χ‖ ≤
        D * (orderOf χ : ℝ) ^ (-P))
    (C L K : ℝ≥0) (hg : LipschitzWith L density) (hg0 : ∀ y, 0 ≤ density y)
    (htest : ∀ z r, LipschitzWith K (test z r))
    (hcap : ∀ y, |density y| ≤ C) (hbound : ∀ z r y, ‖test z r y‖ ≤ 1)
    (hscale : ∀ j, 0 < scale j) (hradius : 0 ≤ radius) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmesh : ∀ j, ((q * cutoff : ℕ) : ℝ) / scale j ≤ δ)
    (hsupport : ∀ y, radius < ‖y‖ → density y = 0) :
    ‖forecastJointOriginalGridMean U basis Lsize hm inactive active gridPoint Y N q hq
      gridVolume density test center scale -
      (∑' z, 𝔼 r : Out → ZMod N,
        ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z r / gridVolume : ℝ) : ℂ) *
          ∫ y, test z (fun a => ZMod.castHom hq (ZMod q) (r a)) y
            ∂realDensityMeasure volume density)‖ ≤
      ((cutoff : ℝ) ^ (Fintype.card Out + 1) *
        (2 * (2 * radius + 2) ^ Fintype.card Joint * ((L : ℝ) + C * K) * δ) +
        (D / cutoff) * ((2 * radius + 2) ^ Fintype.card Joint * (L : ℝ) * δ)) *
          (2 * radius) ^ Fintype.card Cont +
        (2 * (D / cutoff)) * ∫ y, density y := by
  let g := fun p : (Cont → ℝ) × (Joint → ℝ) => density (join p.1 p.2)
  let φ := fun z (r : (Aux ⊕ Joint) → ZMod q) (p : (Cont → ℝ) × (Joint → ℝ)) =>
    test z (fun a => r (axis a)) (join p.1 p.2)
  let Y' := fun i ω a => Y i ω ((axis).symm a)
  have h := forecastJointOriginalGridMean_reindexed_comparison U basis Lsize hm
    inactive active gridPoint Y N q hq gridVolume density test center scale hV cutoff hcutoff
    hD hP hdecay C L K hg hg0 htest hcap hbound hscale hradius hδ hδ1 hmesh hsupport
  have hmean : forecastJointOriginalGridMean U basis Lsize hm inactive active gridPoint Y N q hq
      gridVolume density test center scale =
      (𝔼 aux : Aux → ZMod N, ∫ c : Cont → ℝ,
        (∑' z, ∑' k : Joint → ℤ,
          (g (c, fun j => ((k j : ℝ) - center j) / scale j) : ℂ) *
          ((rationalInactiveForecast inactive active gridPoint Y' N gridVolume z
            (Sum.elim aux (fun j => (k j : ZMod N))) / gridVolume : ℝ) : ℂ) *
          φ z (Sum.elim (zmodPiReduction hq aux) (fun j => (k j : ZMod q)))
            (c, fun j => ((k j : ℝ) - center j) / scale j)) /
            ((∏ j, scale j : ℝ) : ℂ)) :=
    forecastJointOriginalGridMean_reindexed U basis Lsize hm inactive active gridPoint Y N q hq
      gridVolume density test center scale
  rw [hmean]
  have href := forecastJoint_rational_reference U basis Lsize hm inactive active gridPoint Y N q hq
    gridVolume density hg.continuous.measurable hg0 test
  convert h using 1
  congr 2
  exact href.symm

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped Classical BigOperators NNReal
variable {X : Type*} [Fintype X]
variable {m : ℕ} {I E : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
variable {n : Fin m → ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (Lsize : ℕ) (hm : 0 < m)
local notation "short" => allocatedShortAxis (I := I) U basis Lsize
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X E short)
local notation "Aux" => (Σ j : Fin m, E j)
local notation "IntAxis" => AllocatedActiveIntegerAxis U basis Lsize
local notation "Joint" => X ⊕ IntAxis
local notation "Cont" => (Σ j : Fin m, I j)
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)
local notation "Output" => (Σ _a : {a : LayerSamplerAxis I n // ¬short a}, Unit)
local notation "Domain" => (Spatial → ℝ) × (Output → ℝ)
local notation "axis" => forecastCongruenceJointAxisEquiv (X := X) (I := I) (E := E) U basis Lsize hm
local notation "join" => forecastJointCoordinateJoin (X := X) (I := I) U basis Lsize

variable {PIndex Ω Z : Type*} [Fintype PIndex] [Fintype Ω]
variable (inactive : FiniteProbabilityWeights PIndex) (active : PIndex → FiniteProbabilityWeights Ω)
variable (gridPoint : PIndex → Z) (Y : PIndex → Ω → Sigma (AllocatedCongruenceRankOutput X E
  (allocatedShortAxis (I := I) U basis Lsize)) → ℤ)
variable (N q : ℕ) [NeZero N] (hq : q ∣ N) (gridVolume : ℝ)
variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis Lsize a}, Unit) → ℝ)) → ℝ)
variable (test : Z → (Sigma (AllocatedCongruenceRankOutput X E
  (allocatedShortAxis (I := I) U basis Lsize)) → ZMod q) →
  (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis Lsize a}, Unit) → ℝ)) → ℂ)
variable (center scale : X ⊕ AllocatedActiveIntegerAxis U basis Lsize → ℝ)

theorem forecastJointOriginalGridMean_mul_normalization
    (hV : gridVolume ≠ 0) (hscale : ∀ j, scale j ≠ 0) :
    (gridVolume : ℂ) * ((∏ j, scale j : ℝ) : ℂ) *
      forecastJointOriginalGridMean U basis Lsize hm inactive active gridPoint Y N q hq
        gridVolume density test center scale =
    𝔼 aux : Aux → ZMod N, ∫ c : Cont → ℝ,
      ∑' z, ∑' k : Joint → ℤ,
        (density (join c (fun j => ((k j : ℝ) - center j) / scale j)) : ℂ) *
        (rationalInactiveForecast inactive active gridPoint Y N gridVolume z
          (fun a => Sum.elim aux (fun j => (k j : ZMod N)) (axis a)) : ℂ) *
        test z (fun a => Sum.elim (zmodPiReduction hq aux)
          (fun j => (k j : ZMod q)) (axis a))
          (join c (fun j => ((k j : ℝ) - center j) / scale j)) := by
  have hVc : (gridVolume : ℂ) ≠ 0 := by exact_mod_cast hV
  have hTc : ((∏ j, scale j : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast Finset.prod_ne_zero_iff.mpr (fun j _ => hscale j)
  unfold forecastJointOriginalGridMean
  rw [Finset.mul_expect]
  apply Finset.expect_congr rfl
  intro aux haux
  rw [← integral_const_mul]
  apply integral_congr_ae
  refine ae_of_all _ (fun c => ?_)
  dsimp only
  rw [mul_assoc, mul_div_cancel₀ _ hTc]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro z
  rw [← tsum_mul_left]
  apply tsum_congr
  intro k
  push_cast
  field_simp

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory BooleanCubeKernel
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G X T : Type*} [Fintype G] [Fintype X] [Fintype T]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}
variable (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "degree" => layerSamplerDegree I n
local notation "Sample" => CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n
local notation "Original" => PrincipalIntegerTuples B degree Empty (allocatedPrincipalSides B U basis S)
local notation "selected" => allocatedShortIntegerSelection U basis S.value
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X E short)
local notation "Joint" => X ⊕ AllocatedActiveIntegerAxis U basis S.value
local notation "Cont" => (Σ j : Fin m, I j)

include hR hσ in
theorem fixedSpatialNativeJointGridMean_comparison
    (e : G ≃ X ⊕ (X ⊕ T)) (rootBudget rootLength : ℝ) (z : Option G × X → ℝ)
    (h0 : (fixedSpatialKernelBlock e rootBudget rootLength z false).det ≠ 0)
    (h1 : (fixedSpatialKernelBlock e rootBudget rootLength z true).det ≠ 0)
    (hB : ∀ a : Active, 4 ≤ Fintype.card (B a.val))
    (hW : 0 ≤ rootBudget) (hL : 0 ≤ rootLength)
    (hsize : (Fintype.card G : ℝ) * rootLength ≤ rootBudget)
    (hz : ∀ a, |z a| ≤ 1)
    (sample : Sample)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    (hS : 2 ≤ S.value) (hm : 0 < m)
    (τ : ℝ) (base : X → ℤ) (box : X → ℕ)
    (xref : G → IntegerScalarCubeBox Empty S.value)
    {Ω : Type*} [Fintype Ω]
    (active : Original → FiniteProbabilityWeights Ω)
    (Y : Original → Ω → Out → ℤ)
    (N q : ℕ) [NeZero N] [NeZero q] (hq : q ∣ N)
    (hperiod : W.modulus ∣ q) (hcover : W.cover ∣ q)
    (gridVolume : ℝ) (hV : gridVolume ≠ 0)
    (center scale : Joint → ℝ) (hscale : ∀ j, 0 < scale j)
    (cutoff : ℕ) (hcutoff : 0 < cutoff)
    {D P δ : ℝ} (hD : 0 ≤ D)
    (hP : ((Fintype.card Out + 2 : ℕ) : ℝ) ≤ P)
    (hdecay : ∀ i (χ : AddChar (Out → ZMod N) ℂ),
      ‖finiteImageCharacteristic (active i) (fun x j => (Y i x j : ZMod N)) χ‖ ≤
        D * (orderOf χ : ℝ) ^ (-P))
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmesh : ∀ j, ((q * cutoff : ℕ) : ℝ) / scale j ≤ δ) :
    let lower := fun (_a : Active) (_p : B _a.val × Fin (degree _a.val)) => (0 : ℝ)
    let width := fun (_a : Active) (_p : B _a.val × Fin (degree _a.val)) =>
      ((S.value : ℝ) - 1) / S.value
    let density := fixedSpatialKernelOriginalForecastDensity B U basis S e rootBudget rootLength z
      h0 h1 hB lower width sample
    let C := fixedSpatialOriginalForecastCap B
      (fixedSpatialKernelBlockEquiv e rootBudget rootLength z true h1) (δ := 1 / 2) (by norm_num)
    let L := fixedSpatialOriginalForecastLip B
      (fixedSpatialKernelBlockEquiv e rootBudget rootLength z false h0)
      (fixedSpatialKernelBlockEquiv e rootBudget rootLength z true h1) (δ := 1 / 2) (by norm_num)
    let K := Lip * max ‖τ / 8‖₊ (forecastNativeAmbientLip U basis o R)
    let law := principalTupleWeights (α := Empty) B degree
      (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S)
    let c := fun a => (sample (selected a).1).2 (selected a).2
    let grid := forecastInactiveFixedOutput B U basis S selected c xref
    let test := W.forecastShortGridTest U basis S.value hb o bW R q hm hperiod hcover
      (fun a => (base a : ℝ) / box a) τ
    ‖forecastJointOriginalGridMean U basis S.value hm law active grid Y N q hq
        gridVolume density test center scale -
      (∑' g, 𝔼 r : Out → ZMod N,
        ((rationalInactiveForecast law active grid Y N gridVolume g r / gridVolume : ℝ) : ℂ) *
          ∫ y, test g (fun a => ZMod.castHom hq (ZMod q) (r a)) y
            ∂realDensityMeasure volume density)‖ ≤
      ((cutoff : ℝ) ^ (Fintype.card Out + 1) *
        (2 * 8 ^ Fintype.card Joint * ((L : ℝ) + C * K) * δ) +
        (D / cutoff) * (8 ^ Fintype.card Joint * (L : ℝ) * δ)) *
          6 ^ Fintype.card Cont + 2 * (D / cutoff) := by
  classical
  intro lower width density C L K law c grid test
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  have hSpos : (0 : ℝ) < S.value := by exact_mod_cast S.positive
  have hSreal : (2 : ℝ) ≤ S.value := by exact_mod_cast hS
  have hw : (1 / 2 : ℝ) ≤ ((S.value : ℝ) - 1) / S.value := by
    apply (le_div_iff₀ hSpos).mpr
    linarith
  have hwidth : ∀ a p, |lower a p| + |width a p| ≤ 1 := by
    intro a p
    dsimp only [lower, width]
    rw [abs_zero, zero_add, abs_of_nonneg (le_trans (by norm_num) hw)]
    apply (div_le_one hSpos).mpr
    linarith
  have hbnd := fixedSpatialKernelOriginalForecastDensity_bounds B U basis hR hσ S
    e rootBudget rootLength z h0 h1 hB lower width hhalf
    (fun _ _ => hw) (fun _ _ => le_rfl) sample hs
  have hdata := fixedSpatialKernelOriginalForecastDensity_probability_data B U basis hR hσ S
    e rootBudget rootLength z h0 h1 hB lower width hhalf
    (fun _ _ => hw) (fun _ _ => le_rfl) sample hs
  have hsupport : ∀ y, (3 : ℝ) < ‖y‖ → density y = 0 := by
    intro y hy
    exact fixedSpatialKernelOriginalForecastDensity_zero_of_norm_gt_two B U basis hR hσ S
      e rootBudget rootLength z h0 h1 hB lower width hhalf
      (fun _ _ => hw) (fun _ _ => le_rfl) sample hs hwidth hW hL hsize hz y
      (lt_trans (by norm_num) hy)
  have htest := W.forecastShortGridTest_bounds U basis S.value hb o bW R q hm hperiod hcover
    (fun a => (base a : ℝ) / box a) τ
  have h := forecastJointOriginalGridMean_comparison U basis S.value hm law active grid Y N q hq
    gridVolume density test center scale hV cutoff hcutoff hD hP hdecay C L K
    hbnd.2 hdata.1 (fun g r => (htest g r).2)
    (fun y => by rw [abs_of_nonneg (hdata.1 y)]; exact (hbnd.1 y).2)
    (fun g r => (htest g r).1) hscale (radius := 3) (by norm_num) hδ hδ1 hmesh hsupport
  have hmass : (∫ y, density y) = 1 := hdata.2.2
  norm_num only [hmass, mul_one] at h
  exact h

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory BooleanCubeKernel
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G X T : Type*} [Fintype G] [Fintype X] [Fintype T]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}
variable (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "degree" => layerSamplerDegree I n
local notation "Sample" => CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n
local notation "Original" => PrincipalIntegerTuples B degree Empty (allocatedPrincipalSides B U basis S)
local notation "selected" => allocatedShortIntegerSelection U basis S.value
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X E short)
local notation "Joint" => X ⊕ AllocatedActiveIntegerAxis U basis S.value
local notation "Cont" => (Σ j : Fin m, I j)

include hR hσ in
theorem fixedSpatialSliceNativeJointGridMean_comparison
    (e : G ≃ X ⊕ (X ⊕ T)) (rootBudget rootLength : ℝ) (z : Option G × X → ℝ)
    (h0 : (fixedSpatialKernelBlock e rootBudget rootLength z false).det ≠ 0)
    (h1 : (fixedSpatialKernelBlock e rootBudget rootLength z true).det ≠ 0)
    (lowerG widthG : G → ℝ) (hwGne : ∀ g, widthG g ≠ 0)
    (hlG : ∀ g, 0 ≤ lowerG g) (hwG : ∀ g, 0 ≤ widthG g)
    (hcontainedG : ∀ g, lowerG g + widthG g ≤ 1)
    (hB : ∀ a : Active, 4 ≤ Fintype.card (B a.val))
    (lowerP widthP : ∀ a : Active, B a.val × Fin (degree a.val) → ℝ)
    {δP : ℝ} (hδP : 0 < δP)
    (hwP : ∀ a p, δP ≤ widthP a p) (hlP : ∀ a p, 0 ≤ lowerP a p)
    (hwidthP : ∀ a p, |lowerP a p| + |widthP a p| ≤ 1)
    (hW : 0 ≤ rootBudget) (hL : 0 ≤ rootLength)
    (hsize : (Fintype.card G : ℝ) * rootLength ≤ rootBudget)
    (hz : ∀ a, |z a| ≤ 1)
    (sample : Sample)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    (hm : 0 < m)
    (τ : ℝ) (base : X → ℤ) (box : X → ℕ)
    (xref : G → IntegerScalarCubeBox Empty S.value)
    {Ω : Type*} [Fintype Ω]
    (law : FiniteProbabilityWeights Original)
    (active : Original → FiniteProbabilityWeights Ω)
    (Y : Original → Ω → Out → ℤ)
    (N q : ℕ) [NeZero N] [NeZero q] (hq : q ∣ N)
    (hperiod : W.modulus ∣ q) (hcover : W.cover ∣ q)
    (gridVolume : ℝ) (hV : gridVolume ≠ 0)
    (center scale : Joint → ℝ) (hscale : ∀ j, 0 < scale j)
    (cutoff : ℕ) (hcutoff : 0 < cutoff)
    {D P δ : ℝ} (hD : 0 ≤ D)
    (hP : ((Fintype.card Out + 2 : ℕ) : ℝ) ≤ P)
    (hdecay : ∀ i (χ : AddChar (Out → ZMod N) ℂ),
      ‖finiteImageCharacteristic (active i) (fun x j => (Y i x j : ZMod N)) χ‖ ≤
        D * (orderOf χ : ℝ) ^ (-P))
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmesh : ∀ j, ((q * cutoff : ℕ) : ℝ) / scale j ≤ δ) :
    let frame := fixedSpatialKernelSliceFrame rootBudget rootLength z lowerG widthG
    let h0slice := fixedSpatialKernelBlock_slice_det_ne_zero e rootBudget rootLength z
      lowerG widthG false h0 hwGne
    let h1slice := fixedSpatialKernelBlock_slice_det_ne_zero e rootBudget rootLength z
      lowerG widthG true h1 hwGne
    let density := fixedSpatialKernelSliceOriginalForecastDensity B U basis S e rootBudget rootLength z
      lowerG widthG h0 h1 hwGne hB lowerP widthP sample
    let C := fixedSpatialOriginalForecastCap B
      (fixedSpatialKernelBlockEquiv e rootBudget rootLength frame true h1slice) hδP
    let L := fixedSpatialOriginalForecastLip B
      (fixedSpatialKernelBlockEquiv e rootBudget rootLength frame false h0slice)
      (fixedSpatialKernelBlockEquiv e rootBudget rootLength frame true h1slice) hδP
    let K := Lip * max ‖τ / 8‖₊ (forecastNativeAmbientLip U basis o R)
    let c := fun a => (sample (selected a).1).2 (selected a).2
    let grid := forecastInactiveFixedOutput B U basis S selected c xref
    let test := W.forecastShortGridTest U basis S.value hb o bW R q hm hperiod hcover
      (fun a => (base a : ℝ) / box a) τ
    ‖forecastJointOriginalGridMean U basis S.value hm law active grid Y N q hq
        gridVolume density test center scale -
      (∑' g, 𝔼 r : Out → ZMod N,
        ((rationalInactiveForecast law active grid Y N gridVolume g r / gridVolume : ℝ) : ℂ) *
          ∫ y, test g (fun a => ZMod.castHom hq (ZMod q) (r a)) y
            ∂realDensityMeasure volume density)‖ ≤
      ((cutoff : ℝ) ^ (Fintype.card Out + 1) *
        (2 * 8 ^ Fintype.card Joint * ((L : ℝ) + C * K) * δ) +
        (D / cutoff) * (8 ^ Fintype.card Joint * (L : ℝ) * δ)) *
          6 ^ Fintype.card Cont + 2 * (D / cutoff) := by
  classical
  intro frame h0slice h1slice density C L K c grid test
  have hbnd := fixedSpatialKernelSliceOriginalForecastDensity_bounds B U basis hR hσ S
    e rootBudget rootLength z lowerG widthG h0 h1 hwGne hB lowerP widthP
    hδP hwP hlP sample hs
  have hdata := fixedSpatialKernelSliceOriginalForecastDensity_probability_data B U basis hR hσ S
    e rootBudget rootLength z lowerG widthG h0 h1 hwGne hB lowerP widthP
    hδP hwP hlP sample hs
  have hsupport : ∀ y, (3 : ℝ) < ‖y‖ → density y = 0 := by
    intro y hy
    exact fixedSpatialKernelSliceOriginalForecastDensity_zero_of_norm_gt_two B U basis hR hσ S
      e rootBudget rootLength z lowerG widthG h0 h1 hwGne hB lowerP widthP
      hδP hwP hlP sample hs hwidthP hW hL hsize hz hlG hwG hcontainedG y
      (lt_trans (by norm_num) hy)
  have htest := W.forecastShortGridTest_bounds U basis S.value hb o bW R q hm hperiod hcover
    (fun a => (base a : ℝ) / box a) τ
  have h := forecastJointOriginalGridMean_comparison U basis S.value hm law active grid Y N q hq
    gridVolume density test center scale hV cutoff hcutoff hD hP hdecay C L K
    hbnd.2 hdata.1 (fun g r => (htest g r).2)
    (fun y => by rw [abs_of_nonneg (hdata.1 y)]; exact (hbnd.1 y).2)
    (fun g r => (htest g r).1) hscale (radius := 3) (by norm_num) hδ hδ1 hmesh hsupport
  have hmass : (∫ y, density y) = 1 := hdata.2.2
  norm_num only [hmass, mul_one] at h
  exact h

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory BooleanCubeKernel
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G X T : Type*} [Fintype G] [Fintype X] [Fintype T]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}
variable (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "degree" => layerSamplerDegree I n
local notation "Sample" => CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n
local notation "Original" => PrincipalIntegerTuples B degree Empty (allocatedPrincipalSides B U basis S)
local notation "selected" => allocatedShortIntegerSelection U basis S.value
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X E short)
local notation "Joint" => X ⊕ AllocatedActiveIntegerAxis U basis S.value
local notation "Cont" => (Σ j : Fin m, I j)

include hR hσ in
theorem fixedSpatialNativeJointGridMean_precision
    (e : G ≃ X ⊕ (X ⊕ T)) (rootBudget rootLength : ℝ) (z : Option G × X → ℝ)
    (h0 : (fixedSpatialKernelBlock e rootBudget rootLength z false).det ≠ 0)
    (h1 : (fixedSpatialKernelBlock e rootBudget rootLength z true).det ≠ 0)
    (hB : ∀ a : Active, 4 ≤ Fintype.card (B a.val))
    (hW : 0 ≤ rootBudget) (hL : 0 ≤ rootLength)
    (hsize : (Fintype.card G : ℝ) * rootLength ≤ rootBudget)
    (hz : ∀ a, |z a| ≤ 1)
    (sample : Sample)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    (hS : 2 ≤ S.value) (hm : 0 < m)
    (τ : ℝ) (base : X → ℤ) (box : X → ℕ)
    (xref : G → IntegerScalarCubeBox Empty S.value)
    {Ω : Type*} [Fintype Ω]
    (active : Original → FiniteProbabilityWeights Ω)
    (Y : Original → Ω → Out → ℤ)
    (N q : ℕ) [NeZero N] [NeZero q] (hq : q ∣ N)
    (hperiod : W.modulus ∣ q) (hcover : W.cover ∣ q)
    (gridVolume : ℝ) (hV : gridVolume ≠ 0)
    (d : ℕ) {Pbound Eerr Q Pτ PR : ℝ} (hPbound : 0 ≤ Pbound) (hEerr : 0 ≤ Eerr)
    {D decayPower : ℝ} (hD : 0 ≤ D) (hDP : D ≤ Real.exp Pbound)
    (hdecayPower : ((Fintype.card Out + 2 : ℕ) : ℝ) ≤ decayPower)
    (hdecay : ∀ i (χ : AddChar (Out → ZMod N) ℂ),
      ‖finiteImageCharacteristic (active i) (fun x j => (Y i x j : ZMod N)) χ‖ ≤
        D * (orderOf χ : ℝ) ^ (-decayPower))
    (hdOut : Fintype.card Out ≤ d) (hdJoint : Fintype.card Joint ≤ d)
    (hdCont : Fintype.card Cont ≤ d)
    (hτ : 0 < τ) (hqexp : (q : ℝ) ≤ Real.exp Q) (hτinv : τ⁻¹ ≤ Real.exp Pτ)
    (hRinv : ∀ j, (R j)⁻¹ ≤ Real.exp PR)
    (hfloor : forecastJointGridSamplerFloor d Pbound Eerr Q PR ≤ S.value)
    (hbox : ∀ i, Real.exp (forecastJointGridAmbientLog d Pbound Eerr Q Pτ) ≤ (box i : ℝ)) :
    let C := fixedSpatialOriginalForecastCap B
      (fixedSpatialKernelBlockEquiv e rootBudget rootLength z true h1) (δ := 1 / 2) (by norm_num)
    let L := fixedSpatialOriginalForecastLip B
      (fixedSpatialKernelBlockEquiv e rootBudget rootLength z false h0)
      (fixedSpatialKernelBlockEquiv e rootBudget rootLength z true h1) (δ := 1 / 2) (by norm_num)
    let K := Lip * max ‖τ / 8‖₊ (forecastNativeAmbientLip U basis o R)
    (C : ℝ) ≤ Real.exp Pbound → (L : ℝ) ≤ Real.exp Pbound →
    (K : ℝ) ≤ Real.exp Pbound →
    let lower := fun (_a : Active) (_p : B _a.val × Fin (degree _a.val)) => (0 : ℝ)
    let width := fun (_a : Active) (_p : B _a.val × Fin (degree _a.val)) =>
      ((S.value : ℝ) - 1) / S.value
    let density := fixedSpatialKernelOriginalForecastDensity B U basis S e rootBudget rootLength z
      h0 h1 hB lower width sample
    let law := principalTupleWeights (α := Empty) B degree
      (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S)
    let c := fun a => (sample (selected a).1).2 (selected a).2
    let grid := forecastInactiveFixedOutput B U basis S selected c xref
    let test := W.forecastShortGridTest U basis S.value hb o bW R q hm hperiod hcover
      (fun a => (base a : ℝ) / box a) τ
    ‖forecastJointOriginalGridMean U basis S.value hm law active grid Y N q hq
        gridVolume density test
        (fun j => (forecastJointGridCenter U basis S.value base j : ℝ))
        (forecastJointGridScale U basis R S.value box τ) -
      (∑' g, 𝔼 r : Out → ZMod N,
        ((rationalInactiveForecast law active grid Y N gridVolume g r / gridVolume : ℝ) : ℂ) *
          ∫ y, test g (fun a => ZMod.castHom hq (ZMod q) (r a)) y
            ∂realDensityMeasure volume density)‖ ≤
      Real.exp (-Eerr) := by
  intro C L K hcap hLip htestLip lower width density law c grid test
  have hmesh := forecastJointGridScale_mesh_of_floor U basis d hPbound hEerr hR hτ
    q S.value box hqexp hτinv hRinv hfloor hbox
  have hboxpos (i : X) : 0 < box i := Nat.cast_pos.mp ((Real.exp_pos _).trans_le (hbox i))
  have hscale := forecastJointGridScale_pos U basis hR S.value box hboxpos hτ
  have hδ := forecastJointGridMesh_bounds d hPbound hEerr
  have hcomparison := fixedSpatialNativeJointGridMean_comparison B U basis hR hσ S hb o bW W
    e rootBudget rootLength z h0 h1 hB hW hL hsize hz sample hs hS hm τ base box xref
    active Y N q hq hperiod hcover gridVolume hV
    (fun j => (forecastJointGridCenter U basis S.value base j : ℝ))
    (forecastJointGridScale U basis R S.value box τ) hscale
    (forecastJointGridCutoff Pbound Eerr) (forecastJointGridCutoff_pos hPbound hEerr)
    hD hdecayPower hdecay hδ.1.le hδ.2 hmesh
  have hbudget := (forecastJointGridErrorBudget d hPbound hEerr).2.2.2.2
    hdOut hdJoint hdCont hD L.coe_nonneg C.coe_nonneg K.coe_nonneg
    hDP hLip hcap htestLip hδ.1.le (le_refl (forecastJointGridMesh d Pbound Eerr))
  exact hcomparison.trans (by simpa only [forecastJointGridError] using hbudget)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory BooleanCubeKernel
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G X T : Type*} [Fintype G] [Fintype X] [Fintype T]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}
variable (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "degree" => layerSamplerDegree I n
local notation "Sample" => CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n
local notation "Original" => PrincipalIntegerTuples B degree Empty (allocatedPrincipalSides B U basis S)
local notation "selected" => allocatedShortIntegerSelection U basis S.value
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X E short)
local notation "Joint" => X ⊕ AllocatedActiveIntegerAxis U basis S.value
local notation "Cont" => (Σ j : Fin m, I j)

local notation "Long" => LayerSamplerLongVariables short G B

local instance recoveredNativeGridPrecisionModulusNeZero (Pr : Finset ℕ) (A : ℕ → ℕ)
    [∀ p : Pr, NeZero p.val] : NeZero (∏ p : Pr, p.val ^ A p.val) :=
  ⟨Finset.prod_ne_zero_iff.mpr (fun p _ => pow_ne_zero _ (NeZero.ne p.val))⟩

include hR hσ in
theorem allocatedRecoveredNativeJointGridMean_precision
    (e : G ≃ X ⊕ (X ⊕ T)) (rootBudget rootLength : ℝ) (z : Option G × X → ℝ)
    (h0 : (fixedSpatialKernelBlock e rootBudget rootLength z false).det ≠ 0)
    (h1 : (fixedSpatialKernelBlock e rootBudget rootLength z true).det ≠ 0)
    (hB : ∀ a : Active, 4 ≤ Fintype.card (B a.val))
    (hW : 0 ≤ rootBudget) (hL : 0 ≤ rootLength)
    (hsize : (Fintype.card G : ℝ) * rootLength ≤ rootBudget)
    (hz : ∀ a, |z a| ≤ 1)
    (sample : Sample)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    (hS : 2 ≤ S.value) (hm : 0 < m)
    (τ : ℝ) (base : X → ℤ) (box : X → ℕ)
    (xref : G → IntegerScalarCubeBox Empty S.value)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (hnoise : allocatedReadNoise read = noise)
    (hinteger : ∀ j i d, allocatedReadProjection read ⟨j, Sum.inr i⟩ d = (sample j).2 i d)
    {Lrank : ℕ} (spatial : Fin Lrank ↪ G)
    (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis short j, Fin Lrank ↪ B ⟨j,a.val⟩)
    (Dmod : ℕ)
    (hDmod : Fintype.card X + ∑ j : Fin m, (Fintype.card (E j) + n j) ≤ Dmod)
    (Pr : Finset ℕ) [∀ p : Pr, NeZero p.val]
    (Aexp : ℕ → ℕ) (hp : ∀ p ∈ Pr, p.Prime) (Rbad : ℕ)
    (hbad : (∏ p ∈ Pr, p ^ largestTestedBadDepth Aexp
      (allocatedActualPrimeBad short spatial kernel block Pr
        (modularForecastRankConstant m Dmod : ℝ)) p read) ≤ Rbad)
    (origin : ∀ p : Pr, Long → ZMod (p.val ^ Aexp p.val))
    (q : ℕ) [NeZero q] (hq : q ∣ ∏ p : Pr, p.val ^ Aexp p.val)
    (hperiod : W.modulus ∣ q) (hcover : W.cover ∣ q)
    (gridVolume : ℝ) (hV : gridVolume ≠ 0)
    (d : ℕ) {Pbound Eerr Q Pτ PR : ℝ} (hPbound : 0 ≤ Pbound) (hEerr : 0 ≤ Eerr)
    (hDP : (Rbad : ℝ) ^
      (modularRankDecayExponent m (modularForecastRankConstant m Dmod : ℝ) *
        modularRankChargeFactor m) ≤ Real.exp Pbound)
    (hdOut : Fintype.card Out ≤ d) (hdJoint : Fintype.card Joint ≤ d)
    (hdCont : Fintype.card Cont ≤ d)
    (hτ : 0 < τ) (hqexp : (q : ℝ) ≤ Real.exp Q) (hτinv : τ⁻¹ ≤ Real.exp Pτ)
    (hRinv : ∀ j, (R j)⁻¹ ≤ Real.exp PR)
    (hfloor : forecastJointGridSamplerFloor d Pbound Eerr Q PR ≤ S.value)
    (hbox : ∀ i, Real.exp (forecastJointGridAmbientLog d Pbound Eerr Q Pτ) ≤ (box i : ℝ)) :
    let N := ∏ p : Pr, p.val ^ Aexp p.val
    let poly := allocatedForecastPolynomial short base noise (allocatedReadDeck read)
      (allocatedOriginalSampleCongruenceProjection B U basis S sample)
    let pRat := crtPolynomialInputLaw (fun p : Pr => p.val) (fun p : Pr => Aexp p.val)
      (fun _ : Pr => 0)
      (primePower_crt_coprime (fun p : Pr => p.val) (fun p : Pr => Aexp p.val)
        (fun p => hp p.val p.property) Subtype.val_injective) origin
    let active := fun _ : Original => pRat
    let Y := fun v : Original => integerLongPolynomialOutput poly (fun k => (v k.1 k.2 : ℤ)) N
    let C := fixedSpatialOriginalForecastCap B
      (fixedSpatialKernelBlockEquiv e rootBudget rootLength z true h1) (δ := 1 / 2) (by norm_num)
    let L := fixedSpatialOriginalForecastLip B
      (fixedSpatialKernelBlockEquiv e rootBudget rootLength z false h0)
      (fixedSpatialKernelBlockEquiv e rootBudget rootLength z true h1) (δ := 1 / 2) (by norm_num)
    let K := Lip * max ‖τ / 8‖₊ (forecastNativeAmbientLip U basis o R)
    (C : ℝ) ≤ Real.exp Pbound → (L : ℝ) ≤ Real.exp Pbound →
    (K : ℝ) ≤ Real.exp Pbound →
    let lower := fun (_a : Active) (_p : B _a.val × Fin (degree _a.val)) => (0 : ℝ)
    let width := fun (_a : Active) (_p : B _a.val × Fin (degree _a.val)) =>
      ((S.value : ℝ) - 1) / S.value
    let density := fixedSpatialKernelOriginalForecastDensity B U basis S e rootBudget rootLength z
      h0 h1 hB lower width sample
    let law := principalTupleWeights (α := Empty) B degree
      (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S)
    let c := fun a => (sample (selected a).1).2 (selected a).2
    let grid := forecastInactiveFixedOutput B U basis S selected c xref
    let test := W.forecastShortGridTest U basis S.value hb o bW R q hm hperiod hcover
      (fun a => (base a : ℝ) / box a) τ
    ‖forecastJointOriginalGridMean U basis S.value hm law active grid Y N q hq
        gridVolume density test
        (fun j => (forecastJointGridCenter U basis S.value base j : ℝ))
        (forecastJointGridScale U basis R S.value box τ) -
      (∑' g, 𝔼 r : Out → ZMod N,
        ((rationalInactiveForecast law active grid Y N gridVolume g r / gridVolume : ℝ) : ℂ) *
          ∫ y, test g (fun a => ZMod.castHom hq (ZMod q) (r a)) y
            ∂realDensityMeasure volume density)‖ ≤
      Real.exp (-Eerr) := by
  classical
  intro N poly pRat active Y C L K hcap hLip htestLip lower width density law c grid test
  let Cmod := (modularForecastRankConstant m Dmod : ℝ)
  let D := (Rbad : ℝ) ^ (modularRankDecayExponent m Cmod * modularRankChargeFactor m)
  have hD : 0 ≤ D := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hP : ((Fintype.card Out + 2 : ℕ) : ℝ) ≤ modularRankDecayExponent m Cmod :=
    allocatedCongruenceForecastRankConstant_dimension short hm Dmod hDmod
  have hdecay (v : Original) (χ : AddChar (Out → ZMod N) ℂ) :
      ‖finiteImageCharacteristic (active v) (fun t j => (Y v t j : ZMod N)) χ‖ ≤
        D * (orderOf χ : ℝ) ^ (-modularRankDecayExponent m Cmod) :=
    allocatedRecoveredForecast_crt_decay B U basis S base noise read hnoise sample hinteger
      spatial kernel block hm Pr Aexp hp Cmod (Nat.cast_nonneg _) Rbad hbad origin
      (fun k => (v k.1 k.2 : ℤ)) χ
  exact fixedSpatialNativeJointGridMean_precision B U basis hR hσ S hb o bW W
    e rootBudget rootLength z h0 h1 hB hW hL hsize hz sample hs hS hm τ base box xref
    active Y N q hq hperiod hcover gridVolume hV d hPbound hEerr hD hDP hP hdecay
    hdOut hdJoint hdCont hτ hqexp hτinv hRinv hfloor hbox hcap hLip htestLip

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X] {T : Type*} [Fintype T]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "degree" => layerSamplerDegree I n
local notation "Input" => (Σ a : Active, B (Subtype.val a) × Fin (degree (Subtype.val a)))
local notation "Output" => (Σ _a : Active, Unit)
local notation "Sample" => CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n
local notation "noise" => allocatedSampleRestrictedProfileNoise B U basis S short

local notation "Spatial" => ((Σ _ : X, Unit ⊕ Empty) → ℝ)
local notation "Domain" => (Spatial × (Output → ℝ))
local notation "budget" => allocatedPhysicalRootBudget B U basis S (fun _ => 0)
local notation "ShortTuple" => PrincipalAxisTuples (α := Empty)
  (allocatedShortAxis (I := I) U basis S.value) (allocatedPrincipalSides B U basis S)

local notation "sides" => allocatedPrincipalSides B U basis S
local notation "hSides" => allocatedPrincipalSides_pos B U basis S
local notation "FullInput" => PrincipalTupleIndex B degree
local notation "Original" => PrincipalIntegerTuples B degree Empty sides

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (Pr : Finset ℕ) [∀ p : Pr, NeZero p.val] (Aexp : ℕ → ℕ)
local notation "primes" => (fun p : Pr => Subtype.val p)
local notation "exponent" => (fun p : Pr => Aexp (Subtype.val p))
local notation "N" => (∏ p : Pr, Subtype.val p ^ Aexp (Subtype.val p))
local instance fixedPathRecoveredGridCRTModulusNeZero : NeZero N :=
  ⟨Finset.prod_ne_zero_iff.mpr (fun p _ => pow_ne_zero _ (NeZero.ne p.val))⟩
local notation "Long" => LayerSamplerLongVariables short G B
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X E short)

variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}
variable (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
local notation "selected" => allocatedShortIntegerSelection U basis S.value
local notation "Grid" => AllocatedShortIntegerAxis U basis S.value →
  ((Finset.univ : Finset (Finset Empty)) : Type) → ℤ

local instance fixedPathRecoveredGridCoverNeZero : NeZero W.cover := ⟨W.cover_pos.ne'⟩

include hR hσ in
theorem allocatedFixedPath_recovered_native_jointGrid_comparison
    (τ ξ : ℝ) (hτ : 0 < τ) (hξ : 0 < ξ) (box : X → ℕ) (hbox : ∀ x, 0 < box x)
    (integerFrame : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (hframe : integerFrame ∈ rectangularWeightIndices 0
      (narrowTrimmedSpatialWidths (G := G) (J := FullInput) budget τ ξ box) 1)
    (e : G ≃ X ⊕ (X ⊕ T))
    (h0 : (fixedSpatialKernelBlock e budget (S.value : ℝ) (allocatedFixedPathKernelFrame B U basis S τ ξ box integerFrame) false).det ≠ 0)
    (h1 : (fixedSpatialKernelBlock e budget (S.value : ℝ) (allocatedFixedPathKernelFrame B U basis S τ ξ box integerFrame) true).det ≠ 0)
    (hB : ∀ a : Active, 4 ≤ Fintype.card (B a.val))
    (sample : Sample)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    {t : ℝ} (ht : 0 < t) (hσbound : ∀ j, |σ j| ≤ t)
    (b : ∀ a : Active, B a.val) {η : ℝ} (hη : 0 < η)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition)
    (htail : |t| * polynomialMassC2Budget (Fintype.card Input) m 1 ≤
      slicedPrincipalC2Tolerance (Fintype.card Input) (Fintype.card Active) m 1
        (unitProfilePrincipalLowerBound B) (1 / 2) A η)
    (hS : 2 ≤ S.value) (q : ℕ) [NeZero q] (hsize : q ≤ S.value)
    (hsmall : scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / S.value) < 1)
    (hm : 0 < m) (hperiod : W.modulus ∣ q) (hcover : W.cover ∣ q)
    (xref : G → IntegerScalarCubeBox Empty S.value)
    (base : X → ℤ)
    (nativePoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hmem : ∀ j a, coefficients (nativePoly j) a ∈ U j)
    (hdegree : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (nativePoly j))
    (hbase : canonicalCoefficientSample U basis hb o sample =
      affineSampleCoefficientTorus U nativePoly hmem
        (fun k x => ((integerBaseTranslation (K := LayerSamplerVariables G I n B) base +
          integerFrame) (k, x) : ℝ)))
    (hsmallChart : ∀ a, |coefficientSamplerAmbientPoint U basis o sample a| < 1 / 2)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (hread : ∀ event : CoefficientChartResidues (LayerSamplerVariables G I n B) n E W.cover → Prop,
      coefficientDeckChartEvent U bW basis hb o W.cover event
        (affineCoefficientCoverSample U nativePoly hmem W.cover
          (fun k x => ((integerBaseTranslation (K := LayerSamplerVariables G I n B) base +
            integerFrame) (k, x) : ℝ))) ↔
        event (allocatedReadCoefficientChartResidues (fun i => (read i : ZMod W.cover))))
    (hnoise : allocatedReadNoise read = integerFrame)
    (hinteger : ∀ j i d, allocatedReadProjection read ⟨j, Sum.inr i⟩ d = (sample j).2 i d)
    {Lrank : ℕ} (spatial : Fin Lrank ↪ G)
    (kernelRank : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis short j, Fin Lrank ↪ B ⟨j,a.val⟩)
    (Dmod : ℕ)
    (hDmod : Fintype.card X + ∑ j : Fin m, (Fintype.card (E j) + n j) ≤ Dmod)
    (hp : ∀ p ∈ Pr, p.Prime) (Rbad : ℕ)
    (hbad : (∏ p ∈ Pr, p ^ largestTestedBadDepth Aexp
      (allocatedActualPrimeBad short spatial kernelRank block Pr
        (modularForecastRankConstant m Dmod : ℝ)) p read) ≤ Rbad)
    (origin : ∀ p : Pr, Long → ZMod (p.val ^ Aexp p.val))
    (hqN : q ∣ N) {gridVolume : ℝ} (hV : gridVolume ≠ 0)
    (d : ℕ) {Pbound Eerr Q Pτ PR : ℝ} (hPbound : 0 ≤ Pbound) (hEerr : 0 ≤ Eerr)
    (hDP : (Rbad : ℝ) ^
      (modularRankDecayExponent m (modularForecastRankConstant m Dmod : ℝ) *
        modularRankChargeFactor m) ≤ Real.exp Pbound)
    (hdOut : Fintype.card Out ≤ d)
    (hdJoint : Fintype.card (X ⊕ AllocatedActiveIntegerAxis U basis S.value) ≤ d)
    (hdCont : Fintype.card (Σ j : Fin m, I j) ≤ d)
    (hqexp : (q : ℝ) ≤ Real.exp Q) (hτinv : τ⁻¹ ≤ Real.exp Pτ)
    (hRinv : ∀ j, (R j)⁻¹ ≤ Real.exp PR)
    (hfloor : forecastJointGridSamplerFloor d Pbound Eerr Q PR ≤ S.value)
    (hboxLarge : ∀ i, Real.exp (forecastJointGridAmbientLog d Pbound Eerr Q Pτ) ≤ (box i : ℝ))
    (hcap : (fixedSpatialOriginalForecastCap B
      (fixedSpatialKernelBlockEquiv e budget (S.value : ℝ)
        (allocatedFixedPathKernelFrame B U basis S τ ξ box integerFrame) true h1)
      (δ := 1 / 2) (by norm_num) : ℝ) ≤ Real.exp Pbound)
    (hLip : (fixedSpatialOriginalForecastLip B
      (fixedSpatialKernelBlockEquiv e budget (S.value : ℝ)
        (allocatedFixedPathKernelFrame B U basis S τ ξ box integerFrame) false h0)
      (fixedSpatialKernelBlockEquiv e budget (S.value : ℝ)
        (allocatedFixedPathKernelFrame B U basis S τ ξ box integerFrame) true h1)
      (δ := 1 / 2) (by norm_num) : ℝ) ≤ Real.exp Pbound)
    (htestLip : ((Lip * max ‖τ / 8‖₊ (forecastNativeAmbientLip U basis o R) : ℝ≥0) : ℝ) ≤
      Real.exp Pbound) :
    let c := fun a => (sample (selected a).1).2 (selected a).2
    let projection := allocatedOriginalSampleCongruenceProjection B U basis S sample
    let poly := allocatedForecastPolynomial short base integerFrame (allocatedReadDeck read) projection
    let lower := fun (_a : Active) (_p : B _a.val × Fin (degree _a.val)) => (0 : ℝ)
    let width := fun (_a : Active) (_p : B _a.val × Fin (degree _a.val)) =>
      ((S.value : ℝ) - 1) / S.value
    let Kφ := Lip * max ‖τ / 8‖₊ (forecastNativeAmbientLip U basis o R)
    let K := Kφ * allocatedOriginalSampleFullSliceLip B U basis S t
    let kernel := FiniteProbabilityWeights.pi (fun _ : G => integerScalarCubeWeights Empty S.value S.positive)
    let law := principalTupleWeights (α := Empty) B degree sides hSides
    let density := fixedSpatialKernelOriginalForecastDensity B U basis S e budget
      (S.value : ℝ) (allocatedFixedPathKernelFrame B U basis S τ ξ box integerFrame) h0 h1 hB lower width sample
    let pRat := crtPolynomialInputLaw primes exponent (fun _ : Pr => 0)
      (primePower_crt_coprime primes exponent (fun p => hp p.val p.property)
        Subtype.val_injective) origin
    let grid := forecastInactiveFixedOutput B U basis S selected c xref
    let Y := fun v : Original => integerLongPolynomialOutput poly (fun k => (v k.1 k.2 : ℤ)) N
    let test := W.forecastShortGridTest U basis S.value hb o bW R q hm hperiod hcover
      (fun a => (base a : ℝ) / box a) τ
    ‖kernel.complexMean (fun x => law.complexMean (fun v =>
        W.eval box nativePoly (fun a => base a + integerPhysicalSite
          (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x v) integerFrame a))) -
      forecastJointOriginalGridMean U basis S.value hm law (fun _ => pRat) grid Y N q hqN
        gridVolume density test
        (fun j => (forecastJointGridCenter U basis S.value base j : ℝ))
        (forecastJointGridScale U basis R S.value box τ)‖ ≤
      ((Fintype.card Input : ℝ) * ((q : ℝ) / S.value) +
        (2 * ((2 * scalarCubeGridBoundaryConstant Empty + K * 2) *
          ∑ _j : Input, (q : ℝ) / S.value + K * (1 / S.value)) + 2 * η)) +
      (1 + 2 * (2 * scalarCubeGridBoundaryConstant Empty + Kφ)) *
        (Fintype.card G * ((q : ℝ) / S.value)) + (Kφ : ℝ) * ξ + Real.exp (-Eerr) := by
  classical
  intro c projection poly lower width Kφ K kernel law density pRat grid Y test
  let reference : ℂ := ∑' g, 𝔼 r : Out → ZMod N,
    ((rationalInactiveForecast law (fun _ => pRat) grid Y N gridVolume g r / gridVolume : ℝ) : ℂ) *
      ∫ y, test g (fun a => ZMod.castHom hqN (ZMod q) (r a)) y
        ∂realDensityMeasure volume density
  have hsrc := allocatedFixedPath_recovered_native_rational_density_comparison
    B U basis hR hσ S primes exponent hb o bW W τ ξ hτ hξ box hbox integerFrame hframe
    e h0 h1 hB sample hs ht hσbound b hη A hA htail hS q hsize hsmall hm hperiod hcover
    xref base nativePoly hmem hdegree hbase hsmallChart read hread
    (fun p => hp p.val p.property) Subtype.val_injective
    (primePower_crt_coprime primes exponent (fun p => hp p.val p.property)
      Subtype.val_injective) origin hqN hV
  have hg := allocatedFixedPathKernelFrame_geometry B U basis S hτ hξ box hbox integerFrame hframe
  have hgrid := allocatedRecoveredNativeJointGridMean_precision B U basis hR hσ S hb o bW W
    e budget (S.value : ℝ) (allocatedFixedPathKernelFrame B U basis S τ ξ box integerFrame)
    h0 h1 hB hg.1 hg.2.1 hg.2.2.1 hg.2.2.2 sample hs hS hm τ base box xref
    integerFrame read hnoise hinteger spatial kernelRank block Dmod hDmod Pr Aexp hp Rbad hbad
    origin q hqN hperiod hcover gridVolume hV d hPbound hEerr hDP hdOut hdJoint hdCont
    hτ hqexp hτinv hRinv hfloor hboxLarge hcap hLip htestLip
  have htriangle := norm_sub_le_norm_sub_add_norm_sub
    (kernel.complexMean (fun x => law.complexMean (fun v =>
      W.eval box nativePoly (fun a => base a + integerPhysicalSite
        (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x v) integerFrame a))))
    reference
    (forecastJointOriginalGridMean U basis S.value hm law (fun _ => pRat) grid Y N q hqN
      gridVolume density test
      (fun j => (forecastJointGridCenter U basis S.value base j : ℝ))
      (forecastJointGridScale U basis R S.value box τ))
  rw [norm_sub_rev reference] at htriangle
  exact htriangle.trans (add_le_add hsrc hgrid)

end Erdos3.VectorPolynomial

end

end OAI
