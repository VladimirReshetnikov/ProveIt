import OAI.Combinatorics.Progressions.Estimates.CoefficientFamilyLocalization
import OAI.Combinatorics.Progressions.Estimates.CoefficientLengthProduct
import OAI.Combinatorics.Progressions.Estimates.UniformStridedBlockEntry
import OAI.Combinatorics.Progressions.Geometry.EmptyCubeCoordinate
import OAI.Combinatorics.Progressions.Lattices.AffineCubeCoordinates
import OAI.Combinatorics.Progressions.Polynomial.PolynomialScalarCubeLength

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical
open CircleFourier

theorem booleanBlockPhase_bounded_stride_major_arc {n : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (N : Fin (n+1) → ℕ) (s : Fin (n+1) → Option α → ℕ)
    (u : Fin (n+1) → Option α → ℝ) (ξ : Finset α → ℝ)
    (J : Finset (Finset α)) (hJ : ∀ S ∈ J, S.card ≤ n+1)
    (hs : ∀ g r, 0 < s g r) {R : ℝ} (hR : ∀ g r, (s g r : ℝ) ≤ R)
    {ζ : ℝ} (hζ : 0 < ζ) (hN : ∀ g, multiaffineBiasBudget n ζ ≤ N g)
    (hbias : ζ ≤ ‖𝔼 x : ∀ g, Option α → Fin (N g),
      character ((booleanBlockPhase ξ (fun g r => u g r+(s g r : ℝ)*((x g r).val : ℝ)) : ℝ) :
        CircleFourier.Circle)‖) :
    ∃ D : ℕ, 0 < D ∧ (D : ℝ) ≤ (multiaffineBiasBudget n ζ*R^(n+1))^J.card ∧
      ∃ a : J → ℤ, ∀ S : J, |ξ S-(a S : ℝ)/D| ≤
        multiaffineBiasBudget n ζ / ∏ g, (N g : ℝ) := by
  have h := exists_common_rational_approximations (fun S : J => ξ S)
    (fun S => booleanBlockPhase_bounded_stride_entry N s u ξ S (hJ S S.property) hs hR hζ hN hbias)
  simpa only [Fintype.card_coe] using h

theorem moderateBooleanBlock_bounded_stride_major_arc {n : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (N : Fin n → ℕ) (s : Fin n → Option α → ℕ) (M k : ℕ)
    (u : Fin n → Option α → ℝ) (w : ℝ) (ξ : Finset α → ℝ)
    (J : Finset (Finset α)) (hJ : ∀ S ∈ J, S.card ≤ n)
    (hs : ∀ g r, 0 < s g r) (hk : 0 < k) {R : ℝ} (hR : ∀ g r, (s g r : ℝ) ≤ R)
    {ζ : ℝ} (hζ : 0 < ζ) (hN : ∀ g, multiaffineBiasBudget n ζ ≤ N g)
    (hM : multiaffineBiasBudget n ζ ≤ M)
    (hbias : ζ ≤ ‖𝔼 c : Fin M, 𝔼 x : ∀ g, Option α → Fin (N g),
      character (((w+(k : ℝ)*(c.val : ℝ))*
        booleanBlockPhase ξ (fun g r => u g r+(s g r : ℝ)*((x g r).val : ℝ)) : ℝ) :
        CircleFourier.Circle)‖) :
    ∃ D : ℕ, 0 < D ∧ (D : ℝ) ≤ (multiaffineBiasBudget n ζ*((k : ℝ)*R^n))^J.card ∧
      ∃ a : J → ℤ, ∀ S : J, |ξ S-(a S : ℝ)/D| ≤
        multiaffineBiasBudget n ζ / (((k : ℝ)*M)*∏ g, (N g : ℝ)) := by
  have h := exists_common_rational_approximations (fun S : J => ξ S)
    (fun S => moderateBooleanBlock_bounded_stride_entry N s M k u w ξ S (hJ S S.property)
      hs hk hR hζ hN hM hbias)
  simpa only [Fintype.card_coe] using h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators
open CircleFourier

theorem weightedCubeBlock_major_arc {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (d : Fin (n + 1) → ScalarCubeLocalizationData I) (τ : Fin (n + 2) → ℝ)
    (hτ : ∀ j : Fin (n + 1), 0 < τ j.succ)
    (herror : ∀ j, (d j).error (τ j.succ) ≤ τ j.castSucc)
    (ξ : Finset I → ℝ) (J : Finset (Finset I)) (hJ : ∀ S ∈ J, S.card ≤ n + 1)
    {R : ℝ} (hR : ∀ j i, ((d j).modulus i : ℝ) ≤ R)
    (hN : ∀ j, multiaffineBiasBudget n (τ (Fin.last (n + 1))) ≤ (d j).cellLength)
    (hbias : τ 0 ≤ ‖(FiniteProbabilityWeights.pi (fun j => (d j).source)).complexMean
      (fun z => character ((booleanBlockPhase ξ (fun j i => (z j i : ℝ)) : ℝ) : CircleFourier.Circle))‖) :
    ∃ D : ℕ, 0 < D ∧
      (D : ℝ) ≤ (multiaffineBiasBudget n (τ (Fin.last (n + 1))) * R ^ (n + 1)) ^ J.card ∧
      ∃ a : J → ℤ, ∀ S : J, |ξ S - (a S : ℝ) / D| ≤
        multiaffineBiasBudget n (τ (Fin.last (n + 1))) / ∏ j, ((d j).cellLength : ℝ) := by
  let F : (Fin (n + 1) → Option I → ℝ) → ℂ := fun x =>
    character ((booleanBlockPhase ξ (fun j i => ((d j).length : ℝ) * x j i) : ℝ) : CircleFourier.Circle)
  have hF (x) : ‖F x‖ ≤ 1 := le_of_eq (norm_character _)
  have hsourceeq : (fun z : ∀ j, IntegerScalarCubeBox I (d j).length => F (fun j => (d j).point (z j))) =
      (fun z => character ((booleanBlockPhase ξ (fun j i => (z j i : ℝ)) : ℝ) : CircleFourier.Circle)) := by
    funext z
    have hx : (fun j i => ((d j).length : ℝ) * (d j).point (z j) i) =
        (fun j i => (z j i : ℝ)) := by
      funext j i
      exact (d j).point_scale (z j) i
    dsimp only [F]
    rw [hx]
  have hs : τ 0 ≤ ‖(FiniteProbabilityWeights.pi (fun j => (d j).source)).complexMean
      (fun z => F (fun j => (d j).point (z j)))‖ := by
    rwa [hsourceeq]
  obtain ⟨k, _, hphase⟩ := scalarCubeFamily_localize (fun _ => I) d τ hτ herror F hF hs
  have hcell (t : ∀ j, Option I → Fin (d j).cellLength) :
      F (fun j => (d j).cell (k j) (t j)) =
      character ((booleanBlockPhase ξ (fun j i => (d j).integerOffset (k j) i +
        ((d j).modulus i : ℝ) * (t j i).val) : ℝ) : CircleFourier.Circle) := by
    have hx : (fun j i => ((d j).length : ℝ) * (d j).cell (k j) (t j) i) =
        (fun j i => (d j).integerOffset (k j) i + ((d j).modulus i : ℝ) * (t j i).val) := by
      funext j
      exact (d j).cell_scale (k j) (t j)
    dsimp only [F]
    rw [hx]
  have hm := Finset.expect_congr (s := Finset.univ) rfl (fun t _ => hcell t)
  have hp := hphase.trans_eq (congrArg norm hm)
  exact booleanBlockPhase_bounded_stride_major_arc (fun j => (d j).cellLength)
    (fun j => (d j).modulus) (fun j => (d j).integerOffset (k j)) ξ J hJ
    (fun j => (d j).modulus_pos) hR (hτ (Fin.last n)) hN hp

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators
open CircleFourier

theorem weightedModerateBlock_major_arc {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (c : ScalarCubeLocalizationData Empty) (d : Fin n → ScalarCubeLocalizationData I)
    (τ : Fin (n + 2) → ℝ) (hτ : ∀ j : Fin (n + 1), 0 < τ j.succ)
    (hc : c.error (τ 1) ≤ τ 0)
    (hd : ∀ j : Fin n, (d j).error (τ j.succ.succ) ≤ τ j.castSucc.succ)
    (shift : ℝ) (ξ : Finset I → ℝ) (J : Finset (Finset I)) (hJ : ∀ S ∈ J, S.card ≤ n)
    {R : ℝ} (hR : ∀ j i, ((d j).modulus i : ℝ) ≤ R)
    (hN : ∀ j, multiaffineBiasBudget n (τ (Fin.last (n + 1))) ≤ (d j).cellLength)
    (hM : multiaffineBiasBudget n (τ (Fin.last (n + 1))) ≤ c.cellLength)
    (hbias : τ 0 ≤ ‖c.source.complexMean (fun z =>
      (FiniteProbabilityWeights.pi (fun j => (d j).source)).complexMean
        (fun x => character (((shift + (z none : ℝ)) *
          booleanBlockPhase ξ (fun j i => (x j i : ℝ)) : ℝ) : CircleFourier.Circle)))‖) :
    ∃ D : ℕ, 0 < D ∧
      (D : ℝ) ≤ (multiaffineBiasBudget n (τ (Fin.last (n + 1))) *
        ((c.modulus none : ℝ) * R ^ n)) ^ J.card ∧
      ∃ a : J → ℤ, ∀ S : J, |ξ S - (a S : ℝ) / D| ≤
        multiaffineBiasBudget n (τ (Fin.last (n + 1))) /
          (((c.modulus none : ℝ) * c.cellLength) * ∏ j, ((d j).cellLength : ℝ)) := by
  let F : (Option Empty → ℝ) → (Fin n → Option I → ℝ) → ℂ := fun z x =>
    character (((shift + (c.length : ℝ) * z none) *
      booleanBlockPhase ξ (fun j i => ((d j).length : ℝ) * x j i) : ℝ) : CircleFourier.Circle)
  have hF (z x) : ‖F z x‖ ≤ 1 := le_of_eq (norm_character _)
  have hsource (z : IntegerScalarCubeBox Empty c.length)
      (x : ∀ j, IntegerScalarCubeBox I (d j).length) : F (c.point z) (fun j => (d j).point (x j)) =
      character (((shift + (z none : ℝ)) *
        booleanBlockPhase ξ (fun j i => (x j i : ℝ)) : ℝ) : CircleFourier.Circle) := by
    have hx : (fun j i => ((d j).length : ℝ) * (d j).point (x j) i) =
        (fun j i => (x j i : ℝ)) := by
      funext j i
      exact (d j).point_scale (x j) i
    dsimp only [F]
    rw [c.point_scale, hx]
  have hs : τ 0 ≤ ‖c.source.complexMean (fun z =>
      (FiniteProbabilityWeights.pi (fun j => (d j).source)).complexMean
        (fun x => F (c.point z) (fun j => (d j).point (x j))))‖ := by
    simpa only [hsource] using hbias
  obtain ⟨a, k, _, _, hphase⟩ := coefficientCubeFamily_localize c d τ hτ hc hd F hF hs
  have hcell (t : Option Empty → Fin c.cellLength) (u : ∀ j, Option I → Fin (d j).cellLength) :
      F (c.cell a t) (fun j => (d j).cell (k j) (u j)) =
      character (((shift + c.integerOffset a none + (c.modulus none : ℝ) * (t none).val) *
        booleanBlockPhase ξ (fun j i => (d j).integerOffset (k j) i +
          ((d j).modulus i : ℝ) * (u j i).val) : ℝ) : CircleFourier.Circle) := by
    have hx : (fun j i => ((d j).length : ℝ) * (d j).cell (k j) (u j) i) =
        (fun j i => (d j).integerOffset (k j) i + ((d j).modulus i : ℝ) * (u j i).val) := by
      funext j
      exact (d j).cell_scale (k j) (u j)
    have hz := congrFun (c.cell_scale a t) none
    dsimp only [F]
    rw [hz, hx, ← add_assoc]
  have hm := Finset.expect_congr (s := Finset.univ) rfl
    (fun t _ => Finset.expect_congr (s := Finset.univ) rfl (fun u _ => hcell t u))
  have hp := hphase.trans_eq (congrArg norm hm)
  rw [expect_emptyCubeCoordinate (fun t : Fin c.cellLength =>
    𝔼 u : ∀ j, Option I → Fin (d j).cellLength,
      character (((shift + c.integerOffset a none + (c.modulus none : ℝ) * t.val) *
        booleanBlockPhase ξ (fun j i => (d j).integerOffset (k j) i +
          ((d j).modulus i : ℝ) * (u j i).val) : ℝ) : CircleFourier.Circle))] at hp
  exact moderateBooleanBlock_bounded_stride_major_arc (fun j => (d j).cellLength)
    (fun j => (d j).modulus) c.cellLength (c.modulus none)
    (fun j => (d j).integerOffset (k j)) (shift + c.integerOffset a none) ξ J hJ
    (fun j => (d j).modulus_pos) (c.modulus_pos none) hR (hτ (Fin.last n)) hN hM hp

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators
open CircleFourier

theorem affine_weightedCubeBlock_major_arc {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (d : Fin (n + 1) → ScalarCubeLocalizationData I) (τ : Fin (n + 2) → ℝ)
    (hτ : ∀ j : Fin (n + 1), 0 < τ j.succ)
    (herror : ∀ j, (d j).error (τ j.succ) ≤ τ j.castSucc)
    (u : Fin (n + 1) → Option I → ℝ) (v : Fin (n + 1) → Option I → ℕ)
    (hv : ∀ j i, 0 < v j i) (ξ : Finset I → ℝ)
    (J : Finset (Finset I)) (hJ : ∀ S ∈ J, S.card ≤ n + 1)
    {R : ℝ} (hR : ∀ j i, ((v j i * (d j).modulus i : ℕ) : ℝ) ≤ R)
    (hN : ∀ j, multiaffineBiasBudget n (τ (Fin.last (n + 1))) ≤ (d j).cellLength)
    (hbias : τ 0 ≤ ‖(FiniteProbabilityWeights.pi (fun j => (d j).source)).complexMean
      (fun z => character ((booleanBlockPhase ξ
        (fun j => affineCubeCoordinates (u j) (v j) (fun i => (z j i : ℝ))) : ℝ) : CircleFourier.Circle))‖) :
    ∃ D : ℕ, 0 < D ∧
      (D : ℝ) ≤ (multiaffineBiasBudget n (τ (Fin.last (n + 1))) * R ^ (n + 1)) ^ J.card ∧
      ∃ a : J → ℤ, ∀ S : J, |ξ S - (a S : ℝ) / D| ≤
        multiaffineBiasBudget n (τ (Fin.last (n + 1))) / ∏ j, ((d j).cellLength : ℝ) := by
  let F : (Fin (n + 1) → Option I → ℝ) → ℂ := fun x => character ((booleanBlockPhase ξ
    (fun j => affineCubeCoordinates (u j) (v j) (fun i => ((d j).length : ℝ) * x j i)) : ℝ) : CircleFourier.Circle)
  have hF (x) : ‖F x‖ ≤ 1 := le_of_eq (norm_character _)
  have hsource (z : ∀ j, IntegerScalarCubeBox I (d j).length) :
      F (fun j => (d j).point (z j)) = character ((booleanBlockPhase ξ
        (fun j => affineCubeCoordinates (u j) (v j) (fun i => (z j i : ℝ))) : ℝ) : CircleFourier.Circle) := by
    dsimp only [F]
    simp only [ScalarCubeLocalizationData.affine_point_scale]
  have hs : τ 0 ≤ ‖(FiniteProbabilityWeights.pi (fun j => (d j).source)).complexMean
      (fun z => F (fun j => (d j).point (z j)))‖ := by simpa only [hsource] using hbias
  obtain ⟨k, _, hphase⟩ := scalarCubeFamily_localize (fun _ => I) d τ hτ herror F hF hs
  have hcell (t : ∀ j, Option I → Fin (d j).cellLength) :
      F (fun j => (d j).cell (k j) (t j)) = character ((booleanBlockPhase ξ (fun j i =>
        (u j i + (v j i : ℝ) * (d j).integerOffset (k j) i) +
          ((v j i * (d j).modulus i : ℕ) : ℝ) * (t j i).val) : ℝ) : CircleFourier.Circle) := by
    dsimp only [F]
    simp only [ScalarCubeLocalizationData.affine_cell_scale]
  have hm := Finset.expect_congr (s := Finset.univ) rfl (fun t _ => hcell t)
  have hp := hphase.trans_eq (congrArg norm hm)
  exact booleanBlockPhase_bounded_stride_major_arc (fun j => (d j).cellLength)
    (fun j i => v j i * (d j).modulus i)
    (fun j i => u j i + (v j i : ℝ) * (d j).integerOffset (k j) i) ξ J hJ
    (fun j i => Nat.mul_pos (hv j i) ((d j).modulus_pos i)) hR (hτ (Fin.last n)) hN hp

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators
open CircleFourier

theorem affine_weightedModerateBlock_major_arc {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (c : ScalarCubeLocalizationData Empty) (d : Fin n → ScalarCubeLocalizationData I)
    (τ : Fin (n + 2) → ℝ) (hτ : ∀ j : Fin (n + 1), 0 < τ j.succ)
    (hc : c.error (τ 1) ≤ τ 0)
    (hd : ∀ j : Fin n, (d j).error (τ j.succ.succ) ≤ τ j.castSucc.succ)
    (shift : ℝ) (t : ℕ) (ht : 0 < t) (u : Fin n → Option I → ℝ) (v : Fin n → Option I → ℕ)
    (hv : ∀ j i, 0 < v j i) (ξ : Finset I → ℝ) (J : Finset (Finset I)) (hJ : ∀ S ∈ J, S.card ≤ n)
    {R : ℝ} (hR : ∀ j i, ((v j i * (d j).modulus i : ℕ) : ℝ) ≤ R)
    (hN : ∀ j, multiaffineBiasBudget n (τ (Fin.last (n + 1))) ≤ (d j).cellLength)
    (hM : multiaffineBiasBudget n (τ (Fin.last (n + 1))) ≤ c.cellLength)
    (hbias : τ 0 ≤ ‖c.source.complexMean (fun z =>
      (FiniteProbabilityWeights.pi (fun j => (d j).source)).complexMean (fun x => character
        (((shift + (t : ℝ) * (z none : ℝ)) * booleanBlockPhase ξ
          (fun j => affineCubeCoordinates (u j) (v j) (fun i => (x j i : ℝ))) : ℝ) : CircleFourier.Circle)))‖) :
    ∃ D : ℕ, 0 < D ∧
      (D : ℝ) ≤ (multiaffineBiasBudget n (τ (Fin.last (n + 1))) *
        (((t * c.modulus none : ℕ) : ℝ) * R ^ n)) ^ J.card ∧
      ∃ a : J → ℤ, ∀ S : J, |ξ S - (a S : ℝ) / D| ≤
        multiaffineBiasBudget n (τ (Fin.last (n + 1))) /
          ((((t * c.modulus none : ℕ) : ℝ) * c.cellLength) * ∏ j, ((d j).cellLength : ℝ)) := by
  let F : (Option Empty → ℝ) → (Fin n → Option I → ℝ) → ℂ := fun z x => character
    (((shift + (t : ℝ) * ((c.length : ℝ) * z none)) * booleanBlockPhase ξ
      (fun j => affineCubeCoordinates (u j) (v j) (fun i => ((d j).length : ℝ) * x j i)) : ℝ) : CircleFourier.Circle)
  have hF (z x) : ‖F z x‖ ≤ 1 := le_of_eq (norm_character _)
  have hsource (z : IntegerScalarCubeBox Empty c.length) (x : ∀ j, IntegerScalarCubeBox I (d j).length) :
      F (c.point z) (fun j => (d j).point (x j)) = character
        (((shift + (t : ℝ) * (z none : ℝ)) * booleanBlockPhase ξ
          (fun j => affineCubeCoordinates (u j) (v j) (fun i => (x j i : ℝ))) : ℝ) : CircleFourier.Circle) := by
    dsimp only [F]
    rw [c.point_scale]
    simp only [ScalarCubeLocalizationData.affine_point_scale]
  have hs : τ 0 ≤ ‖c.source.complexMean (fun z =>
      (FiniteProbabilityWeights.pi (fun j => (d j).source)).complexMean
        (fun x => F (c.point z) (fun j => (d j).point (x j))))‖ := by simpa only [hsource] using hbias
  obtain ⟨a, k, _, _, hphase⟩ := coefficientCubeFamily_localize c d τ hτ hc hd F hF hs
  have hcell (z : Option Empty → Fin c.cellLength) (x : ∀ j, Option I → Fin (d j).cellLength) :
      F (c.cell a z) (fun j => (d j).cell (k j) (x j)) = character
        (((shift + (t : ℝ) * c.integerOffset a none + ((t * c.modulus none : ℕ) : ℝ) * (z none).val) *
          booleanBlockPhase ξ (fun j i => (u j i + (v j i : ℝ) * (d j).integerOffset (k j) i) +
            ((v j i * (d j).modulus i : ℕ) : ℝ) * (x j i).val) : ℝ) : CircleFourier.Circle) := by
    dsimp only [F]
    rw [congrFun (c.cell_scale a z) none]
    simp only [ScalarCubeLocalizationData.affine_cell_scale]
    congr 2
    push_cast
    ring
  have hm := Finset.expect_congr (s := Finset.univ) rfl
    (fun z _ => Finset.expect_congr (s := Finset.univ) rfl (fun x _ => hcell z x))
  have hp := hphase.trans_eq (congrArg norm hm)
  rw [expect_emptyCubeCoordinate (fun z : Fin c.cellLength =>
    𝔼 x : ∀ j, Option I → Fin (d j).cellLength, character
      (((shift + (t : ℝ) * c.integerOffset a none + ((t * c.modulus none : ℕ) : ℝ) * z.val) *
        booleanBlockPhase ξ (fun j i => (u j i + (v j i : ℝ) * (d j).integerOffset (k j) i) +
          ((v j i * (d j).modulus i : ℕ) : ℝ) * (x j i).val) : ℝ) : CircleFourier.Circle))] at hp
  exact moderateBooleanBlock_bounded_stride_major_arc (fun j => (d j).cellLength)
    (fun j i => v j i * (d j).modulus i) c.cellLength (t * c.modulus none)
    (fun j i => u j i + (v j i : ℝ) * (d j).integerOffset (k j) i)
    (shift + (t : ℝ) * c.integerOffset a none) ξ J hJ
    (fun j i => Nat.mul_pos (hv j i) ((d j).modulus_pos i)) (Nat.mul_pos ht (c.modulus_pos none))
    hR (hτ (Fin.last n)) hN hM hp

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

namespace NormalizedScalarCubeSource

variable {I : Type*} [Fintype I] [DecidableEq I] (s : NormalizedScalarCubeSource I)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {n : ℕ} {U ζ : ℝ}
    (h : ScalarCubePrimitiveBudget s A U) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hlen : localizedMajorArcLengthBudget n U ζ ≤ s.length)

noncomputable def majorArcLocalizationData : ScalarCubeLocalizationData I :=
  s.polynomialLocalizationData A hA h (localizationThreshold_pos h.one_le hζ (n + 1))
    (localizationThreshold_le_one h.one_le hζ hζ1 (n + 1))
    (by linarith [localizedMajorArcBudget_pos n h.one_le hζ]) hlen

theorem majorArcLocalizationData_source :
    (s.majorArcLocalizationData A hA h hζ hζ1 hlen).source = s.source := rfl

theorem majorArcLocalizationData_cellLength :
    localizedMajorArcBudget n U ζ ≤
      ((s.majorArcLocalizationData A hA h hζ hζ1 hlen).cellLength : ℝ) := by
  exact (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)).trans
    (s.polynomialLocalizationData_cellLength A hA h
      (localizationThreshold_pos h.one_le hζ (n + 1))
      (localizationThreshold_le_one h.one_le hζ hζ1 (n + 1))
      (by linarith [localizedMajorArcBudget_pos n h.one_le hζ]) hlen)

theorem majorArcLocalizationData_error {i : ℕ} (hi : i + 1 ≤ n + 1) :
    (s.majorArcLocalizationData A hA h hζ hζ1 hlen).error (localizationThreshold U ζ (i + 1)) ≤
      localizationThreshold U ζ i := by
  exact (s.polynomialLocalizationData_error A hA h
    (localizationThreshold_pos h.one_le hζ (n + 1))
    (localizationThreshold_le_one h.one_le hζ hζ1 (n + 1))
    (by linarith [localizedMajorArcBudget_pos n h.one_le hζ]) hlen
    (localizationThreshold_pos h.one_le hζ (i + 1)).le).trans
      (localizationThreshold_step h.one_le hζ hi)

theorem majorArcLocalizationData_lengthLoss :
    (s.majorArcLocalizationData A hA h hζ hζ1 hlen).lengthLoss ≤
      localizationLengthBudget U (localizationThreshold U ζ (n + 1)) 1 :=
  s.polynomialLocalizationData_lengthLoss A hA h
    (localizationThreshold_pos h.one_le hζ (n + 1))
    (localizationThreshold_le_one h.one_le hζ hζ1 (n + 1))
    (by linarith [localizedMajorArcBudget_pos n h.one_le hζ]) hlen

end NormalizedScalarCubeSource
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal
open CircleFourier

theorem polynomial_affine_weightedCubeBlock_major_arc {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (s : Fin (n + 1) → NormalizedScalarCubeSource I)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {U ζ : ℝ}
    (h : ∀ j, ScalarCubePrimitiveBudget (s j) A U) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hlen : ∀ j, localizedMajorArcLengthBudget n U ζ ≤ (s j).length)
    (u : Fin (n + 1) → Option I → ℝ) (v : Fin (n + 1) → Option I → ℕ)
    (hv : ∀ j i, 0 < v j i) (hstride : ∀ j i, ((v j i * (s j).modulus i : ℕ) : ℝ) ≤ U)
    (ξ : Finset I → ℝ) (J : Finset (Finset I)) (hJ : ∀ S ∈ J, S.card ≤ n + 1)
    (hbias : ζ ≤ ‖(FiniteProbabilityWeights.pi (fun j => (s j).source)).complexMean
      (fun z => character ((booleanBlockPhase ξ
        (fun j => affineCubeCoordinates (u j) (v j) (fun i => (z j i : ℝ))) : ℝ) : CircleFourier.Circle))‖) :
    ∃ D : ℕ, 0 < D ∧
      (D : ℝ) ≤ (localizedMajorArcBudget n U ζ * U ^ (n + 1)) ^ J.card ∧
      ∃ a : J → ℤ, ∀ S : J, |ξ S - (a S : ℝ) / D| ≤
        localizedMajorArcErrorBudget n U ζ / ∏ j, ((s j).length : ℝ) := by
  let d j := (s j).majorArcLocalizationData A hA (h j) hζ hζ1 (hlen j)
  let τ : Fin (n + 2) → ℝ := fun i => localizationThreshold U ζ i.val
  have hU := (h 0).one_le
  have hτ (j : Fin (n + 1)) : 0 < τ j.succ := localizationThreshold_pos hU hζ _
  have herr (j : Fin (n + 1)) : (d j).error (τ j.succ) ≤ τ j.castSucc :=
    (s j).majorArcLocalizationData_error A hA (h j) hζ hζ1 (hlen j) (by omega)
  have hN (j : Fin (n + 1)) : multiaffineBiasBudget n (τ (Fin.last (n + 1))) ≤ (d j).cellLength :=
    (s j).majorArcLocalizationData_cellLength A hA (h j) hζ hζ1 (hlen j)
  have hb : τ 0 ≤ ‖(FiniteProbabilityWeights.pi (fun j => (d j).source)).complexMean
      (fun z => character ((booleanBlockPhase ξ
        (fun j => affineCubeCoordinates (u j) (v j) (fun i => (z j i : ℝ))) : ℝ) : CircleFourier.Circle))‖ := by
    change localizationThreshold U ζ 0 ≤ _
    rw [localizationThreshold_zero]
    exact hbias
  obtain ⟨D, hD, hDb, a, ha⟩ := affine_weightedCubeBlock_major_arc d τ hτ herr u v hv ξ J hJ hstride hN hb
  refine ⟨D, hD, hDb, a, fun S => (ha S).trans ?_⟩
  have he := polynomialScalarCube_inverse_product (fun _ : Fin (n + 1) => I) s A hA h
    (localizationThreshold_pos hU hζ (n + 1))
    (localizationThreshold_le_one hU hζ hζ1 (n + 1))
    (by linarith [localizedMajorArcBudget_pos n hU hζ]) hlen
    (localizedMajorArcBudget_pos n hU hζ).le
  simpa only [Fintype.card_fin, localizedMajorArcErrorBudget, localizedMajorArcBudget,
    τ, Fin.val_last, d, NormalizedScalarCubeSource.majorArcLocalizationData] using he

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal
open CircleFourier

theorem polynomial_affine_weightedModerateBlock_major_arc {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (c : NormalizedScalarCubeSource Empty) (s : Fin n → NormalizedScalarCubeSource I)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {U ζ : ℝ}
    (hc : ScalarCubePrimitiveBudget c A U) (h : ∀ j, ScalarCubePrimitiveBudget (s j) A U)
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hclen : localizedMajorArcLengthBudget n U ζ ≤ c.length)
    (hlen : ∀ j, localizedMajorArcLengthBudget n U ζ ≤ (s j).length)
    (shift : ℝ) (t : ℕ) (ht : 0 < t)
    (u : Fin n → Option I → ℝ) (v : Fin n → Option I → ℕ)
    (hv : ∀ j i, 0 < v j i) (hstride : ∀ j i, ((v j i * (s j).modulus i : ℕ) : ℝ) ≤ U)
    (ξ : Finset I → ℝ) (J : Finset (Finset I)) (hJ : ∀ S ∈ J, S.card ≤ n)
    (hbias : ζ ≤ ‖c.source.complexMean (fun z =>
      (FiniteProbabilityWeights.pi (fun j => (s j).source)).complexMean
        (fun x => character (((shift + (t : ℝ) * (z none : ℝ)) *
          booleanBlockPhase ξ (fun j => affineCubeCoordinates (u j) (v j) (fun i => (x j i : ℝ))) : ℝ) : CircleFourier.Circle)))‖) :
    ∃ D : ℕ, 0 < D ∧
      (D : ℝ) ≤ (localizedMajorArcBudget n U ζ * (((t * c.modulus none : ℕ) : ℝ) * U ^ n)) ^ J.card ∧
      ∃ a : J → ℤ, ∀ S : J, |ξ S - (a S : ℝ) / D| ≤
        localizedMajorArcErrorBudget n U ζ /
          ((((t * c.modulus none : ℕ) : ℝ) * c.length) * ∏ j, ((s j).length : ℝ)) := by
  let d j := (s j).majorArcLocalizationData A hA (h j) hζ hζ1 (hlen j)
  let e := c.majorArcLocalizationData A hA hc hζ hζ1 hclen
  let τ : Fin (n + 2) → ℝ := fun i => localizationThreshold U ζ i.val
  have hτ (j : Fin (n + 1)) : 0 < τ j.succ := localizationThreshold_pos hc.one_le hζ _
  have he : e.error (τ 1) ≤ τ 0 := by
    simpa only [τ, Fin.val_one, Fin.val_zero] using
      c.majorArcLocalizationData_error A hA hc hζ hζ1 hclen (i := 0) (by omega)
  have hd (j : Fin n) : (d j).error (τ j.succ.succ) ≤ τ j.castSucc.succ :=
    (s j).majorArcLocalizationData_error A hA (h j) hζ hζ1 (hlen j) (by omega)
  have hR (j : Fin n) (i : Option I) : ((v j i * (d j).modulus i : ℕ) : ℝ) ≤ U :=
    hstride j i
  have hN (j : Fin n) : multiaffineBiasBudget n (τ (Fin.last (n + 1))) ≤ (d j).cellLength :=
    (s j).majorArcLocalizationData_cellLength A hA (h j) hζ hζ1 (hlen j)
  have hM : multiaffineBiasBudget n (τ (Fin.last (n + 1))) ≤ e.cellLength :=
    c.majorArcLocalizationData_cellLength A hA hc hζ hζ1 hclen
  have hb : τ 0 ≤ ‖e.source.complexMean (fun z =>
      (FiniteProbabilityWeights.pi (fun j => (d j).source)).complexMean
        (fun x => character (((shift + (t : ℝ) * (z none : ℝ)) *
          booleanBlockPhase ξ (fun j => affineCubeCoordinates (u j) (v j) (fun i => (x j i : ℝ))) : ℝ) : CircleFourier.Circle)))‖ := by
    change localizationThreshold U ζ 0 ≤ _
    rw [localizationThreshold_zero]
    exact hbias
  obtain ⟨D, hD, hDb, a, ha⟩ := affine_weightedModerateBlock_major_arc e d τ hτ he hd shift t ht u v hv ξ J hJ hR hN hM hb
  refine ⟨D, hD, hDb, a, fun S => (ha S).trans ?_⟩
  have hcloss := c.majorArcLocalizationData_lengthLoss A hA hc hζ hζ1 hclen
  have hsloss j := (s j).majorArcLocalizationData_lengthLoss A hA (h j) hζ hζ1 (hlen j)
  apply coefficient_inverse_product_le (fun j => ((s j).length : ℝ))
    (fun j => ((d j).cellLength : ℝ))
    (by exact_mod_cast c.length_pos) (by exact_mod_cast e.cellLength_pos)
    (by exact_mod_cast Nat.mul_pos ht (c.modulus_pos none))
    (fun j => by exact_mod_cast (s j).length_pos)
    (fun j => by exact_mod_cast (d j).cellLength_pos)
    (e.length_le_lengthLoss_mul_cellLength.trans
      (mul_le_mul_of_nonneg_right hcloss (Nat.cast_nonneg _)))
    (fun j => (d j).length_le_lengthLoss_mul_cellLength.trans
      (mul_le_mul_of_nonneg_right (hsloss j) (Nat.cast_nonneg _)))
    (localizedMajorArcBudget_pos n hc.one_le hζ).le

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal
open CircleFourier

theorem polynomial_weightedCubeBlock_major_arc {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (s : Fin (n + 1) → NormalizedScalarCubeSource I)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {U ζ : ℝ}
    (h : ∀ j, ScalarCubePrimitiveBudget (s j) A U) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hlen : ∀ j, localizedMajorArcLengthBudget n U ζ ≤ (s j).length)
    (ξ : Finset I → ℝ) (J : Finset (Finset I)) (hJ : ∀ S ∈ J, S.card ≤ n + 1)
    (hbias : ζ ≤ ‖(FiniteProbabilityWeights.pi (fun j => (s j).source)).complexMean
      (fun z => character ((booleanBlockPhase ξ (fun j i => (z j i : ℝ)) : ℝ) : CircleFourier.Circle))‖) :
    ∃ D : ℕ, 0 < D ∧
      (D : ℝ) ≤ (localizedMajorArcBudget n U ζ * U ^ (n + 1)) ^ J.card ∧
      ∃ a : J → ℤ, ∀ S : J, |ξ S - (a S : ℝ) / D| ≤
        localizedMajorArcErrorBudget n U ζ / ∏ j, ((s j).length : ℝ) := by
  let d j := (s j).majorArcLocalizationData A hA (h j) hζ hζ1 (hlen j)
  let τ : Fin (n + 2) → ℝ := fun i => localizationThreshold U ζ i.val
  have hU := (h 0).one_le
  have hτ (j : Fin (n + 1)) : 0 < τ j.succ := localizationThreshold_pos hU hζ _
  have herr (j : Fin (n + 1)) : (d j).error (τ j.succ) ≤ τ j.castSucc :=
    (s j).majorArcLocalizationData_error A hA (h j) hζ hζ1 (hlen j) (by omega)
  have hR (j : Fin (n + 1)) (i : Option I) : ((d j).modulus i : ℝ) ≤ U :=
    (by exact_mod_cast (s j).modulus_le i : ((s j).modulus i : ℝ) ≤ (s j).modulusBound).trans
      (h j).modulus_le
  have hN (j : Fin (n + 1)) : multiaffineBiasBudget n (τ (Fin.last (n + 1))) ≤ (d j).cellLength :=
    (s j).majorArcLocalizationData_cellLength A hA (h j) hζ hζ1 (hlen j)
  have hb : τ 0 ≤ ‖(FiniteProbabilityWeights.pi (fun j => (d j).source)).complexMean
      (fun z => character ((booleanBlockPhase ξ (fun j i => (z j i : ℝ)) : ℝ) : CircleFourier.Circle))‖ := by
    change localizationThreshold U ζ 0 ≤ _
    rw [localizationThreshold_zero]
    exact hbias
  obtain ⟨D, hD, hDb, a, ha⟩ := weightedCubeBlock_major_arc d τ hτ herr ξ J hJ hR hN hb
  refine ⟨D, hD, hDb, a, fun S => (ha S).trans ?_⟩
  have he := polynomialScalarCube_inverse_product (fun _ : Fin (n + 1) => I) s A hA h
    (localizationThreshold_pos hU hζ (n + 1))
    (localizationThreshold_le_one hU hζ hζ1 (n + 1))
    (by linarith [localizedMajorArcBudget_pos n hU hζ]) hlen
    (localizedMajorArcBudget_pos n hU hζ).le
  simpa only [Fintype.card_fin, localizedMajorArcErrorBudget, localizedMajorArcBudget,
    τ, Fin.val_last, d, NormalizedScalarCubeSource.majorArcLocalizationData] using he

end Erdos3

end

end OAI
