import GowersSzemeredi.Proofs07AdditiveRestriction
import GowersSzemeredi.Section16

/-!
# The one-dimensional additive restriction for Lemma 16.3

This isolated slice transports the one-dimensional product property to the
additive-energy input of Corollary 7.6 and extracts one uniformly large
order-eight Freiman graph.  The finite greedy extraction is kept in the next
module-sized slice.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi.BaseCase

/-! ## One-dimensional transports -/

/-- Evaluation identifies a one-dimensional point with its only coordinate. -/
def pointOneEquiv (N : Nat) : Point N 1 ≃ ZMod N where
  toFun x := x 0
  invFun z := fun _ => z
  left_inv x := by funext i; fin_cases i; rfl
  right_inv z := rfl

noncomputable def pointOneDomain {N : Nat} [NeZero N]
    (B : Finset (Point N 1)) : Finset (ZMod N) :=
  B.map (pointOneEquiv N).toEmbedding

def pointOneMap {N : Nat} (phi : Point N 1 → ZMod N) :
    ZMod N → ZMod N :=
  fun z => phi ((pointOneEquiv N).symm z)

@[simp] lemma pointOneDomain_card {N : Nat} [NeZero N]
    (B : Finset (Point N 1)) : (pointOneDomain B).card = B.card := by
  simp [pointOneDomain]

@[simp] lemma mem_pointOneDomain {N : Nat} [NeZero N]
    (B : Finset (Point N 1)) (z : ZMod N) :
    z ∈ pointOneDomain B ↔ (pointOneEquiv N).symm z ∈ B := by
  simp [pointOneDomain]

/-- Candidate graph pieces produced by Corollary 7.6. -/
abbrev BaseCandidate (N : Nat) :=
  Finset (Point N 1) × (Point N 1 → ZMod N)

def candidateGraph {N : Nat} (C : BaseCandidate N) :
    Finset (Point N 1 × ZMod N) :=
  partialGraph C.1 C.2

def IsBaseCandidate {N : Nat} [NeZero N]
    (Gamma : Finset (Point N 1 × ZMod N)) (alpha : Real)
    (C : BaseCandidate N) : Prop :=
  alpha * N ≤ C.1.card ∧
  GraphContained C.1 C.2 Gamma ∧
  FreimanHom 8 (pointOneDomain C.1) (pointOneMap C.2)

def CandidateFamily {N : Nat} [NeZero N]
    (Gamma : Finset (Point N 1 × ZMod N)) (alpha : Real)
    (F : Finset (BaseCandidate N)) : Prop :=
  (∀ C, C ∈ F → IsBaseCandidate Gamma alpha C) ∧
  ∀ C, C ∈ F → ∀ D, D ∈ F → C ≠ D →
    Disjoint (candidateGraph C) (candidateGraph D)

lemma replaceCoordinate_one {N : Nat} (y : Point N 1) (z : ZMod N) :
    replaceCoordinate y 0 z = (pointOneEquiv N).symm z := by
  funext i
  fin_cases i
  simp [replaceCoordinate, pointOneEquiv]

lemma coordinateRestriction_one {N : Nat}
    (phi : Point N 1 → ZMod N) (y : Point N 1) :
    coordinateRestriction phi y 0 = pointOneMap phi := by
  funext z
  simp [coordinateRestriction, replaceCoordinate_one, pointOneMap]

/-- In one dimension the product property supplies exactly the additive-energy
input used by Corollary 7.6. -/
lemma productProperty_one_additive {N : Nat} [NeZero N]
    (gamma : Real) (B : Finset (Point N 1))
    (phi : Point N 1 → ZMod N) (hproduct : HasProductProperty B phi gamma) :
    gamma ^ (8 : Nat) * (N : Real)⁻¹ * (B.card : Real) ^ 4 ≤
      phiAdditiveCount (pointOneDomain B) (pointOneMap phi) := by
  classical
  have h := hproduct 1 0 (fun _ => 0) (pointOneDomain B) (fun _ => (1 : Real))
    (fun _ => zero_le_one) fun _ z hz => by
      rw [replaceCoordinate_one]; exact (mem_pointOneDomain B z).1 hz
  have henergy : weightedSimultaneousAdditiveEnergy (pointOneDomain B) (fun _ => (1 : Real))
      (fun _ : Fin 1 => coordinateRestriction phi 0 0) =
        (phiAdditiveCount (pointOneDomain B) (pointOneMap phi) : Nat) := by
    unfold weightedSimultaneousAdditiveEnergy phiAdditiveCount countWhere
    rw [Finset.filter_congr_decidable]
    simp only [coordinateRestriction_one]
    simp [IsPhiAdditive, IsAdditiveQuadruple]
  rw [henergy] at h
  simpa [pointOneDomain_card] using h

/-- The uniform density of every graph removed in the greedy extraction. -/
def lemma163Alpha (gamma theta : Real) : Real :=
  (2 : Real) ^ (-(2000 : Real)) * (gamma * theta) ^ (10000 : Nat)

lemma lemma163Alpha_pos {gamma theta : Real}
    (hgamma : 0 < gamma) (htheta : 0 < theta) :
    0 < lemma163Alpha gamma theta := by
  unfold lemma163Alpha
  positivity

/-- One pass through the argument: a graph selection on at least `theta*N`
base points contains a uniformly large order-eight Freiman restriction. -/
lemma section16_product_restriction {N : Nat} [NeZero N]
    (gamma theta : Real) (hgamma : 0 < gamma) (hgammaOne : gamma ≤ 1)
    (htheta : 0 < theta) (hthetaOne : theta ≤ 1)
    (hprime : N.Prime) (Gamma : Finset (Point N 1 × ZMod N))
    (hrelation : RelationProductProperty gamma Gamma)
    (B : Finset (Point N 1)) (phi : Point N 1 → ZMod N)
    (hBlarge : theta * N ≤ B.card)
    (hgraph : GraphContained B phi Gamma) :
    ∃ C : BaseCandidate N, IsBaseCandidate Gamma (lemma163Alpha gamma theta) C := by
  have hNpos : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  let beta : Real := (B.card : Real) / N
  have hbetaLower : theta ≤ beta := (le_div_iff₀ hNpos).2 hBlarge
  have hbeta : 0 < beta := htheta.trans_le hbetaLower
  have hBcard : (B.card : Real) = beta * N := (div_mul_cancel₀ _ hNpos.ne').symm
  -- Corollary 7.6 on the one-dimensional additive input
  have hadd : (gamma ^ (8 : Nat) * beta) * (beta * N) ^ 3 ≤
      phiAdditiveCount (pointOneDomain B) (pointOneMap phi) := by
    refine le_of_eq_of_le ?_ (productProperty_one_additive gamma B phi (hrelation B phi hgraph))
    rw [hBcard]
    field_simp [hNpos.ne']
  obtain ⟨A, hAB, hAsize, hAfreiman⟩ :=
    corollary_7_6_holds N (pointOneDomain B) (pointOneMap phi) beta
      (gamma ^ (8 : Nat) * beta) hprime hbeta (mul_pos (pow_pos hgamma 8) hbeta)
      (by simpa [pointOneDomain_card] using hBcard) hadd
  -- the extracted set, back in `Point N 1`
  let B' : Finset (Point N 1) := A.map (pointOneEquiv N).symm.toEmbedding
  have hB'card : B'.card = A.card := Finset.card_map _
  have hB'sub : B' ⊆ B := fun x hx => by
    obtain ⟨z, hzA, rfl⟩ := Finset.mem_map.mp hx
    exact (mem_pointOneDomain B z).1 (hAB hzA)
  -- `α ≤ 2^(-1882) (γ⁸β)^1164 β`, since `γ, θ ≤ 1` and `θ ≤ β`
  have hpow : (gamma * theta) ^ 10000 ≤ (gamma ^ 8 * beta) ^ 1164 * beta :=
    calc (gamma * theta) ^ 10000 = gamma ^ 10000 * theta ^ 10000 := mul_pow _ _ _
      _ ≤ gamma ^ 9312 * beta ^ 1165 :=
        mul_le_mul (pow_le_pow_of_le_one hgamma.le hgammaOne (by norm_num))
          ((pow_le_pow_of_le_one htheta.le hthetaOne (by norm_num)).trans
            (pow_le_pow_left₀ htheta.le hbetaLower _)) (by positivity) (by positivity)
      _ = (gamma ^ 8 * beta) ^ 1164 * beta := by ring
  have hsize : lemma163Alpha gamma theta * N ≤ B'.card := by
    rw [hB'card]
    calc lemma163Alpha gamma theta * N
        ≤ 2 ^ (-(1882 : Real)) * ((gamma ^ 8 * beta) ^ 1164 * beta) * N :=
          mul_le_mul_of_nonneg_right (mul_le_mul (Real.rpow_le_rpow_of_exponent_le (by norm_num)
            (by norm_num)) hpow (by positivity) (by positivity)) hNpos.le
      _ = 2 ^ (-(1882 : Real)) * (gamma ^ 8 * beta) ^ 1164 * beta * N := by ring
      _ ≤ A.card := hAsize
  refine ⟨(B', phi), hsize, fun x hx => hgraph x (hB'sub hx), ?_⟩
  rw [show pointOneDomain B' = A by ext z; simp [B']]
  exact hAfreiman

@[simp] lemma candidateGraph_card {N : Nat} [NeZero N]
    (C : BaseCandidate N) : (candidateGraph C).card = C.1.card := by
  unfold candidateGraph partialGraph
  rw [Finset.card_image_iff.mpr]
  intro x _ y _ hxy
  exact congrArg Prod.fst hxy


end LeanProofs.GowersSzemeredi.BaseCase
