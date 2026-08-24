import GowersSzemeredi.Proofs07AdditiveRestriction
import GowersSzemeredi.Proofs16BaseCaseCore

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
  let y : Fin 1 → Point N 1 := fun _ => 0
  have h := hproduct 1 0 y (pointOneDomain B) (fun _ => (1 : Real))
    (fun _ => by positivity)
  have hmem : ∀ (i : Fin 1) z, z ∈ pointOneDomain B →
      replaceCoordinate (y i) 0 z ∈ B := by
    intro i z hz
    rw [replaceCoordinate_one]
    exact (mem_pointOneDomain B z).1 hz
  specialize h hmem
  have henergy :
      weightedSimultaneousAdditiveEnergy (pointOneDomain B)
          (fun _ => (1 : Real))
          (fun i => coordinateRestriction phi (y i) 0) =
        (phiAdditiveCount (pointOneDomain B) (pointOneMap phi) : Nat) := by
    classical
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
  classical
  let beta : Real := (B.card : Real) / N
  have hNposNat : 0 < N := NeZero.pos N
  have hNpos : (0 : Real) < N := by exact_mod_cast hNposNat
  have hbeta : 0 < beta := by
    dsimp only [beta]
    have hBpos : (0 : Real) < B.card :=
      (mul_pos htheta hNpos).trans_le hBlarge
    positivity
  have hbetaLower : theta ≤ beta := by
    dsimp only [beta]
    exact (le_div_iff₀ hNpos).2 hBlarge
  have hBcard : (B.card : Real) = beta * N := by
    dsimp only [beta]
    field_simp [hNpos.ne']
  have hproduct := hrelation B phi hgraph
  have hadd0 := productProperty_one_additive gamma B phi hproduct
  have hadd :
      (gamma ^ (8 : Nat) * beta) * (beta * N) ^ 3 ≤
        phiAdditiveCount (pointOneDomain B) (pointOneMap phi) := by
    calc
      (gamma ^ (8 : Nat) * beta) * (beta * N) ^ 3 =
          gamma ^ (8 : Nat) * (N : Real)⁻¹ * (B.card : Real) ^ 4 := by
        rw [hBcard]
        field_simp [hNpos.ne']
      _ ≤ _ := hadd0
  obtain ⟨A, hAB, hAsize, hAfreiman⟩ :=
    corollary_7_6_holds N (pointOneDomain B) (pointOneMap phi) beta
      (gamma ^ (8 : Nat) * beta) hprime hbeta
      (mul_pos (pow_pos hgamma 8) hbeta)
      (by simpa [pointOneDomain_card] using hBcard) hadd
  let B' : Finset (Point N 1) :=
    A.map (pointOneEquiv N).symm.toEmbedding
  have hB'card : B'.card = A.card := by simp [B']
  have hB'sub : B' ⊆ B := by
    intro x hx
    dsimp only [B'] at hx
    rw [Finset.mem_map] at hx
    obtain ⟨z, hzA, hzx⟩ := hx
    have hzB := (mem_pointOneDomain B z).1 (hAB hzA)
    subst x
    change (pointOneEquiv N).symm z ∈ B
    exact hzB
  have hB'graph : GraphContained B' phi Gamma := by
    intro x hx
    exact hgraph x (hB'sub hx)
  have hsize : lemma163Alpha gamma theta * N ≤ B'.card := by
    rw [hB'card]
    calc
      lemma163Alpha gamma theta * N ≤
          (2 : Real) ^ (-(1882 : Real)) *
            (gamma ^ (8 : Nat) * beta) ^ (1164 : Nat) * beta * N := by
        unfold lemma163Alpha
        have hgammaNonneg : 0 ≤ gamma := hgamma.le
        have hthetaNonneg : 0 ≤ theta := htheta.le
        have hbetaNonneg : 0 ≤ beta := hbeta.le
        have htwo : (2 : Real) ^ (-(2000 : Real)) ≤
            (2 : Real) ^ (-(1882 : Real)) := by
          exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        have hgammaPow : gamma ^ (10000 : Nat) ≤ gamma ^ (9312 : Nat) := by
          exact pow_le_pow_of_le_one hgamma.le hgammaOne (by omega)
        have hthetaPow : theta ^ (10000 : Nat) ≤ beta ^ (1165 : Nat) := by
          calc
            theta ^ (10000 : Nat) ≤ theta ^ (1165 : Nat) :=
              pow_le_pow_of_le_one htheta.le hthetaOne (by omega)
            _ ≤ beta ^ (1165 : Nat) :=
              pow_le_pow_left₀ hthetaNonneg hbetaLower 1165
        have hgammaNested : gamma ^ (9312 : Nat) =
            (gamma ^ (8 : Nat)) ^ (1164 : Nat) := by
          simpa only [Nat.reduceMul] using (pow_mul gamma 8 1164)
        have hbetaSucc : beta ^ (1165 : Nat) =
            beta ^ (1164 : Nat) * beta := by
          simpa only [Nat.reduceAdd] using (pow_succ beta 1164)
        have hgammaPow' : gamma ^ (10000 : Nat) ≤
            (gamma ^ (8 : Nat)) ^ (1164 : Nat) :=
          hgammaPow.trans_eq hgammaNested
        have hthetaPow' : theta ^ (10000 : Nat) ≤
            beta ^ (1164 : Nat) * beta :=
          hthetaPow.trans_eq hbetaSucc
        have hproduct :
            (2 : Real) ^ (-(2000 : Real)) *
                (gamma ^ (10000 : Nat) * theta ^ (10000 : Nat)) ≤
              (2 : Real) ^ (-(1882 : Real)) *
                ((gamma ^ (8 : Nat)) ^ (1164 : Nat) *
                  (beta ^ (1164 : Nat) * beta)) := by
          exact mul_le_mul htwo
            (mul_le_mul hgammaPow' hthetaPow'
              (pow_nonneg hthetaNonneg 10000)
              (pow_nonneg (pow_nonneg hgammaNonneg 8) 1164))
            (mul_nonneg (pow_nonneg hgammaNonneg 10000)
              (pow_nonneg hthetaNonneg 10000))
            (Real.rpow_nonneg (by norm_num : (0 : Real) ≤ 2) (-(1882 : Real)))
        calc
          (2 : Real) ^ (-(2000 : Real)) * (gamma * theta) ^ (10000 : Nat) * N =
              (2 : Real) ^ (-(2000 : Real)) *
                (gamma ^ (10000 : Nat) * theta ^ (10000 : Nat)) * N := by
            rw [mul_pow]
          _ ≤ (2 : Real) ^ (-(1882 : Real)) *
                ((gamma ^ (8 : Nat)) ^ (1164 : Nat) *
                  (beta ^ (1164 : Nat) * beta)) * N :=
            mul_le_mul_of_nonneg_right hproduct (by positivity)
          _ = (2 : Real) ^ (-(1882 : Real)) *
                (gamma ^ (8 : Nat) * beta) ^ (1164 : Nat) * beta * N := by
            rw [mul_pow]
            ac_rfl
      _ ≤ A.card := hAsize
  refine ⟨(B', phi), hsize, hB'graph, ?_⟩
  have hdomain : pointOneDomain B' = A := by
    apply Finset.Subset.antisymm
    · intro z hz
      rw [pointOneDomain, Finset.mem_map] at hz
      obtain ⟨x, hx, rfl⟩ := hz
      dsimp only [B'] at hx
      rw [Finset.mem_map] at hx
      obtain ⟨a, ha, rfl⟩ := hx
      simpa using ha
    · intro z hz
      rw [pointOneDomain, Finset.mem_map]
      refine ⟨(pointOneEquiv N).symm z, ?_, by simp⟩
      dsimp only [B']
      rw [Finset.mem_map]
      exact ⟨z, hz, rfl⟩
  rw [hdomain]
  exact hAfreiman

@[simp] lemma candidateGraph_card {N : Nat} [NeZero N]
    (C : BaseCandidate N) : (candidateGraph C).card = C.1.card := by
  classical
  unfold candidateGraph partialGraph
  rw [Finset.card_image_iff.mpr]
  intro x _ y _ hxy
  exact congrArg Prod.fst hxy


end LeanProofs.GowersSzemeredi.BaseCase
