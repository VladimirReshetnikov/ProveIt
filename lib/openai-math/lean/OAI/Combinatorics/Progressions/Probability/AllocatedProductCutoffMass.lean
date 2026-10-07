/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Sampling.AllocatedUniformGridVolumeCap

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

def allocatedCutoffMassLog {A : Type*} [Semiring A] (D F : A) : A :=
  D * (D * (2 * D + F + 11)) + D * (D + F + 4) + 3

theorem allocatedCutoffMassLog_nonneg {D F : ℝ} (hD : 0 ≤ D) (hF : 0 ≤ F) :
    0 ≤ allocatedCutoffMassLog D F := by
  unfold allocatedCutoffMassLog
  positivity

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] (rowSets : Fin m → Finset (Finset α))
variable {D F : ℝ}
variable (hgeom : AllocatedComparisonDimensions (G := G) B α (fun j => (rowSets j : Type _)) D)

include hgeom in
theorem allocatedUniformCutoffMass_exp_bound (r : ℝ≥0)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ D)
    (hF : 0 ≤ F) (hradius : 2 * (r : ℝ) ≤ Real.exp F)
    {η ε : ℝ} (hη : η ≤ 1) (hε : ε ≤ 1) :
    allocatedUniformGridVolumeCap B rowSets r *
      (2 * ((2 : ℝ) ^ Fintype.card α * (2 * (r : ℝ))) + 1) ^
        Fintype.card (Σ a : LayerSamplerAxis I n, (rowSets a.fst : Type _)) +
      2 * η + ε ≤ Real.exp (allocatedCutoffMassLog D F) := by
  have hD := hgeom.nonneg
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have height : (8 : ℝ) ≤ Real.exp 7 := by linarith [Real.add_one_le_exp (7 : ℝ)]
  have hbinary : (2 : ℝ) ^ Fintype.card α ≤ Real.exp D := by
    simpa only [mul_one] using pow_le_exp_mul_of_le_exp (by norm_num) htwo
      (by norm_num) (Fintype.card α) hgeom.cube
  have hblock (a : LayerSamplerAxis I n) : (Fintype.card (B a) : ℝ) ≤ D :=
    (Finset.single_le_sum (fun a _ => Nat.cast_nonneg (Fintype.card (B a)))
      (Finset.mem_univ a)).trans ((allocatedBlock_card_sum_le_variables (G := G) B).trans hvars)
  have hshort : (2 : ℝ) ^ Fintype.card α * (2 * (r : ℝ)) ≤ Real.exp (D + F) := by
    calc
      _ ≤ Real.exp D * Real.exp F := mul_le_mul hbinary hradius (by positivity) (Real.exp_pos _).le
      _ = _ := (Real.exp_add _ _).symm
  have hgridBase (a : LayerSamplerAxis I n) :
      2 * (((2 : ℝ) ^ Fintype.card α * (2 * (r : ℝ))) *
        (8 * ((Fintype.card (B a) : ℝ) + 1))) + 3 ≤ Real.exp (2 * D + F + 11) := by
    have hB : (Fintype.card (B a) : ℝ) + 1 ≤ Real.exp D := by
      linarith [hblock a, Real.add_one_le_exp D]
    have hinner : ((2 : ℝ) ^ Fintype.card α * (2 * (r : ℝ))) *
        (8 * ((Fintype.card (B a) : ℝ) + 1)) ≤ Real.exp (2 * D + F + 7) := by
      calc
        _ ≤ Real.exp (D + F) * (Real.exp 7 * Real.exp D) := by gcongr
        _ = _ := by simp only [← Real.exp_add]; congr 1; ring
    exact (two_mul_add_three_exp_bound (by positivity) hinner).trans_eq (by congr 1; ring)
  have hgrid : allocatedUniformGridVolumeCap B rowSets r ≤
      Real.exp (D * (D * (2 * D + F + 11))) := by
    have hrow (j : Fin m) : ((rowSets j).card : ℝ) ≤ D := by
      simpa only [Fintype.card_coe] using hgeom.rows j
    have hpow (a : LayerSamplerAxis I n) := pow_le_exp_mul_of_le_exp
      (by positivity : 0 ≤ 2 * (((2 : ℝ) ^ Fintype.card α * (2 * (r : ℝ))) *
        (8 * ((Fintype.card (B a) : ℝ) + 1))) + 3)
      (hgridBase a) (by positivity) (rowSets a.fst).card (hrow a.fst)
    calc
      _ ≤ ∏ _a : LayerSamplerAxis I n, Real.exp (D * (2 * D + F + 11)) :=
        Finset.prod_le_prod₀ (fun _ _ => by positivity) (fun a _ => hpow a)
      _ = Real.exp (D * (2 * D + F + 11)) ^ Fintype.card (LayerSamplerAxis I n) := by simp
      _ ≤ _ := pow_le_exp_mul_of_le_exp (Real.exp_pos _).le le_rfl (by positivity) _ hgeom.axes
  have hwindowBase : 2 * ((2 : ℝ) ^ Fintype.card α * (2 * (r : ℝ))) + 1 ≤
      Real.exp (D + F + 4) := by
    apply le_trans _ (two_mul_add_three_exp_bound (add_nonneg hD hF) hshort)
    linarith
  have hwindow := pow_le_exp_mul_of_le_exp
    (by positivity : 0 ≤ 2 * ((2 : ℝ) ^ Fintype.card α * (2 * (r : ℝ))) + 1)
    hwindowBase (by positivity)
    (Fintype.card (Σ a : LayerSamplerAxis I n, (rowSets a.fst : Type _))) hgeom.outputs
  have hmass : allocatedUniformGridVolumeCap B rowSets r *
      (2 * ((2 : ℝ) ^ Fintype.card α * (2 * (r : ℝ))) + 1) ^
        Fintype.card (Σ a : LayerSamplerAxis I n, (rowSets a.fst : Type _)) ≤
      Real.exp (D * (D * (2 * D + F + 11)) + D * (D + F + 4)) := by
    exact (mul_le_mul hgrid hwindow (by positivity) (Real.exp_pos _).le).trans_eq
      (Real.exp_add _ _).symm
  have hone : 1 ≤ Real.exp (D * (D * (2 * D + F + 11)) + D * (D + F + 4)) :=
    Real.one_le_exp_iff.mpr (by positivity)
  have hfour : (4 : ℝ) ≤ Real.exp 3 := by linarith [Real.add_one_le_exp (3 : ℝ)]
  calc
    _ ≤ 4 * Real.exp (D * (D * (2 * D + F + 11)) + D * (D + F + 4)) := by linarith
    _ ≤ Real.exp 3 * Real.exp (D * (D * (2 * D + F + 11)) + D * (D + F + 4)) :=
      mul_le_mul_of_nonneg_right hfour (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; unfold allocatedCutoffMassLog; ring

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

def allocatedProductCutoffMassLog {A : Type*} [Semiring A] (m : ℕ) (D c : A) : A :=
  allocatedCutoffMassLog D (8 * allocatedIdealCoverInputLog m D c + 14 + 2 * D + 2)

theorem allocatedProductCutoffMassLog_nonneg (m : ℕ) {D c : ℝ} (hD : 0 ≤ D) (hc : 0 ≤ c) :
    0 ≤ allocatedProductCutoffMassLog m D c :=
  allocatedCutoffMassLog_nonneg hD (allocatedProductChartLog_bounds m hD hc).2.1

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] (rowSets : Fin m → Finset (Finset α))
variable {D c : ℝ}

local notation "radius" => allocatedProductIdealSiteRadius (G := G) B rowSets

theorem allocatedProductCutoffMass_exp_bound
    (hgeom : AllocatedComparisonDimensions (G := G) B α (fun j => (rowSets j : Type _)) D)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ D)
    (hc : 0 ≤ c) (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ D) (hn : ∀ j, (n j : ℝ) ≤ D)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j) (hCc : ∀ j, C j ≤ Real.exp c)
    {η ε : ℝ} (hη : η ≤ 1) (hε : ε ≤ 1) :
    allocatedUniformGridVolumeCap B rowSets radius *
      (2 * ((2 : ℝ) ^ Fintype.card α * (2 * (radius : ℝ))) + 1) ^
        Fintype.card (Σ a : LayerSamplerAxis I n, (rowSets a.fst : Type _)) +
      2 * η + ε ≤ Real.exp (allocatedProductCutoffMassLog m D c) := by
  exact allocatedUniformCutoffMass_exp_bound B rowSets hgeom radius hvars
    (allocatedProductChartLog_bounds m hgeom.nonneg hc).2.1
    (allocatedProductIdealSiteRadius_exp_bound B rowSets hgeom hc hI hn C hC hCc) hη hε

end Erdos3.VectorPolynomial

end

end OAI
