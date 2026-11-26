import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalSquareGrid
import IPRADerivations.Analysis.Polynomials.RootFinding.GaussianMonicApplications
import IPRADerivations.Analysis.Polynomials.Horner.GaussianRationalHornerLipschitz
import IPRADerivations.Analysis.RationalArithmetic.FiniteProducts.GaussianRationalLinearProduct
import IPRADerivations.Foundations.LeastBoundedWitness
import IPRADerivations.Core.CongruenceTactic

/-!
# Actual bounded square-grid search for a monic approximate root

The original numerical monic polynomial and coefficient/precision guards
supply an actual approximate root. Its proved residual radius and the
actual nearest-grid map derive a successful stored grid index. An actual
least scan then returns a grid point with the requested original residual.
The conservative integer mesh is explicit; no search, rounding, descent
or desired residual law is supplied.
-/

set_option autoImplicit false
set_option linter.unnecessarySeqFocus false

namespace LeanProofs.IPRA.Analysis.GaussianMonicGridApproximateRoot

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (evaluate)
open GaussianRationalSyntheticDivision (qone)
open GaussianRationalMetric (bounded qnormSq squaredTolerance)
open GaussianEuclideanResidualRadius (coefficientBounds)
open GaussianRationalSquareGrid (grid nearest nearestIndex)
open GaussianRationalReciprocal (bound_congr)
open GaussianRationalDistanceOrder (distance_radius_mono distance_symmetric)
open GaussianDominantSyntax (four)
open GaussianCoefficientNameBounds (bounded_radius_mono)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def radius (A : PTm n) : PTm n := A+two
def disk (A : PTm n) : PTm n := two*radius A+one
def slope (N A : PTm n) : PTm n := GaussianRationalHornerLipschitz.constant N (disk A) A
def gain (N A : PTm n) : PTm n := succ (slope N A)
def mesh (N A q : PTm n) : PTm n := four*gain N A*q
def witness (C N p q : PTm n) : PTm n := GaussianMonicApplications.approximateRoot C N p (two*q)
def rounded (C N A p q : PTm n) : PTm n := nearest (radius A) (mesh N A q) (witness C N p q)
def witnessIndex (C N A p q : PTm n) : PTm n := nearestIndex (radius A) (mesh N A q) (witness C N p q)
def input (C N A p q : PTm n) : Fm PTm n := le one N ⋏
  (le one A ⋏ (length C ≐ succ N ⋏ (entry C zero ≐ qone ⋏
    (coefficientBounds C A ⋏ (le one p ⋏ le p q)))))
@[simp] theorem subst_radius {l : ℕ} (σ : Fin n → PTm l) (A : PTm n) : Syn.subst σ (radius A) = radius (Syn.subst σ A) := by simp [radius]
@[simp] theorem subst_disk {l : ℕ} (σ : Fin n → PTm l) (A : PTm n) : Syn.subst σ (disk A) = disk (Syn.subst σ A) := by simp [disk]
@[simp] theorem subst_slope {l : ℕ} (σ : Fin n → PTm l) (N A : PTm n) : Syn.subst σ (slope N A) = slope (Syn.subst σ N) (Syn.subst σ A) := by simp [slope]
@[simp] theorem subst_gain {l : ℕ} (σ : Fin n → PTm l) (N A : PTm n) : Syn.subst σ (gain N A) = gain (Syn.subst σ N) (Syn.subst σ A) := by simp [gain]
@[simp] theorem subst_mesh {l : ℕ} (σ : Fin n → PTm l) (N A q : PTm n) : Syn.subst σ (mesh N A q) = mesh (Syn.subst σ N) (Syn.subst σ A) (Syn.subst σ q) := by simp [mesh]
@[simp] theorem subst_witness {l : ℕ} (σ : Fin n → PTm l) (C N p q : PTm n) : Syn.subst σ (witness C N p q) = witness (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ p) (Syn.subst σ q) := by simp [witness]
@[simp] theorem subst_rounded {l : ℕ} (σ : Fin n → PTm l) (C N A p q : PTm n) : Syn.subst σ (rounded C N A p q) = rounded (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ A) (Syn.subst σ p) (Syn.subst σ q) := by simp [rounded]
@[simp] theorem subst_witnessIndex {l : ℕ} (σ : Fin n → PTm l) (C N A p q : PTm n) : Syn.subst σ (witnessIndex C N A p q) = witnessIndex (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ A) (Syn.subst σ p) (Syn.subst σ q) := by simp [witnessIndex]
@[simp] theorem subst_input {l : ℕ} (σ : Fin n → PTm l) (C N A p q : PTm n) : (input C N A p q).subst σ = input (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ A) (Syn.subst σ p) (Syn.subst σ q) := by simp [input]

theorem input_degree (C N A p q : PTm n) (h : Γ ⊢[PRAAx] input C N A p q) : Γ ⊢[PRAAx] le one N := .andE₁ h
theorem input_height (C N A p q : PTm n) (h : Γ ⊢[PRAAx] input C N A p q) : Γ ⊢[PRAAx] le one A := .andE₁ (.andE₂ h)
theorem input_length (C N A p q : PTm n) (h : Γ ⊢[PRAAx] input C N A p q) : Γ ⊢[PRAAx] length C ≐ succ N := .andE₁ (.andE₂ (.andE₂ h))
theorem input_monic (C N A p q : PTm n) (h : Γ ⊢[PRAAx] input C N A p q) : Γ ⊢[PRAAx] entry C zero ≐ qone := .andE₁ (.andE₂ (.andE₂ (.andE₂ h)))
theorem input_coefficients (C N A p q : PTm n) (h : Γ ⊢[PRAAx] input C N A p q) : Γ ⊢[PRAAx] coefficientBounds C A := .andE₁ (.andE₂ (.andE₂ (.andE₂ (.andE₂ h))))
theorem input_numerator (C N A p q : PTm n) (h : Γ ⊢[PRAAx] input C N A p q) : Γ ⊢[PRAAx] le one p := .andE₁ (.andE₂ (.andE₂ (.andE₂ (.andE₂ (.andE₂ h)))))
theorem input_tolerance (C N A p q : PTm n) (h : Γ ⊢[PRAAx] input C N A p q) : Γ ⊢[PRAAx] le p q := .andE₂ (.andE₂ (.andE₂ (.andE₂ (.andE₂ (.andE₂ h)))))
theorem input_denominator (C N A p q : PTm n) (h : Γ ⊢[PRAAx] input C N A p q) : Γ ⊢[PRAAx] le one q := le_trans (input_numerator _ _ _ _ _ h) (input_tolerance _ _ _ _ _ h)

theorem mesh_positive (N A q : PTm n) (hq : Γ ⊢[PRAAx] le one q) : Γ ⊢[PRAAx] le one (mesh N A q) :=
  GaussianRationalHorner.positive_product _ _ (GaussianRationalHorner.positive_product _ _
    (GaussianRationalHorner.positive_product two two (le_succ_self one) (le_succ_self one)) (zero_lt_succ _)) hq

theorem mesh_budget (N A p q : PTm n) (hp : Γ ⊢[PRAAx] le one p) : Γ ⊢[PRAAx]
    le (slope N A*(two*q)) (p*mesh N A q) := by
  have first := mul_le_mul_right (Γ := Γ) (two*q) (le_succ_self (slope N A))
  have small : Γ ⊢[PRAAx] le two (four : PTm n) := le_of_eq_add (d := two) (by unfold four; ipra_ring)
  have second : Γ ⊢[PRAAx] le (gain N A*(two*q)) (mesh N A q) :=
    le_congr (by ipra_ring) (by unfold mesh; ipra_ring) (mul_le_mul_right (gain N A*q) small)
  have third : Γ ⊢[PRAAx] le (mesh N A q) (p*mesh N A q) :=
    le_congr (one_mul _) (.eqRefl _) (mul_le_mul_right (mesh N A q) hp)
  exact le_trans first (le_trans second third)

theorem witness_residual (C N A p q : PTm n) (h : Γ ⊢[PRAAx] input C N A p q) : Γ ⊢[PRAAx]
    bounded (evaluate C (witness C N p q)) p (two*q) := .andE₂
  (GaussianMonicApplications.approximate_root C N p (two*q) (input_degree _ _ _ _ _ h) (input_length _ _ _ _ _ h)
    (input_monic _ _ _ _ _ h) (input_numerator _ _ _ _ _ h)
    (GaussianRationalHorner.positive_product _ _ (le_succ_self one) (input_denominator _ _ _ _ _ h)))

theorem witness_disk (C N A p q : PTm n) (h : Γ ⊢[PRAAx] input C N A p q) : Γ ⊢[PRAAx]
    bounded (witness C N p q) (radius A) one := by
  have hq := input_denominator C N A p q h
  have small : Γ ⊢[PRAAx] le (p*one) (one*(two*q)) :=
    le_congr (by ipra_ring) (one_mul _).eqSymm (le_trans (input_tolerance _ _ _ _ _ h)
      (le_of_eq_add (d := q) (by ipra_ring)))
  have residual := bounded_radius_mono _ _ _ _ _ (GaussianRationalHorner.positive_product _ _ (le_succ_self one) hq)
    (le_refl one) small (witness_residual C N A p q h)
  exact GaussianEuclideanResidualRadius.residual_radius C (witness C N p q) N A
    (input_degree _ _ _ _ _ h) (input_height _ _ _ _ _ h) (input_length _ _ _ _ _ h)
    (input_monic _ _ _ _ _ h) (input_coefficients _ _ _ _ _ h) residual

theorem rounded_residual (C N A p q : PTm n) (h : Γ ⊢[PRAAx] input C N A p q) : Γ ⊢[PRAAx]
    bounded (evaluate C (rounded C N A p q)) p q := by
  have hq := input_denominator C N A p q h
  have hp := input_numerator C N A p q h
  have hm := mesh_positive N A q hq
  have h2q := GaussianRationalHorner.positive_product _ _ (le_succ_self one) hq
  have diskRoot := witness_disk C N A p q h
  have diskRounded := GaussianRationalSquareGrid.nearest_bound (radius A) (mesh N A q) (witness C N p q) hm diskRoot
  have rootU : Γ ⊢[PRAAx] bounded (witness C N p q) (disk A) one :=
    bounded_radius_mono _ _ _ _ _ (le_refl one) (le_refl one)
      (by unfold disk; exact le_congr (by ipra_ring) (by ipra_ring) (le_of_eq_add (a := radius A) (b := two*radius A+one) (d := radius A+one) (by ipra_ring))) diskRoot
  have roundU : Γ ⊢[PRAAx] bounded (rounded C N A p q) (disk A) one :=
    bounded_radius_mono _ _ _ _ _ (le_refl one) (le_refl one)
      (le_congr (by ipra_ring) (by unfold disk; ipra_ring) (le_succ_self (two*radius A))) diskRounded
  have near := GaussianRationalSquareGrid.nearest_distance (radius A) (mesh N A q) (witness C N p q) hm diskRoot
  have variation := GaussianRationalHornerLipschitz.evaluation_bound C (witness C N p q) (rounded C N A p q)
    N (disk A) A one (mesh N A q) (input_length _ _ _ _ _ h) (input_coefficients _ _ _ _ _ h) rootU roundU hm near
  have small := distance_radius_mono _ _ _ _ _ _ hm h2q
    (le_congr (by unfold slope; ipra_ring) (.eqRefl _) (mesh_budget N A p q hp)) variation
  have reverse := distance_symmetric _ _ p (two*q) h2q small
  have combined := GaussianRationalPowerDifference.bounded_sum_same _ _ p p (two*q) h2q (witness_residual C N A p q h) reverse
  have value := GaussianRationalLinearProduct.add_sub_right (Γ := Γ) (evaluate C (witness C N p q)) (evaluate C (rounded C N A p q))
    (GaussianRationalHorner.horner_canonical _ _ _)
  have evalBound : Γ ⊢[PRAAx] bounded (evaluate C (rounded C N A p q)) (p+p) (two*q) :=
    bound_congr value (.eqRefl _) (.eqRefl _) combined
  exact bounded_radius_mono _ _ _ _ _ h2q hq (le_congr (by ipra_ring) (by ipra_ring) (le_refl (two*p*q))) evalBound

def check (C z p q : PTm n) : PTm n :=
  monus (RationalArgmin.left (qnormSq (evaluate C z)) (squaredTolerance p q))
    (RationalArgmin.left (squaredTolerance p q) (qnormSq (evaluate C z)))
def data (C R M p q : PTm n) : PTm n := pairT (pairT C R) (pairT M (pairT p q))
def scanBody : PTm 2 := check (fstT (fstT (var 1)))
  (entry (grid (sndT (fstT (var 1))) (fstT (sndT (var 1)))) (var 0))
  (fstT (sndT (sndT (var 1)))) (sndT (sndT (sndT (var 1))))
def selected (C R M p q : PTm n) : PTm n := Search.mu scanBody (length (grid R M)) (data C R M p q)
def root (C N A p q : PTm n) : PTm n :=
  entry (grid (radius A) (mesh N A q)) (selected C (radius A) (mesh N A q) p q)
@[simp] theorem subst_check {l : ℕ} (σ : Fin n → PTm l) (C z p q : PTm n) :
    Syn.subst σ (check C z p q) = check (Syn.subst σ C) (Syn.subst σ z) (Syn.subst σ p) (Syn.subst σ q) := by simp [check]
@[simp] theorem subst_data {l : ℕ} (σ : Fin n → PTm l) (C R M p q : PTm n) :
    Syn.subst σ (data C R M p q) = data (Syn.subst σ C) (Syn.subst σ R) (Syn.subst σ M) (Syn.subst σ p) (Syn.subst σ q) := by simp [data]
@[simp] theorem subst_selected {l : ℕ} (σ : Fin n → PTm l) (C R M p q : PTm n) :
    Syn.subst σ (selected C R M p q) = selected (Syn.subst σ C) (Syn.subst σ R) (Syn.subst σ M) (Syn.subst σ p) (Syn.subst σ q) := by simp [selected]
@[simp] theorem subst_root {l : ℕ} (σ : Fin n → PTm l) (C N A p q : PTm n) :
    Syn.subst σ (root C N A p q) = root (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ A) (Syn.subst σ p) (Syn.subst σ q) := by simp [root]

theorem check_congr {C D z w p a q b : PTm n} (hC : Γ ⊢[PRAAx] C ≐ D) (hz : Γ ⊢[PRAAx] z ≐ w)
    (hp : Γ ⊢[PRAAx] p ≐ a) (hq : Γ ⊢[PRAAx] q ≐ b) : Γ ⊢[PRAAx] check C z p q ≐ check D w a b := by
  ipra_congr (check (var 0) (var 1) (var 2) (var 3) : PTm 4) with [hC, hz, hp, hq]
theorem grid_congr {R S M K : PTm n} (hR : Γ ⊢[PRAAx] R ≐ S) (hM : Γ ⊢[PRAAx] M ≐ K) : Γ ⊢[PRAAx] grid R M ≐ grid S K := by
  ipra_congr (grid (var 0) (var 1) : PTm 2) with [hR, hM]

theorem scan_body_at (C R M p q i : PTm n) : Γ ⊢[PRAAx]
    inst2 scanBody i (data C R M p q) ≐ check C (entry (grid R M) i) p q := by
  have left := fst_pair (Γ := Γ) (pairT C R) (pairT M (pairT p q))
  have right := snd_pair (Γ := Γ) (pairT C R) (pairT M (pairT p q))
  have tail := (congrSnd right).eqTrans (snd_pair _ _)
  simp only [scanBody,inst2,subst_check,Foundations.MasterCertificate.subst_entry,
    GaussianRationalSquareGrid.subst_grid,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact check_congr ((congrFst left).eqTrans (fst_pair _ _))
    (Foundations.SequenceComposition.entry_congr
      (grid_congr ((congrSnd left).eqTrans (snd_pair _ _)) ((congrFst right).eqTrans (fst_pair _ _))) (.eqRefl _))
    ((congrFst tail).eqTrans (fst_pair _ _)) ((congrSnd tail).eqTrans (snd_pair _ _))

theorem scan_accept (C R M p q i : PTm n) (h : Γ ⊢[PRAAx] inst2 scanBody i (data C R M p q) ≐ zero) : Γ ⊢[PRAAx]
    bounded (evaluate C (entry (grid R M) i)) p q := (scan_body_at C R M p q i).eqSymm.eqTrans h
theorem scan_zero (C R M p q i : PTm n) (h : Γ ⊢[PRAAx] bounded (evaluate C (entry (grid R M) i)) p q) : Γ ⊢[PRAAx]
    inst2 scanBody i (data C R M p q) ≐ zero := (scan_body_at C R M p q i).eqTrans h

/-- The actual original root and actual rounded stored entry derive a
successful grid test before the bounded search is used. -/
theorem constructive_witness (C N A p q : PTm n) (h : Γ ⊢[PRAAx] input C N A p q) : Γ ⊢[PRAAx]
    lt (witnessIndex C N A p q) (length (grid (radius A) (mesh N A q))) ⋏
      bounded (evaluate C (entry (grid (radius A) (mesh N A q)) (witnessIndex C N A p q))) p q := by
  have original := witness_disk C N A p q h
  have lookup := GaussianRationalSquareGrid.nearest_lookup (radius A) (mesh N A q) (witness C N p q) original
  have value : Γ ⊢[PRAAx] evaluate C (entry (grid (radius A) (mesh N A q)) (witnessIndex C N A p q)) ≐
      evaluate C (rounded C N A p q) := congrAp3 GaussianRationalHorner.hornerF (.eqRefl _) (.eqRefl _) lookup
  exact .andI (GaussianRationalSquareGrid.nearest_index_bound _ _ _ original)
    (bound_congr value.eqSymm (.eqRefl _) (.eqRefl _) (rounded_residual C N A p q h))

theorem search_found (C N A p q : PTm n) (h : Γ ⊢[PRAAx] input C N A p q) : Γ ⊢[PRAAx]
    lt (selected C (radius A) (mesh N A q) p q) (length (grid (radius A) (mesh N A q))) ⋏
      ((inst2 scanBody (selected C (radius A) (mesh N A q) p q) (data C (radius A) (mesh N A q) p q) ≐ zero) ⋏
        le (selected C (radius A) (mesh N A q) p q) (witnessIndex C N A p q)) := by
  have actual := constructive_witness C N A p q h
  exact Search.search_found (scan_zero _ _ _ _ _ _ (.andE₂ actual)) (.andE₁ actual)

theorem root_residual (C N A p q : PTm n) (h : Γ ⊢[PRAAx] input C N A p q) : Γ ⊢[PRAAx]
    bounded (evaluate C (root C N A p q)) p q := scan_accept _ _ _ _ _ _ (.andE₁ (.andE₂ (search_found C N A p q h)))
theorem root_canonical (C N A p q : PTm n) (h : Γ ⊢[PRAAx] input C N A p q) : Γ ⊢[PRAAx]
    GaussianRationalHorner.canonical (root C N A p q) := GaussianRationalSquareGrid.grid_entry_canonical _ _ _
      (mesh_positive N A q (input_denominator _ _ _ _ _ h)) (.andE₁ (search_found C N A p q h))
theorem selected_bound (C N A p q : PTm n) (h : Γ ⊢[PRAAx] input C N A p q) : Γ ⊢[PRAAx]
    lt (selected C (radius A) (mesh N A q) p q) (GaussianRationalSquareGrid.side (radius A) (mesh N A q)*GaussianRationalSquareGrid.side (radius A) (mesh N A q)) :=
  lt_congr (.eqRefl _) (GaussianRationalSquareGrid.grid_length _ _) (.andE₁ (search_found C N A p q h))

theorem least_rejects (C R M p q i : PTm n) (hi : Γ ⊢[PRAAx] lt i (selected C R M p q)) : Γ ⊢[PRAAx]
    neg (bounded (evaluate C (entry (grid R M) i)) p q) := by
  refine .impI ?_
  exact .impE (Search.search_minimal (f := scanBody) hi.wk) (scan_zero _ _ _ _ _ _ Prf.hyp0)

theorem root_disk (C N A p q : PTm n) (h : Γ ⊢[PRAAx] input C N A p q) : Γ ⊢[PRAAx]
    bounded (root C N A p q) (radius A) one := by
  have hq := input_denominator C N A p q h
  have small : Γ ⊢[PRAAx] le (p*one) (one*q) :=
    le_congr (by ipra_ring) (by ipra_ring) (input_tolerance C N A p q h)
  exact GaussianEuclideanResidualRadius.residual_radius C (root C N A p q) N A
    (input_degree _ _ _ _ _ h) (input_height _ _ _ _ _ h) (input_length _ _ _ _ _ h)
    (input_monic _ _ _ _ _ h) (input_coefficients _ _ _ _ _ h)
    (bounded_radius_mono _ _ _ _ _ hq (le_refl one) small (root_residual C N A p q h))

def lowerBounds (C N A : PTm n) : Fm PTm n := .all (lt (var 0) (Syn.shift N) ⟶
  bounded (entry (Syn.shift C) (succ (var 0))) (Syn.shift A) one)
def sourceInput (C N A p q : PTm n) : Fm PTm n := le one N ⋏
  (le one A ⋏ (length C ≐ succ N ⋏ (entry C zero ≐ qone ⋏
    (lowerBounds C N A ⋏ (le one p ⋏ le p q)))))
@[simp] theorem subst_lowerBounds {l : ℕ} (σ : Fin n → PTm l) (C N A : PTm n) :
    (lowerBounds C N A).subst σ = lowerBounds (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ A) := by simp [lowerBounds,Syn.subst_shift,Syn.shift_subst]
@[simp] theorem subst_sourceInput {l : ℕ} (σ : Fin n → PTm l) (C N A p q : PTm n) :
    (sourceInput C N A p q).subst σ = sourceInput (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ A) (Syn.subst σ p) (Syn.subst σ q) := by simp [sourceInput]

theorem lower_at (C N A i : PTm n) (h : Γ ⊢[PRAAx] lowerBounds C N A) (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    bounded (entry C (succ i)) A one := by
  have rule : Γ ⊢[PRAAx] lt i N ⟶ bounded (entry C (succ i)) A one := by simpa [lowerBounds] using h.allE i
  exact .impE rule hi

theorem coefficient_of_lower (C N A i : PTm n) (hA : Γ ⊢[PRAAx] le one A)
    (hLen : Γ ⊢[PRAAx] length C ≐ succ N) (hMonic : Γ ⊢[PRAAx] entry C zero ≐ qone)
    (hLower : Γ ⊢[PRAAx] lowerBounds C N A) (hi : Γ ⊢[PRAAx] lt i (length C)) : Γ ⊢[PRAAx] bounded (entry C i) A one := by
  have oneBound : Γ ⊢[PRAAx] bounded qone A one := bounded_radius_mono _ _ _ _ _ (le_refl one) (le_refl one)
    (le_congr (by ipra_ring) (by ipra_ring) hA) GaussianRationalReciprocal.qone_bounded
  refine .orE (zero_or_succ i) ?_ ?_
  · have value : (i ≐ zero)::Γ ⊢[PRAAx] entry C i ≐ qone :=
      (Foundations.SequenceComposition.entry_congr (.eqRefl _) Prf.hyp0).eqTrans hMonic.wk
    exact bound_congr value.eqSymm (.eqRefl _) (.eqRefl _) oneBound.wk
  · let Δ := (i ≐ succ (PTm.pred i))::Γ
    have degree : Δ ⊢[PRAAx] le i N := (succ_monus_succ i N).eqSymm.eqTrans
      (lt_congr (.eqRefl _) hLen.wk hi.wk)
    have tail : Δ ⊢[PRAAx] lt (PTm.pred i) N := le_congr Prf.hyp0 (.eqRefl _) degree
    exact bound_congr (Foundations.SequenceComposition.entry_congr (.eqRefl _) Prf.hyp0.eqSymm) (.eqRefl _) (.eqRefl _)
      (lower_at C N A (PTm.pred i) hLower.wk tail)

theorem coefficients_of_lower (C N A : PTm n) (hA : Γ ⊢[PRAAx] le one A)
    (hLen : Γ ⊢[PRAAx] length C ≐ succ N) (hMonic : Γ ⊢[PRAAx] entry C zero ≐ qone)
    (hLower : Γ ⊢[PRAAx] lowerBounds C N A) : Γ ⊢[PRAAx] coefficientBounds C A := by
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (length (Syn.shift C)) :: Γ.map Fm.shift
  have aa : Δ ⊢[PRAAx] le one (Syn.shift A) := by simpa [Δ,Fm.shift,Syn.shift,one] using hA.shift.wk
  have len : Δ ⊢[PRAAx] length (Syn.shift C) ≐ succ (Syn.shift N) := by simpa [Δ,Fm.shift,Syn.shift] using hLen.shift.wk
  have monic : Δ ⊢[PRAAx] entry (Syn.shift C) zero ≐ qone := by simpa [Δ,Fm.shift,Syn.shift] using hMonic.shift.wk
  have lower : Δ ⊢[PRAAx] lowerBounds (Syn.shift C) (Syn.shift N) (Syn.shift A) := by simpa [Δ,Fm.shift,Syn.shift] using hLower.shift.wk
  exact coefficient_of_lower _ _ _ _ aa len monic lower Prf.hyp0

theorem input_of_source (C N A p q : PTm n) (h : Γ ⊢[PRAAx] sourceInput C N A p q) : Γ ⊢[PRAAx] input C N A p q := by
  have hN := Prf.andE₁ h
  have hA := Prf.andE₁ (Prf.andE₂ h)
  have len := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ h))
  have monic := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ h)))
  have lower := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ h))))
  have precision := Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ h))))
  exact .andI hN (.andI hA (.andI len (.andI monic (.andI (coefficients_of_lower C N A hA len monic lower) precision))))

def output (C N A p q : PTm n) : PTm n := pairT (root C N A p q)
  (pairT (selected C (radius A) (mesh N A q) p q)
    (pairT (grid (radius A) (mesh N A q)) (pairT (mesh N A q) (radius A))))
def outputF : PR 5 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4))
def run (C N A p q : PTm n) : PTm n := PTm.app outputF ![C,N,A,p,q]
@[simp] theorem subst_output {l : ℕ} (σ : Fin n → PTm l) (C N A p q : PTm n) :
    Syn.subst σ (output C N A p q) = output (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ A) (Syn.subst σ p) (Syn.subst σ q) := by simp [output]
@[simp] theorem subst_run {l : ℕ} (σ : Fin n → PTm l) (C N A p q : PTm n) :
    Syn.subst σ (run C N A p q) = run (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ A) (Syn.subst σ p) (Syn.subst σ q) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl
theorem program_at (C N A p q : PTm n) : Γ ⊢[PRAAx] run C N A p q ≐ output C N A p q := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![C,N,A,p,q]
theorem returned_root (C N A p q : PTm n) : Γ ⊢[PRAAx] fstT (run C N A p q) ≐ root C N A p q :=
  (congrFst (program_at C N A p q)).eqTrans (fst_pair _ _)
theorem returned_index (C N A p q : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run C N A p q)) ≐ selected C (radius A) (mesh N A q) p q :=
  (congrFst (congrSnd (program_at C N A p q))).eqTrans ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _))
theorem returned_grid (C N A p q : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run C N A p q))) ≐ grid (radius A) (mesh N A q) := by
  have t1 := (congrSnd (program_at (Γ := Γ) C N A p q)).eqTrans (snd_pair _ _)
  have t2 := (congrSnd t1).eqTrans (snd_pair _ _)
  exact (congrFst t2).eqTrans (fst_pair _ _)
theorem returned_mesh (C N A p q : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (sndT (run C N A p q)))) ≐ mesh N A q := by
  have t1 := (congrSnd (program_at (Γ := Γ) C N A p q)).eqTrans (snd_pair _ _)
  have t2 := (congrSnd t1).eqTrans (snd_pair _ _)
  have t3 := (congrSnd t2).eqTrans (snd_pair _ _)
  exact (congrFst t3).eqTrans (fst_pair _ _)
theorem returned_radius (C N A p q : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (sndT (run C N A p q)))) ≐ radius A := by
  have t1 := (congrSnd (program_at (Γ := Γ) C N A p q)).eqTrans (snd_pair _ _)
  have t2 := (congrSnd t1).eqTrans (snd_pair _ _)
  have t3 := (congrSnd t2).eqTrans (snd_pair _ _)
  exact (congrSnd t3).eqTrans (snd_pair _ _)

theorem source_result (C N A p q : PTm n) (h : Γ ⊢[PRAAx] sourceInput C N A p q) : Γ ⊢[PRAAx]
    GaussianRationalHorner.canonical (root C N A p q) ⋏
      (bounded (evaluate C (root C N A p q)) p q ⋏ bounded (root C N A p q) (radius A) one) :=
  .andI (root_canonical _ _ _ _ _ (input_of_source C N A p q h))
    (.andI (root_residual _ _ _ _ _ (input_of_source C N A p q h)) (root_disk _ _ _ _ _ (input_of_source C N A p q h)))
theorem returned_result (C N A p q : PTm n) (h : Γ ⊢[PRAAx] sourceInput C N A p q) : Γ ⊢[PRAAx]
    GaussianRationalHorner.canonical (fstT (run C N A p q)) ⋏
      (bounded (evaluate C (fstT (run C N A p q))) p q ⋏ bounded (fstT (run C N A p q)) (sndT (sndT (sndT (sndT (run C N A p q))))) one) := by
  have actual := source_result C N A p q h
  exact .andI (GaussianRationalHorner.canonical_congr (returned_root C N A p q) (.andE₁ actual))
    (.andI (bound_congr (congrAp3 GaussianRationalHorner.hornerF (.eqRefl _) (.eqRefl _) (returned_root C N A p q)).eqSymm
      (.eqRefl _) (.eqRefl _) (.andE₁ (.andE₂ actual)))
      (bound_congr (returned_root C N A p q).eqSymm (returned_radius C N A p q).eqSymm (.eqRefl _) (.andE₂ (.andE₂ actual))))
theorem returned_lookup (C N A p q : PTm n) : Γ ⊢[PRAAx]
    entry (fstT (sndT (sndT (run C N A p q)))) (fstT (sndT (run C N A p q))) ≐ fstT (run C N A p q) :=
  (Foundations.SequenceComposition.entry_congr (returned_grid C N A p q) (returned_index C N A p q)).eqTrans
    (returned_root C N A p q).eqSymm

theorem returned_index_bound (C N A p q : PTm n) (h : Γ ⊢[PRAAx] sourceInput C N A p q) : Γ ⊢[PRAAx]
    lt (fstT (sndT (run C N A p q))) (length (fstT (sndT (sndT (run C N A p q))))) :=
  lt_congr (returned_index C N A p q).eqSymm (congrFst (returned_grid C N A p q)).eqSymm
    (.andE₁ (search_found C N A p q (input_of_source C N A p q h)))
theorem returned_grid_size (C N A p q : PTm n) : Γ ⊢[PRAAx]
    length (fstT (sndT (sndT (run C N A p q)))) ≐
      GaussianRationalSquareGrid.side (radius A) (mesh N A q)*GaussianRationalSquareGrid.side (radius A) (mesh N A q) :=
  (congrFst (returned_grid C N A p q)).eqTrans (GaussianRationalSquareGrid.grid_length _ _)

theorem actual_original_grid_root_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (sourceInput (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      (GaussianRationalHorner.canonical (root (var 0) (var 1) (var 2) (var 3) (var 4)) ⋏
        (bounded (evaluate (var 0) (root (var 0) (var 1) (var 2) (var 3) (var 4))) (var 3) (var 4) ⋏
          bounded (root (var 0) (var 1) (var 2) (var 3) (var 4)) (radius (var 2)) one))) :=
  closeUniv 5 (.impI (source_result _ _ _ _ _ Prf.hyp0))

theorem actual_constructive_grid_witness_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (sourceInput (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      (lt (witnessIndex (var 0) (var 1) (var 2) (var 3) (var 4)) (length (grid (radius (var 2)) (mesh (var 1) (var 2) (var 4)))) ⋏
        bounded (evaluate (var 0) (entry (grid (radius (var 2)) (mesh (var 1) (var 2) (var 4)))
          (witnessIndex (var 0) (var 1) (var 2) (var 3) (var 4)))) (var 3) (var 4))) :=
  closeUniv 5 (.impI (constructive_witness _ _ _ _ _ (input_of_source _ _ _ _ _ Prf.hyp0)))

theorem actual_grid_search_success_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (sourceInput (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      lt (selected (var 0) (radius (var 2)) (mesh (var 1) (var 2) (var 4)) (var 3) (var 4))
        (length (grid (radius (var 2)) (mesh (var 1) (var 2) (var 4))))) :=
  closeUniv 5 (.impI (.andE₁ (search_found _ _ _ _ _ (input_of_source _ _ _ _ _ Prf.hyp0))))

theorem actual_least_grid_rejection_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (lt (var 5) (selected (var 0) (var 1) (var 2) (var 3) (var 4)) ⟶
      neg (bounded (evaluate (var 0) (entry (grid (var 1) (var 2)) (var 5))) (var 3) (var 4))) :=
  closeUniv 6 (.impI (least_rejects _ _ _ _ _ _ Prf.hyp0))

theorem actual_original_lower_coefficients_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 2) ⟶ length (var 0) ≐ succ (var 1) ⟶ entry (var 0) zero ≐ qone ⟶
      lowerBounds (var 0) (var 1) (var 2) ⟶ coefficientBounds (var 0) (var 2)) :=
  closeUniv 3 (.impI (.impI (.impI (.impI (coefficients_of_lower _ _ _ Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))

theorem actual_conservative_mesh_budget_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 2) ⟶ le (slope (var 0) (var 1)*(two*var 3)) (var 2*mesh (var 0) (var 1) (var 3))) :=
  closeUniv 4 (.impI (mesh_budget _ _ _ _ Prf.hyp0))

theorem actual_grid_root_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (run (var 0) (var 1) (var 2) (var 3) (var 4) ≐ output (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (program_at _ _ _ _ _)

theorem actual_returned_grid_root_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (sourceInput (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      (GaussianRationalHorner.canonical (fstT (run (var 0) (var 1) (var 2) (var 3) (var 4))) ⋏
        (bounded (evaluate (var 0) (fstT (run (var 0) (var 1) (var 2) (var 3) (var 4)))) (var 3) (var 4) ⋏
          bounded (fstT (run (var 0) (var 1) (var 2) (var 3) (var 4)))
            (sndT (sndT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4)))))) one))) :=
  closeUniv 5 (.impI (returned_result _ _ _ _ _ Prf.hyp0))

theorem actual_returned_grid_lookup_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (entry (fstT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4)))))
      (fstT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4)))) ≐ fstT (run (var 0) (var 1) (var 2) (var 3) (var 4))) :=
  closeUniv 5 (returned_lookup _ _ _ _ _)

theorem actual_returned_grid_index_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (sourceInput (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      lt (fstT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4))))
        (length (fstT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4))))))) :=
  closeUniv 5 (.impI (returned_index_bound _ _ _ _ _ Prf.hyp0))

theorem actual_returned_grid_size_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (length (fstT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4))))) ≐
      GaussianRationalSquareGrid.side (radius (var 2)) (mesh (var 1) (var 2) (var 4))*
        GaussianRationalSquareGrid.side (radius (var 2)) (mesh (var 1) (var 2) (var 4))) :=
  closeUniv 5 (returned_grid_size _ _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianMonicGridApproximateRoot
