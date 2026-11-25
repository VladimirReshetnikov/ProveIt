import IPRADerivations.Analysis.GaussianStirlingAllOrderPowerIntegralMeshCells
import IPRADerivations.Analysis.GaussianStirlingAllOrderPanelPartsRecurrence

/-!
# Exact antiderivative brackets over the original mesh prefix

Both endpoint comparisons telescope through the original rational
sum of left samples. The upper comparison carries a correction at
its endpoints, so its error budget does not grow with the length.
At a complete panel both endpoint expressions use the original
rational argument and are independent of the mesh.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderPowerIntegralMesh

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ConciseIPRA.PTm (zero succ)
open GaussianEuclideanDistanceName (fraction)
open GaussianRationalSyntheticBounds (add_monotone)
open GaussianStirlingAllOrderKernel (multiply_zero_right)
open GaussianStirlingAllOrderPanelPartsFinite (weightAt weightBody parameters weight_at)
open GaussianStirlingAllOrderPanelPartsRecurrence (panelMass)
open GaussianStirlingAllOrderPowerIntegralMeshCells (endpoint primitive cellSample endpointSample
  endpoint_canonical endpoint_at_multiple cell_at_multiple cell_endpoint_corrections)
open GaussianStirlingAllOrderReciprocalGridError (gridDen)
open RationalAlgebra (add_congr add_commutative add_associative multiply_congr multiply_add positive_product)
open RationalArithmetic (add add_guard multiply)
open RationalArgmin (rationalLE rationalLE_congr reflexive transitive)
open RationalFiniteSum (sum)
open RationalReciprocalPowerTail (add_zero_right zero_fraction)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def brackets (u v upperU upperV mass : PTm n) : Fm PTm n :=
  rationalLE u (add mass v) ⋏ rationalLE (add mass upperV) upperU

@[simp] theorem subst_brackets {l : ℕ} (σ : Fin n → PTm l) (u v upperU upperV mass : PTm n) :
    (brackets u v upperU upperV mass).subst σ =
      brackets (Syn.subst σ u) (Syn.subst σ v) (Syn.subst σ upperU) (Syn.subst σ upperV) (Syn.subst σ mass) :=
  by simp [brackets]

theorem join_brackets (u v w upperU upperV upperW p q r : PTm n)
    (before : Γ ⊢[PRAAx] brackets u v upperU upperV p)
    (after : Γ ⊢[PRAAx] brackets v w upperV upperW q)
    (sum_eq : Γ ⊢[PRAAx] add p q ≐ r) :
    Γ ⊢[PRAAx] brackets u w upperU upperW r := by
  have add_then : Γ ⊢[PRAAx] add p (add q w) ≐ add r w :=
    (add_associative _ _ _).eqSymm.eqTrans (add_congr sum_eq (.eqRefl _))
  have add_bound : Γ ⊢[PRAAx] add r upperW ≐ add p (add q upperW) :=
    (add_congr sum_eq.eqSymm (.eqRefl _)).eqTrans (add_associative _ _ _)
  exact .andI
    (transitive before.andE₁ (rationalLE_congr (.eqRefl _) add_then (add_monotone _ _ _ _
      (reflexive p) after.andE₁)))
    (transitive (rationalLE_congr add_bound.eqSymm (.eqRefl _) (add_monotone _ _ _ _
      (reflexive p) after.andE₂)) before.andE₂)

def meshMass (e : ℕ) (U B M N : PTm n) : PTm n :=
  multiply (fraction one M) (sum (weightBody e) N (parameters U B M))

def meshPotential (e : ℕ) (U B M N : PTm n) : PTm n := endpoint e B M (gridDen U B M N)
def gridSample (e : ℕ) (U B M N : PTm n) : PTm n := cellSample e B M (gridDen U B M N)
def meshUpper (e : ℕ) (U B M N : PTm n) : PTm n := add (meshPotential e U B M N) (gridSample e U B M N)

def meshLaw (e : ℕ) (U B M N : PTm n) : Fm PTm n :=
  brackets (meshPotential e U B M zero) (meshPotential e U B M N)
    (meshUpper e U B M zero) (meshUpper e U B M N) (meshMass e U B M N)

@[simp] theorem subst_meshLaw {l : ℕ} (σ : Fin n → PTm l) (e : ℕ) (U B M N : PTm n) :
    (meshLaw e U B M N).subst σ = meshLaw e (Syn.subst σ U) (Syn.subst σ B) (Syn.subst σ M) (Syn.subst σ N) := by
  simp [meshLaw,meshMass,meshUpper,meshPotential,gridSample,gridDen]

private theorem grid_positive (U B M N : PTm n) (hU : Γ ⊢[PRAAx] le one U) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] le one (gridDen U B M N) :=
  le_trans (positive_product hU hM) (le_add_right _ _)

private theorem mesh_zero (e : ℕ) (he : 2≤e) (U B M : PTm n)
    (hU : Γ ⊢[PRAAx] le one U) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] meshLaw e U B M zero := by
  let x := meshPotential e U B M zero
  let y := meshUpper e U B M zero
  have eq : Γ ⊢[PRAAx] meshMass e U B M zero ≐ fraction zero one :=
    (multiply_congr (.eqRefl _) ((RationalFiniteSum.sum_zero _ _).eqTrans zero_fraction.eqSymm)).eqTrans
      (multiply_zero_right _)
  have zero_add_canonical (z : PTm n) (hz : Γ ⊢[PRAAx] RationalNormalForm.wellFormed z) :
      Γ ⊢[PRAAx] add (meshMass e U B M zero) z ≐ z :=
    (add_congr eq (.eqRefl z)).eqTrans ((add_commutative _ _).eqTrans (add_zero_right _ hz))
  have hx := endpoint_canonical e he B M (gridDen U B M zero) (grid_positive U B M zero hU hM)
  exact .andI (rationalLE_congr (.eqRefl x) (zero_add_canonical x hx).eqSymm (reflexive x))
    (rationalLE_congr (zero_add_canonical y (add_guard _ _)).eqSymm (.eqRefl y) (reflexive y))

private theorem mesh_step (e : ℕ) (he : 2≤e) (U B M N : PTm n)
    (hU : Γ ⊢[PRAAx] le one U) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] brackets (meshPotential e U B M N) (meshPotential e U B M (succ N))
      (meshUpper e U B M N) (meshUpper e U B M (succ N)) (gridSample e U B M N) := by
  let K := gridDen U B M N
  let D := cellSample e B M K
  have h := cell_endpoint_corrections e he B M K hM (grid_positive U B M N hU hM)
  have next : Γ ⊢[PRAAx] K+B ≐ gridDen U B M (succ N) := by dsimp [K,gridDen]; ipra_ring
  have p : Γ ⊢[PRAAx] endpoint e B M (K+B) ≐ meshPotential e U B M (succ N) := by
    simpa only [meshPotential,GaussianStirlingAllOrderPowerIntegralMeshCells.subst_endpoint,Syn.subst_var,
      Syn.inst_zero,Syn.subst_inst_shift] using
      Prf.eqCongr (Γ := Γ) (endpoint e (Syn.shift B) (Syn.shift M) (var 0))
        (σ := Syn.inst (K+B)) (σ' := Syn.inst (gridDen U B M (succ N)))
        (fun i => Fin.cases next (fun j => .eqRefl (var j)) i)
  have c : Γ ⊢[PRAAx] cellSample e B M (K+B) ≐ gridSample e U B M (succ N) := by
    simpa only [gridSample,GaussianStirlingAllOrderPowerIntegralMeshCells.subst_cellSample,Syn.subst_var,
      Syn.inst_zero,Syn.subst_inst_shift] using
      Prf.eqCongr (Γ := Γ) (cellSample e (Syn.shift B) (Syn.shift M) (var 0))
        (σ := Syn.inst (K+B)) (σ' := Syn.inst (gridDen U B M (succ N)))
        (fun i => Fin.cases next (fun j => .eqRefl (var j)) i)
  exact .andI (rationalLE_congr (.eqRefl _) (add_congr (.eqRefl D) p) h.andE₁)
    (rationalLE_congr (add_congr (.eqRefl D) (add_congr p c)) (.eqRefl _) h.andE₂)

private theorem mesh_mass_succ (e : ℕ) (U B M N : PTm n) :
    Γ ⊢[PRAAx] meshMass e U B M (succ N) ≐ add (meshMass e U B M N) (gridSample e U B M N) :=
  (multiply_congr (.eqRefl _) (RationalFiniteSum.sum_succ _ _ _)).eqTrans
    ((multiply_add _ _ _).eqTrans (add_congr (.eqRefl _) (multiply_congr (.eqRefl _) (weight_at e U B M N))))

theorem mesh_integral_brackets (e : ℕ) (he : 2≤e) (U B M N : PTm n)
    (hU : Γ ⊢[PRAAx] le one U) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] meshLaw e U B M N := by
  have all : Γ ⊢[PRAAx] .all (meshLaw e (Syn.shift U) (Syn.shift B) (Syn.shift M) (var 0)) := by
    refine PRA.qfInd _ ⟨trivial,trivial⟩ ?_ ?_
    · simpa only [subst_meshLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using mesh_zero e he U B M hU hM
    · simp only [subst_meshLaw,subst_repl_shift,Syn.subst_var,Syn.repl_zero]
      let δ := meshLaw e (Syn.shift U) (Syn.shift B) (Syn.shift M) (var 0)
      let Δ := δ :: Γ.map Fm.shift
      have u : Δ ⊢[PRAAx] le one (Syn.shift U) := by
        simpa [Δ,Fm.shift,Syn.shift,one] using hU.shift.wk
      have m : Δ ⊢[PRAAx] le one (Syn.shift M) := by
        simpa [Δ,Fm.shift,Syn.shift,one] using hM.shift.wk
      exact join_brackets _ _ _ _ _ _ _ _ _ (Prf.hyp0 : Δ ⊢[PRAAx] δ)
        (mesh_step e he _ _ _ _ u m) (mesh_mass_succ e _ _ _ _).eqSymm
  simpa only [subst_meshLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE N

def upperPrimitive (e : ℕ) (U B M : PTm n) : PTm n := add (primitive e U B) (endpointSample e U B M)

@[simp] theorem subst_upperPrimitive {l : ℕ} (σ : Fin n → PTm l) (e : ℕ) (U B M : PTm n) :
    Syn.subst σ (upperPrimitive e U B M) = upperPrimitive e (Syn.subst σ U) (Syn.subst σ B) (Syn.subst σ M) :=
  by simp [upperPrimitive]

private theorem read_endpoint (e : ℕ) (he : 2≤e) (U B M N V : PTm n) (hV : Γ ⊢[PRAAx] le one V)
    (hM : Γ ⊢[PRAAx] le one M) (index : Γ ⊢[PRAAx] gridDen U B M N ≐ V*M) :
    (Γ ⊢[PRAAx] meshPotential e U B M N ≐ primitive e V B) ∧
      (Γ ⊢[PRAAx] meshUpper e U B M N ≐ upperPrimitive e V B M) := by
  have p : Γ ⊢[PRAAx] meshPotential e U B M N ≐ endpoint e B M (V*M) := by
    simpa [meshPotential] using Prf.eqCongr (Γ := Γ) (endpoint e (Syn.shift B) (Syn.shift M) (var 0))
      (σ := Syn.inst (gridDen U B M N)) (σ' := Syn.inst (V*M))
      (fun i => Fin.cases index (fun j => .eqRefl (var j)) i)
  have c : Γ ⊢[PRAAx] gridSample e U B M N ≐ cellSample e B M (V*M) := by
    simpa [gridSample] using Prf.eqCongr (Γ := Γ) (cellSample e (Syn.shift B) (Syn.shift M) (var 0))
      (σ := Syn.inst (gridDen U B M N)) (σ' := Syn.inst (V*M))
      (fun i => Fin.cases index (fun j => .eqRefl (var j)) i)
  have h := p.eqTrans (endpoint_at_multiple e he V B M hV hM)
  exact ⟨h,add_congr h (c.eqTrans (cell_at_multiple e V B M hV hM))⟩

theorem panel_integral_brackets (e : ℕ) (he : 2≤e) (U B M : PTm n)
    (hU : Γ ⊢[PRAAx] le one U) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] brackets (primitive e U B) (primitive e (U+B) B)
      (upperPrimitive e U B M) (upperPrimitive e (U+B) B M) (panelMass e U B M) := by
  have h := mesh_integral_brackets e he U B M M hU hM
  have lo := read_endpoint e he U B M zero U hU hM (by unfold gridDen; ipra_ring)
  have hi := read_endpoint e he U B M M (U+B) (le_trans hU (le_add_right U B)) hM (by unfold gridDen; ipra_ring)
  exact .andI (rationalLE_congr lo.1 (add_congr (.eqRefl _) hi.1) h.andE₁)
    (rationalLE_congr (add_congr (.eqRefl _) hi.2) lo.2 h.andE₂)

theorem actual_original_reciprocal_panel_integral_brackets_closed (e : ℕ) (he : 2≤e) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 (le one (var 0) ⟶ le one (var 2) ⟶
      brackets (primitive e (var 0) (var 1)) (primitive e (var 0+var 1) (var 1))
        (upperPrimitive e (var 0) (var 1) (var 2)) (upperPrimitive e (var 0+var 1) (var 1) (var 2))
        (panelMass e (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (.impI (panel_integral_brackets e he _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderPowerIntegralMesh
