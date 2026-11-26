import IPRADerivations.Analysis.Euler.PositiveAxis.GaussianEulerUnitSubstitutionFloorCuts
import IPRADerivations.Analysis.Euler.PositiveAxis.GaussianEulerUnitSubstitutionReversedDensity
import IPRADerivations.Analysis.Integration.GaussianPartitionedFiniteSumDistance
import IPRADerivations.Analysis.Euler.PositiveAxis.GaussianEulerUnitKernelCompactName

/-!
# Native indices of the original floor-cut lattice

The finite-sum block offsets start at zero. Adding the absolute
left cut gives the actual lattice index, and its native integer
bounds are the corresponding two absolute original floor cuts.
The same subtraction of the first cut leaves every block width exact.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerUnitSubstitutionLatticeGeometry

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerUnitSubstitutionFloorCuts (absoluteF cut cutF data original_absolute_at original_at relativeCut)
open GaussianEulerUnitDecayInput (compactDenominator clock)
open GaussianPartitionedFiniteSumDistance (blockLength)
open GaussianCoefficientNameBounds (unit)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def source (k N z R B a C E T M : PTm n) : Fm PTm n :=
  GaussianEulerUnitSubstitutionDensity.source z R B a C E T N ⋏
    (le ((two*two)*compactDenominator E T*N) (unit (clock k E T)) ⋏
      le (two*(two*compactDenominator E T)) M)
def disk (E T : PTm n) : PTm n := two*(two*compactDenominator E T)
def start (k N a C E T M : PTm n) : PTm n := cut zero k N a C E T M
def count (k N a C E T M : PTm n) : PTm n := ap2 cutF N (data k N a C E T M)

@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (k N z R B a C E T M : PTm n) :
    (source k N z R B a C E T M).subst σ = source (Syn.subst σ k) (Syn.subst σ N) (Syn.subst σ z)
      (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ a) (Syn.subst σ C) (Syn.subst σ E) (Syn.subst σ T) (Syn.subst σ M) := by
  simp [source]
@[simp] theorem subst_disk {m : ℕ} (σ : Fin n → PTm m) (E T : PTm n) :
    Syn.subst σ (disk E T) = disk (Syn.subst σ E) (Syn.subst σ T) := by simp [disk]
@[simp] theorem subst_start {m : ℕ} (σ : Fin n → PTm m) (k N a C E T M : PTm n) :
    Syn.subst σ (start k N a C E T M) = start (Syn.subst σ k) (Syn.subst σ N) (Syn.subst σ a)
      (Syn.subst σ C) (Syn.subst σ E) (Syn.subst σ T) (Syn.subst σ M) := by simp [start]
@[simp] theorem subst_count {m : ℕ} (σ : Fin n → PTm m) (k N a C E T M : PTm n) :
    Syn.subst σ (count k N a C E T M) = count (Syn.subst σ k) (Syn.subst σ N) (Syn.subst σ a)
      (Syn.subst σ C) (Syn.subst σ E) (Syn.subst σ T) (Syn.subst σ M) := by simp [count]

theorem cuts_source (k N z R B a C E T M : PTm n) (h : Γ ⊢[PRAAx] source k N z R B a C E T M) : Γ ⊢[PRAAx]
    GaussianEulerUnitSubstitutionFloorCuts.source k N a C E T M := by
  have s := h.andE₁
  exact .andI (.andI s.andE₁.andE₂.andE₁ (.andI s.andE₁.andE₁.andE₂.andE₁
    (.andI (GaussianEulerUnitSubstitutionReversedDensity.top_positive _ _ _ _ _ _ _ _ s) s.andE₁.andE₂.andE₂)))
    (.andI s.andE₂.andE₁ h.andE₂)

theorem disk_widens (E T : PTm n) : Γ ⊢[PRAAx] le (compactDenominator E T) (disk E T) :=
  le_of_eq_add (d := (two+one)*compactDenominator E T) (by unfold disk; ipra_ring)

theorem disk_positive (E T : PTm n) : Γ ⊢[PRAAx] le one (disk E T) :=
  le_trans (GaussianEulerUnitDecayInput.denominator_positive E T) (disk_widens E T)

theorem denominator_positive (k N z R B a C E T M : PTm n) (h : Γ ⊢[PRAAx] source k N z R B a C E T M) :
    Γ ⊢[PRAAx] le one M :=
  le_trans (disk_positive E T) h.andE₂.andE₂

private theorem from_zero (F : PR 2) (x i : PTm n) (h : Γ ⊢[PRAAx] GaussianPartitionedFiniteSum.increasing F x) :
    Γ ⊢[PRAAx] le (ap2 F zero x) (ap2 F i x) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] GaussianPartitionedFiniteSum.increasing F (Syn.shift x) :=
    by simpa [Fm.shift,Syn.shift] using h.shift
  have steps : Γ ⊢[PRAAx] .all (le (ap2 F zero (Syn.shift x)) (ap2 F (var 0) (Syn.shift x))) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simpa only [subst_le,subst_ap2,ConciseIPRA.PTm.subst_zero,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
        le_refl (Γ := Γ) (ap2 F zero x)
    · simp only [subst_le,subst_ap2,ConciseIPRA.PTm.subst_zero,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact le_trans Prf.hyp0 (GaussianPartitionedFiniteSum.cut_step (Γ := _ :: Γ.map Fm.shift) F (Syn.shift x) (var 0) hs.wk)
  simpa only [subst_le,subst_ap2,ConciseIPRA.PTm.subst_zero,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using steps.allE i

theorem start_le_cut (i k N a C E T M : PTm n) (hs : Γ ⊢[PRAAx] GaussianEulerUnitSubstitutionFloorCuts.source k N a C E T M) :
    Γ ⊢[PRAAx] le (start k N a C E T M) (cut i k N a C E T M) :=
  le_congr (original_absolute_at zero k N a C E T M) (original_absolute_at i k N a C E T M)
    (from_zero absoluteF (data k N a C E T M) i (GaussianEulerUnitSubstitutionFloorCuts.original_absolute_increasing k N a C E T M hs))

theorem absolute_from_relative (i k N a C E T M : PTm n) (hs : Γ ⊢[PRAAx] GaussianEulerUnitSubstitutionFloorCuts.source k N a C E T M) :
    Γ ⊢[PRAAx] start k N a C E T M+ap2 cutF i (data k N a C E T M) ≐ cut i k N a C E T M :=
  (congrAdd (.eqRefl _) (original_at i k N a C E T M)).eqTrans (eq_add_of_le (start_le_cut i k N a C E T M hs)).eqSymm

theorem original_width_at (i k N a C E T M : PTm n) (hs : Γ ⊢[PRAAx] GaussianEulerUnitSubstitutionFloorCuts.source k N a C E T M) :
    Γ ⊢[PRAAx] blockLength cutF i (data k N a C E T M) ≐
      monus (cut (succ i) k N a C E T M) (cut i k N a C E T M) := by
  let d := data k N a C E T M
  let L := start k N a C E T M
  have u := ((add_comm (ap2 cutF (succ i) d) L).eqTrans (absolute_from_relative (succ i) k N a C E T M hs)).eqSymm
  have v := ((add_comm (ap2 cutF i d) L).eqTrans (absolute_from_relative i k N a C E T M hs)).eqSymm
  exact ((congrMonus u v).eqTrans (monus_add_add _ _ _)).eqSymm

theorem original_positions (i j k N a C E T M : PTm n)
    (hs : Γ ⊢[PRAAx] GaussianEulerUnitSubstitutionFloorCuts.source k N a C E T M)
    (hj : Γ ⊢[PRAAx] lt j (blockLength cutF i (data k N a C E T M))) : Γ ⊢[PRAAx]
    le (cut i k N a C E T M) (start k N a C E T M+(ap2 cutF i (data k N a C E T M)+j)) ⋏
    lt (start k N a C E T M+(ap2 cutF i (data k N a C E T M)+j)) (cut (succ i) k N a C E T M) := by
  let L := start k N a C E T M
  let r := ap2 cutF i (data k N a C E T M)
  let u := cut i k N a C E T M
  let v := cut (succ i) k N a C E T M
  have eq : Γ ⊢[PRAAx] L+(r+j) ≐ u+j :=
    (add_assoc L r j).eqSymm.eqTrans (congrAdd (absolute_from_relative i k N a C E T M hs) (.eqRefl _))
  have h : Γ ⊢[PRAAx] lt j (monus v u) := lt_congr (.eqRefl _) (original_width_at i k N a C E T M hs) hj
  have step := GaussianEulerUnitSubstitutionFloorCuts.original_cut_step i k N a C E T M hs
  have finish : Γ ⊢[PRAAx] lt (u+j) v := by
    have e := natEq (eq_add_of_le step)
    change Γ ⊢[PRAAx] le (succ (u+j)) v
    have h' : Γ ⊢[PRAAx] le (succ j) (monus v u) := h
    ipra_le sl h' with e
  exact .andI (le_congr (.eqRefl _) eq.eqSymm (le_add_right _ _)) (lt_congr eq.eqSymm (.eqRefl _) finish)

theorem original_count_bound (k N a C E T M : PTm n)
    (hs : Γ ⊢[PRAAx] GaussianEulerUnitSubstitutionFloorCuts.source k N a C E T M) : Γ ⊢[PRAAx] le (count k N a C E T M) M := by
  have last := GaussianEulerUnitSubstitutionFloorCuts.original_cut_source N k N a C E T M hs
  exact le_trans (le_congr (original_at N k N a C E T M).eqSymm (.eqRefl _) (GaussianMonicResidualRadius.monus_le_left _ _))
    (le_of_lt last.andE₁.andE₂)

theorem compact_interval_source (k N z R B a C E T M : PTm n) (h : Γ ⊢[PRAAx] source k N z R B a C E T M) :
    Γ ⊢[PRAAx] GaussianEulerUnitKernelCompactName.source z R B (start k N a C E T M) (count k N a C E T M) M (disk E T) := by
  let J := disk E T
  let L := start k N a C E T M
  let K := count k N a C E T M
  have hs := cuts_source k N z R B a C E T M h
  have hz := h.andE₁.andE₁.andE₁
  have hl := GaussianEulerUnitSubstitutionFloorCuts.original_cut_source zero k N a C E T M hs
  have hr := GaussianEulerUnitSubstitutionFloorCuts.original_cut_source N k N a C E T M hs
  have eq : Γ ⊢[PRAAx] L+K ≐ cut N k N a C E T M := absolute_from_relative N k N a C E T M hs
  have right := le_congr (congrAdd (congrMul (.eqRefl J) eq.eqSymm) (.eqRefl _)) (.eqRefl _) hr.andE₂.andE₂.andE₂
  exact .andI (.andI hz.andE₁ (.andI (disk_positive E T) hz.andE₂.andE₂))
    (.andI (denominator_positive k N z R B a C E T M h) (.andI hl.andE₂.andE₂.andE₁ right))

theorem actual_original_unit_lattice_count_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (GaussianEulerUnitSubstitutionFloorCuts.source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      le (count (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) (var 6)) :=
  closeUniv 7 (.impI (original_count_bound _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerUnitSubstitutionLatticeGeometry
