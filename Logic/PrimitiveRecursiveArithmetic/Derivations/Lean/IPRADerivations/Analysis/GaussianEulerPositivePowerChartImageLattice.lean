import IPRADerivations.Analysis.GaussianEulerPositivePowerChartCorrectedPanel
import IPRADerivations.Analysis.GaussianEulerUnitSubstitutionFloorCuts
import IPRADerivations.DiophantineNumberTheory.KhinchinConvergence

/-!
# Exact common lattice for finite rational image nodes

A factorial of the sum of the finitely many native denominators is a
common multiple. An additional positive factor gives arbitrarily fine
lattices, while every original node remains exact. The native cut
program extends constantly beyond the final node. This construction
also allows repeated cuts.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerPositivePowerChartImageLattice

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (positive_product)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianEulerUnitSubstitutionFloorCuts (capped capped_below capped_above)
open GaussianPartitionedFiniteSum (increasing)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)
local notation "fact" => DiophantineNumberTheory.KhinchinConvergence.fact
local notation "positiveDenominators" => RationalProductWitness.denominatorGuard

def total (D : PTm 2) (N x : PTm n) : PTm n := ap2 (sumF D) (succ N) x

def meshDenominator (D : PTm 2) (N x J : PTm n) : PTm n := J*fact (total D N x)

def multiplier (D : PTm 2) (i N x J : PTm n) : PTm n :=
  J*quo (fact (total D N x)) (inst2 D i x)

def nodeIndex (P D : PTm 2) (i N x J : PTm n) : PTm n := inst2 P i x*multiplier D i N x J

def absolute (P D : PTm 2) (i N x J : PTm n) : PTm n := nodeIndex P D (capped i N) N x J

@[simp] theorem subst_total {m : ℕ} (σ : Fin n → PTm m) (D : PTm 2) (N x : PTm n) :
    Syn.subst σ (total D N x) = total D (Syn.subst σ N) (Syn.subst σ x) := by simp [total]

@[simp] theorem subst_meshDenominator {m : ℕ} (σ : Fin n → PTm m) (D : PTm 2) (N x J : PTm n) :
    Syn.subst σ (meshDenominator D N x J) = meshDenominator D (Syn.subst σ N) (Syn.subst σ x) (Syn.subst σ J) := by
  simp [meshDenominator]

@[simp] theorem subst_multiplier {m : ℕ} (σ : Fin n → PTm m) (D : PTm 2) (i N x J : PTm n) :
    Syn.subst σ (multiplier D i N x J) = multiplier D (Syn.subst σ i) (Syn.subst σ N) (Syn.subst σ x) (Syn.subst σ J) := by
  simp [multiplier]

@[simp] theorem subst_nodeIndex {m : ℕ} (σ : Fin n → PTm m) (P D : PTm 2) (i N x J : PTm n) :
    Syn.subst σ (nodeIndex P D i N x J) = nodeIndex P D (Syn.subst σ i) (Syn.subst σ N) (Syn.subst σ x) (Syn.subst σ J) := by
  simp [nodeIndex]

@[simp] theorem subst_absolute {m : ℕ} (σ : Fin n → PTm m) (P D : PTm 2) (i N x J : PTm n) :
    Syn.subst σ (absolute P D i N x J) = absolute P D (Syn.subst σ i) (Syn.subst σ N) (Syn.subst σ x) (Syn.subst σ J) := by
  simp [absolute]

theorem mesh_positive (D : PTm 2) (N x J : PTm n) (hJ : Γ ⊢[PRAAx] le one J) :
    Γ ⊢[PRAAx] le one (meshDenominator D N x J) :=
  positive_product _ _ hJ (AnalyticNumberTheory.BlockCross.one_le_fact _)

private theorem lt_succ_of_le {a b : PTm n} (h : Γ ⊢[PRAAx] le a b) : Γ ⊢[PRAAx] lt a (succ b) :=
  (succ_monus_succ _ _).eqTrans h

theorem original_multiplier (D : PTm 2) (i N x J : PTm n)
    (hs : Γ ⊢[PRAAx] positiveDenominators D (succ N) x) (hi : Γ ⊢[PRAAx] le i N) :
    Γ ⊢[PRAAx] meshDenominator D N x J ≐ inst2 D i x*multiplier D i N x J := by
  have h := lt_succ_of_le hi
  have hd := RationalProductWitness.denominator_at D (succ N) x i hs h
  have div := DiophantineNumberTheory.KhinchinConvergence.fact_dvd hd (term_le_sum D h)
  exact (congrMul (.eqRefl J) div).eqTrans (by unfold multiplier total; ipra_ring)

theorem multiplier_positive (D : PTm 2) (i N x J : PTm n)
    (hs : Γ ⊢[PRAAx] positiveDenominators D (succ N) x) (hi : Γ ⊢[PRAAx] le i N) (hJ : Γ ⊢[PRAAx] le one J) :
    Γ ⊢[PRAAx] le one (multiplier D i N x J) := by
  have h := lt_succ_of_le hi
  have hd := RationalProductWitness.denominator_at D (succ N) x i hs h
  have hF : Γ ⊢[PRAAx] fact (total D N x) ≐ inst2 D i x * quo (fact (total D N x)) (inst2 D i x) :=
    DiophantineNumberTheory.KhinchinConvergence.fact_dvd hd (term_le_sum D h)
  have hQ := AnalyticNumberTheory.EulerDomination.quo_pos_of hF (AnalyticNumberTheory.Primes.fact_pos _)
  exact positive_product _ _ hJ (le_congr (.eqRefl _) hQ.eqSymm (zero_lt_succ _))

theorem node_fraction (P D : PTm 2) (i N x J : PTm n)
    (hs : Γ ⊢[PRAAx] positiveDenominators D (succ N) x) (hi : Γ ⊢[PRAAx] le i N) (hJ : Γ ⊢[PRAAx] le one J) :
    Γ ⊢[PRAAx] fraction (nodeIndex P D i N x J) (meshDenominator D N x J) ≐ fraction (inst2 P i x) (inst2 D i x) :=
  (GaussianEulerPositivePowerChartJacobian.fraction_congr (.eqRefl _) (original_multiplier D i N x J hs hi)).eqTrans
    (GaussianEulerPositivePowerChartJacobian.fraction_cancel _ _ _
      (RationalProductWitness.denominator_at D (succ N) x i hs (lt_succ_of_le hi))
      (multiplier_positive D i N x J hs hi hJ))

theorem node_cleared (P D : PTm 2) (i N x J : PTm n)
    (hs : Γ ⊢[PRAAx] positiveDenominators D (succ N) x) (hi : Γ ⊢[PRAAx] le i N) :
    Γ ⊢[PRAAx] inst2 D i x*nodeIndex P D i N x J ≐ meshDenominator D N x J*inst2 P i x :=
  (by unfold nodeIndex; ipra_ring :
    Γ ⊢[PRAAx] inst2 D i x*nodeIndex P D i N x J ≐ (inst2 D i x*multiplier D i N x J)*inst2 P i x).eqTrans
    (congrMul (original_multiplier D i N x J hs hi).eqSymm (.eqRefl _))

theorem node_order (P D : PTm 2) (i j N x J : PTm n)
    (hs : Γ ⊢[PRAAx] positiveDenominators D (succ N) x) (hi : Γ ⊢[PRAAx] le i N) (hj : Γ ⊢[PRAAx] le j N)
    (hij : Γ ⊢[PRAAx] le (inst2 P i x*inst2 D j x) (inst2 P j x*inst2 D i x)) :
    Γ ⊢[PRAAx] le (nodeIndex P D i N x J) (nodeIndex P D j N x J) := by
  let M := meshDenominator D N x J
  let A := nodeIndex P D i N x J
  let B := nodeIndex P D j N x J
  let d := inst2 D i x
  let e := inst2 D j x
  have hA := natEq (node_cleared P D i N x J hs hi)
  have hB := natEq (node_cleared P D j N x J hs hj)
  have left : Γ ⊢[PRAAx] M*(inst2 P i x*e) ≐ (d*e)*A := by
    apply deriveNat
    dsimp only [M,A,d,e]; ipra_simps
    linear_combination -𝔞 (inst2 D j x)*hA
  have right : Γ ⊢[PRAAx] M*(inst2 P j x*d) ≐ (d*e)*B := by
    apply deriveNat
    dsimp only [M,B,d,e]; ipra_simps
    linear_combination -𝔞 (inst2 D i x)*hB
  have clear := mul_le_mul_right M hij
  have ordered : Γ ⊢[PRAAx] le ((d*e)*A) ((d*e)*B) :=
    le_congr ((mul_comm _ M).eqTrans left) ((mul_comm _ M).eqTrans right) clear
  exact RationalValueBounds.positive_cancel
    (positive_product _ _ (RationalProductWitness.denominator_at D (succ N) x i hs (lt_succ_of_le hi))
      (RationalProductWitness.denominator_at D (succ N) x j hs (lt_succ_of_le hj))) ordered

theorem node_congr {P D : PTm 2} {i j N x J : PTm n} (e : Γ ⊢[PRAAx] i ≐ j) :
    Γ ⊢[PRAAx] nodeIndex P D i N x J ≐ nodeIndex P D j N x J := by
  simpa using Prf.eqCongr1 (nodeIndex P D (var 0) (Syn.shift N) (Syn.shift x) (Syn.shift J)) e

theorem absolute_below (P D : PTm 2) (i N x J : PTm n) (hi : Γ ⊢[PRAAx] le i N) :
    Γ ⊢[PRAAx] absolute P D i N x J ≐ nodeIndex P D i N x J := node_congr (capped_below i N hi)

theorem absolute_above (P D : PTm 2) (i N x J : PTm n) (hi : Γ ⊢[PRAAx] le N i) :
    Γ ⊢[PRAAx] absolute P D i N x J ≐ nodeIndex P D N N x J := node_congr (capped_above i N hi)

def cutData (N x J : PTm n) : PTm n := pairT N (pairT x J)

private def absoluteReader (P D : PTm 2) (i y : PTm n) : PTm n :=
  absolute P D i (fstT y) (fstT (sndT y)) (sndT (sndT y))

def absoluteF (P D : PTm 2) : PR 2 := PTm.toPR (absoluteReader P D (var 0) (var 1))

def cutF (P D : PTm 2) : PR 2 := PTm.toPR
  (monus (ap2 (absoluteF P D) (var 0) (var 1)) (ap2 (absoluteF P D) zero (var 1)))

def start (P D : PTm 2) (N x J : PTm n) : PTm n := absolute P D zero N x J

def relative (P D : PTm 2) (i N x J : PTm n) : PTm n := monus (absolute P D i N x J) (start P D N x J)

@[simp] theorem subst_cutData {m : ℕ} (σ : Fin n → PTm m) (N x J : PTm n) :
    Syn.subst σ (cutData N x J) = cutData (Syn.subst σ N) (Syn.subst σ x) (Syn.subst σ J) := by
  simp [cutData]

@[simp] theorem subst_start {m : ℕ} (σ : Fin n → PTm m) (P D : PTm 2) (N x J : PTm n) :
    Syn.subst σ (start P D N x J) = start P D (Syn.subst σ N) (Syn.subst σ x) (Syn.subst σ J) := by
  simp [start]

@[simp] theorem subst_relative {m : ℕ} (σ : Fin n → PTm m) (P D : PTm 2) (i N x J : PTm n) :
    Syn.subst σ (relative P D i N x J) = relative P D (Syn.subst σ i) (Syn.subst σ N) (Syn.subst σ x) (Syn.subst σ J) := by
  simp [relative]

theorem absolute_at (P D : PTm 2) (i N x J : PTm n) : Γ ⊢[PRAAx]
    ap2 (absoluteF P D) i (cutData N x J) ≐ absolute P D i N x J := by
  have compiled : Γ ⊢[PRAAx] ap2 (absoluteF P D) i (cutData N x J) ≐ absoluteReader P D i (cutData N x J) := by
    simpa [absoluteF,ap2,absoluteReader] using
      toPR_eq (Γ := Γ) (absoluteReader P D (var 0) (var 1) : PTm 2) ![i,cutData N x J]
  have hN : Γ ⊢[PRAAx] fstT (cutData N x J) ≐ N := fst_pair _ _
  have hx : Γ ⊢[PRAAx] fstT (sndT (cutData N x J)) ≐ x :=
    (congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)
  have hJ : Γ ⊢[PRAAx] sndT (sndT (cutData N x J)) ≐ J :=
    (congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)
  apply compiled.eqTrans
  simpa [absoluteReader] using Prf.eqCongr (Ax := PRAAx) (Γ := Γ)
    (absolute P D (var 0) (var 1) (var 2) (var 3) : PTm 4)
    (σ := ![i, fstT (cutData N x J),fstT (sndT (cutData N x J)),sndT (sndT (cutData N x J))])
    (σ' := ![i,N,x,J]) (fun j => by fin_cases j; exact .eqRefl _; exact hN; exact hx; exact hJ)

theorem cut_at (P D : PTm 2) (i N x J : PTm n) : Γ ⊢[PRAAx]
    ap2 (cutF P D) i (cutData N x J) ≐ relative P D i N x J := by
  have compiled : Γ ⊢[PRAAx] ap2 (cutF P D) i (cutData N x J) ≐
      monus (ap2 (absoluteF P D) i (cutData N x J)) (ap2 (absoluteF P D) zero (cutData N x J)) := by
    have h := toPR_eq (Γ := Γ)
      (monus (ap2 (absoluteF P D) (var 0) (var 1)) (ap2 (absoluteF P D) zero (var 1)) : PTm 2) ![i,cutData N x J]
    have decode : Syn.subst (![i,cutData N x J] : Fin 2 → PTm n)
        (monus (ap2 (absoluteF P D) (var 0) (var 1)) (ap2 (absoluteF P D) zero (var 1))) =
        monus (ap2 (absoluteF P D) i (cutData N x J)) (ap2 (absoluteF P D) zero (cutData N x J)) := by simp
    rw [decode] at h
    exact h
  exact compiled.eqTrans (congrMonus (absolute_at P D i N x J) (absolute_at P D zero N x J))

theorem cut_zero (P D : PTm 2) (N x J : PTm n) : Γ ⊢[PRAAx] ap2 (cutF P D) zero (cutData N x J) ≐ zero :=
  (cut_at P D zero N x J).eqTrans (monus_self _)

def ordered (P D : PTm 2) (N x : PTm n) : Fm PTm n :=
  .all (.all ((le (var 1) (var 0) ⋏ le (var 0) (Syn.shift (Syn.shift N))) ⟶
    le (inst2 P (var 1) (Syn.shift (Syn.shift x))*inst2 D (var 0) (Syn.shift (Syn.shift x)))
      (inst2 P (var 0) (Syn.shift (Syn.shift x))*inst2 D (var 1) (Syn.shift (Syn.shift x)))))

@[simp] theorem subst_ordered {m : ℕ} (σ : Fin n → PTm m) (P D : PTm 2) (N x : PTm n) :
    (ordered P D N x).subst σ = ordered P D (Syn.subst σ N) (Syn.subst σ x) := by
  simp [ordered,Syn.subst_shift,Syn.shift_subst]

theorem ordered_at (P D : PTm 2) (i j N x : PTm n) (hs : Γ ⊢[PRAAx] ordered P D N x)
    (hi : Γ ⊢[PRAAx] le i j) (hj : Γ ⊢[PRAAx] le j N) :
    Γ ⊢[PRAAx] le (inst2 P i x*inst2 D j x) (inst2 P j x*inst2 D i x) := by
  have rule : Γ ⊢[PRAAx] (le i j ⋏ le j N) ⟶
      le (inst2 P i x*inst2 D j x) (inst2 P j x*inst2 D i x) := by
    simpa [ordered,Syn.subst_shift,Syn.shift_subst,Syn.shift,Syn.subst_subst,Function.comp_def] using (hs.allE i).allE j
  exact .impE rule (.andI hi hj)

theorem absolute_step (P D : PTm 2) (i N x J : PTm n) (hs : Γ ⊢[PRAAx] positiveDenominators D (succ N) x)
    (ho : Γ ⊢[PRAAx] ordered P D N x) : Γ ⊢[PRAAx] le (absolute P D i N x J) (absolute P D (succ i) N x J) := by
  refine .orE (lt_or_le i N) ?_ ?_
  · have hi : (lt i N)::Γ ⊢[PRAAx] lt i N := Prf.hyp0
    have below := le_of_lt hi
    exact le_congr (absolute_below P D i N x J below).eqSymm (absolute_below P D (succ i) N x J hi).eqSymm
      (node_order P D i (succ i) N x J hs.wk below hi (ordered_at P D i (succ i) N x ho.wk (le_succ_self _) hi))
  · have hi : (le N i)::Γ ⊢[PRAAx] le N i := Prf.hyp0
    exact le_congr (absolute_above P D i N x J hi).eqSymm
      (absolute_above P D (succ i) N x J (le_trans hi (le_succ_self i))).eqSymm (le_refl _)

theorem cut_increasing (P D : PTm 2) (N x J : PTm n) (hs : Γ ⊢[PRAAx] positiveDenominators D (succ N) x)
    (ho : Γ ⊢[PRAAx] ordered P D N x) : Γ ⊢[PRAAx] increasing (cutF P D) (cutData N x J) := by
  have h : Γ.map Fm.shift ⊢[PRAAx] positiveDenominators D (succ (Syn.shift N)) (Syn.shift x) := by
    simpa [Fm.shift,Syn.shift] using hs.shift
  have o : Γ.map Fm.shift ⊢[PRAAx] ordered P D (Syn.shift N) (Syn.shift x) := by
    simpa [Fm.shift,Syn.shift] using ho.shift
  refine .allI ?_
  simpa only [increasing,subst_cutData,Syn.shift] using le_congr
    (cut_at P D (var 0) (Syn.shift N) (Syn.shift x) (Syn.shift J)).eqSymm
    (cut_at P D (succ (var 0)) (Syn.shift N) (Syn.shift x) (Syn.shift J)).eqSymm
    (DiophantineNumberTheory.FractionCount.monus_mono
      (c := start P D (Syn.shift N) (Syn.shift x) (Syn.shift J))
      (absolute_step P D (var 0) (Syn.shift N) (Syn.shift x) (Syn.shift J) h o))

theorem start_le_absolute (P D : PTm 2) (i N x J : PTm n)
    (hs : Γ ⊢[PRAAx] positiveDenominators D (succ N) x) (ho : Γ ⊢[PRAAx] ordered P D N x)
    (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx] le (start P D N x J) (absolute P D i N x J) := by
  exact le_congr (absolute_below P D zero N x J (zero_le N)).eqSymm (absolute_below P D i N x J hi).eqSymm
    (node_order P D zero i N x J hs (zero_le N) hi (ordered_at P D zero i N x ho (zero_le i) hi))

theorem absolute_as_relative (P D : PTm 2) (i N x J : PTm n)
    (hs : Γ ⊢[PRAAx] positiveDenominators D (succ N) x) (ho : Γ ⊢[PRAAx] ordered P D N x)
    (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx] start P D N x J + ap2 (cutF P D) i (cutData N x J) ≐ absolute P D i N x J :=
  (congrAdd (.eqRefl _) (cut_at P D i N x J)).eqTrans (eq_add_of_le (start_le_absolute P D i N x J hs ho hi)).eqSymm

end LeanProofs.IPRA.Analysis.GaussianEulerPositivePowerChartImageLattice
