import GowersSzemeredi.Proofs07BalogSzemeredi
import GowersSzemeredi.Proofs07FreimanRestriction

/-!
# Additive restrictions with an order-eight Freiman model

This file proves Corollary 7.6 by applying the group-valued
Balog--Szemerédi proposition to the graph and then Lemma 7.5.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Pointwise Combinatorics.Additive
open Finset

namespace LeanProofs.GowersSzemeredi

private lemma cor76_mem_functionGraph {N : Nat} [NeZero N]
    (B : Finset (ZMod N)) (phi : ZMod N → ZMod N) (p : ZMod N × ZMod N) :
    p ∈ functionGraph B phi ↔ p.1 ∈ B ∧ p.2 = phi p.1 := by
  classical
  simp [functionGraph, Prod.ext_iff, eq_comm]

private lemma cor76_card_functionGraph {N : Nat} [NeZero N]
    (B : Finset (ZMod N)) (phi : ZMod N → ZMod N) :
    (functionGraph B phi).card = B.card := by
  classical
  unfold functionGraph
  rw [Finset.card_image_iff.mpr]
  intro x _ y _ h
  exact congrArg Prod.fst h

private lemma cor76_count_le_graph_energy {N : Nat} [NeZero N]
    (B : Finset (ZMod N)) (phi : ZMod N → ZMod N) :
    phiAdditiveCount B phi ≤
      Finset.addEnergy (functionGraph B phi) (functionGraph B phi) := by
  classical
  unfold phiAdditiveCount countWhere Finset.addEnergy
  let graphPoint : ZMod N → ZMod N × ZMod N := fun x => (x, phi x)
  let toEnergy : (Fin 4 → ZMod N) →
      ((ZMod N × ZMod N) × (ZMod N × ZMod N)) ×
        ((ZMod N × ZMod N) × (ZMod N × ZMod N)) :=
    fun q => ((graphPoint (q 0), graphPoint (q 2)),
      (graphPoint (q 1), graphPoint (q 3)))
  refine Finset.card_le_card_of_injOn toEnergy ?_ ?_
  · intro q hq
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    rcases hq with ⟨hqB, hqadd, hqphi⟩
    constructor
    · simp only [Finset.mem_product]
      repeat' constructor
      all_goals
        simp only [toEnergy, graphPoint, functionGraph, Finset.mem_image]
        exact ⟨_, hqB _, rfl⟩
    · exact Prod.ext hqadd hqphi
  · intro q hq r hr hqr
    simp only [toEnergy, graphPoint, Prod.mk.injEq] at hqr
    funext i
    fin_cases i <;> tauto

private lemma cor76_extract_subgraph {N : Nat} [NeZero N]
    (B0 : Finset (ZMod N)) (phi : ZMod N → ZMod N)
    (Gamma1 : Finset (ZMod N × ZMod N))
    (hsub : Gamma1 ⊆ functionGraph B0 phi) :
    let B1 := Gamma1.image Prod.fst
    B1 ⊆ B0 ∧ functionGraph B1 phi = Gamma1 ∧ B1.card = Gamma1.card := by
  classical
  dsimp only
  let B1 := Gamma1.image Prod.fst
  have hB1sub : B1 ⊆ B0 := by
    intro x hx
    obtain ⟨p, hp, hpx⟩ := Finset.mem_image.mp hx
    have hpgraph := (cor76_mem_functionGraph B0 phi p).1 (hsub hp)
    rw [← hpx]
    exact hpgraph.1
  have hgraph : functionGraph B1 phi = Gamma1 := by
    ext p
    constructor
    · intro hp
      have hp' := (cor76_mem_functionGraph B1 phi p).1 hp
      obtain ⟨q, hq, hqp⟩ := Finset.mem_image.mp hp'.1
      have hq' := (cor76_mem_functionGraph B0 phi q).1 (hsub hq)
      have hpq : p = q := by
        apply Prod.ext
        · exact hqp.symm
        · calc
            p.2 = phi p.1 := hp'.2
            _ = phi q.1 := congrArg phi hqp.symm
            _ = q.2 := hq'.2.symm
      simpa [hpq] using hq
    · intro hp
      have hp' := (cor76_mem_functionGraph B0 phi p).1 (hsub hp)
      exact (cor76_mem_functionGraph B1 phi p).2
        ⟨Finset.mem_image.2 ⟨p, hp, rfl⟩, hp'.2⟩
  refine ⟨hB1sub, hgraph, ?_⟩
  rw [← cor76_card_functionGraph B1 phi, hgraph]

theorem corollary_7_6_holds : corollary_7_6 := by
  intro N _ B0 phi alpha gamma hprime halpha hgamma hB0card hadd
  classical
  let Gamma0 := functionGraph B0 phi
  have hGamma0cardNat : Gamma0.card = B0.card := by
    exact cor76_card_functionGraph B0 phi
  have hGamma0card : (Gamma0.card : Real) = alpha * N := by
    rw [hGamma0cardNat, hB0card]
  have hcountEnergyNat := cor76_count_le_graph_energy B0 phi
  have hcountEnergy :
      (phiAdditiveCount B0 phi : Real) ≤
        Finset.addEnergy Gamma0 Gamma0 := by
    exact_mod_cast hcountEnergyNat
  have henergy :
      gamma * (Gamma0.card : Real) ^ 3 ≤ Finset.addEnergy Gamma0 Gamma0 := by
    calc
      gamma * (Gamma0.card : Real) ^ 3 =
          gamma * (alpha * N) ^ 3 := by rw [hGamma0card]
      _ ≤ (phiAdditiveCount B0 phi : Real) := hadd
      _ ≤ (Finset.addEnergy Gamma0 Gamma0 : Real) := hcountEnergy
  obtain ⟨Gamma1, hGamma1sub, hGamma1size, hGamma1diff⟩ :=
    proposition_7_3_group_holds Gamma0 gamma hgamma henergy
  let B1 := Gamma1.image Prod.fst
  obtain ⟨hB1sub, hB1graph, hB1card⟩ :=
    cor76_extract_subgraph B0 phi Gamma1 hGamma1sub
  let C : Real := (2 : Real) ^ (58 : Nat) * gamma ^ (-(36 : Real))
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  have hsmall :
      (((functionGraph B1 phi - functionGraph B1 phi).card : Real) ≤
        C * (functionGraph B1 phi).card) := by
    rw [hB1graph]
    have hcoefPos :
        0 < (2 : Real) ^ (-(20 : Real)) * gamma ^ (12 : Nat) := by
      positivity
    have hGamma0le :
        (Gamma0.card : Real) ≤
          (Gamma1.card : Real) /
            ((2 : Real) ^ (-(20 : Real)) * gamma ^ (12 : Nat)) := by
      apply (le_div_iff₀ hcoefPos).2
      simpa only [mul_comm, mul_left_comm, mul_assoc] using hGamma1size
    calc
      ((Gamma1 - Gamma1).card : Real) ≤
          (2 : Real) ^ (38 : Nat) * gamma ^ (-(24 : Real)) *
            Gamma0.card := hGamma1diff
      _ ≤ (2 : Real) ^ (38 : Nat) * gamma ^ (-(24 : Real)) *
            ((Gamma1.card : Real) /
              ((2 : Real) ^ (-(20 : Real)) * gamma ^ (12 : Nat))) := by
        gcongr
      _ = C * Gamma1.card := by
        dsimp only [C]
        rw [Real.rpow_neg (le_of_lt hgamma)]
        rw [Real.rpow_neg (show (0 : Real) ≤ 2 by norm_num)]
        norm_num [Real.rpow_natCast]
        field_simp
        ring
  obtain ⟨B, hBB1, hBsize, hFreiman⟩ :=
    lemma_7_5_holds N 8 B1 phi C hprime (by norm_num) hC hsmall
  refine ⟨B, hBB1.trans hB1sub, ?_, hFreiman⟩
  let D : Real := 8 * (8 : Real) * C ^ (4 * 8)
  have hDpos : 0 < D := by
    dsimp only [D]
    positivity
  have hBsize' : (B1.card : Real) / D ≤ B.card := by
    norm_num [D] at hBsize ⊢
    exact hBsize
  have hB1lower :
      (2 : Real) ^ (-(20 : Real)) * gamma ^ (12 : Nat) *
          (alpha * N) ≤ B1.card := by
    calc
      (2 : Real) ^ (-(20 : Real)) * gamma ^ (12 : Nat) *
          (alpha * N) =
          (2 : Real) ^ (-(20 : Real)) * gamma ^ (12 : Nat) *
            Gamma0.card := by rw [hGamma0card]
      _ ≤ Gamma1.card := hGamma1size
      _ = B1.card := by rw [hB1card]
  calc
    (2 : Real) ^ (-(1882 : Real)) * gamma ^ (1164 : Nat) * alpha * N =
        ((2 : Real) ^ (-(20 : Real)) * gamma ^ (12 : Nat) *
          (alpha * N)) / D := by
      have hpow2 : (2 : Real) ^ (1882 : Nat) =
          (2 : Real) ^ (20 : Nat) *
            ((2 : Real) ^ (6 : Nat) *
              ((2 : Real) ^ (58 : Nat)) ^ (32 : Nat)) := by
        rw [show (1882 : Nat) = 20 + (6 + 58 * 32) by norm_num]
        rw [pow_add, pow_add, pow_mul]
      dsimp only [D, C]
      norm_num only [show 4 * 8 = 32 by norm_num]
      rw [Real.rpow_neg (le_of_lt hgamma)]
      rw [Real.rpow_neg (show (0 : Real) ≤ 2 by norm_num)]
      norm_num [Real.rpow_natCast]
      field_simp
      rw [hpow2]
      ring
    _ ≤ (B1.card : Real) / D :=
      (div_le_div_iff_of_pos_right hDpos).2 hB1lower
    _ ≤ B.card := hBsize'

end LeanProofs.GowersSzemeredi
