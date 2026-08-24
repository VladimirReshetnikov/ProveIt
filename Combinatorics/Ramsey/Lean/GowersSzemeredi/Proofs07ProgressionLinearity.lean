import GowersSzemeredi.Proofs07BohrHom

/-!
# Linearity of the induced map on short progressions

This module proves Gowers's Corollary 7.9.  Lemma 7.8 supplies a Freiman
homomorphism on a Bohr neighborhood.  Repeated addition then makes that map
linear on every sufficiently short symmetric progression; primality of the
modulus lets us express the resulting coefficient as an ambient scalar.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

private lemma centeredAbs_add_le {N : Nat} [NeZero N] (x y : ZMod N) :
    centeredAbs (x + y) ≤ centeredAbs x + centeredAbs y := by
  unfold centeredAbs
  calc
    (x + y).valMinAbs.natAbs ≤
        (x.valMinAbs + y.valMinAbs).natAbs :=
      ZMod.natAbs_valMinAbs_add_le x y
    _ ≤ x.valMinAbs.natAbs + y.valMinAbs.natAbs := Int.natAbs_add_le _ _

@[simp] private lemma centeredAbs_neg {N : Nat} [NeZero N] (x : ZMod N) :
    centeredAbs (-x) = centeredAbs x := by
  unfold centeredAbs
  exact ZMod.natAbs_valMinAbs_neg x

private lemma centeredAbs_nsmul_le {N : Nat} [NeZero N] (n : Nat) (x : ZMod N) :
    centeredAbs (n • x) ≤ n * centeredAbs x := by
  induction n with
  | zero => simp [centeredAbs]
  | succ n ih =>
      rw [succ_nsmul, Nat.succ_mul]
      exact le_trans (centeredAbs_add_le (n • x) x) (Nat.add_le_add_right ih _)

private lemma bohr_symmetric_multiples_subset {N : Nat} [NeZero N]
    (K : Finset (ZMod N)) (alpha : Real) (halpha : 0 < alpha)
    (m : Nat) (hm : 0 < m) (d : ZMod N)
    (hd : d ∈ bohr K (alpha / (32 * Real.pi * m))) :
    symmetricMultiples d m ⊆ bohr K (alpha / (32 * Real.pi)) := by
  classical
  intro z hz
  rw [symmetricMultiples, Finset.mem_image] at hz
  obtain ⟨j, hj, rfl⟩ := hz
  rw [bohr, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  intro r hr
  rw [bohr, Finset.mem_filter] at hd
  have hdr := hd.2 r hr
  have hmReal : (0 : Real) < m := by exact_mod_cast hm
  have hbase : 0 ≤ alpha / (32 * Real.pi * (m : Real)) * N := by positivity
  have hcollapse :
      (m : Real) * (alpha / (32 * Real.pi * (m : Real)) * N) =
        alpha / (32 * Real.pi) * N := by
    field_simp
  have hjBounds : -(m : Int) ≤ j ∧ j ≤ (m : Int) := Finset.mem_Icc.mp hj
  cases j with
  | ofNat n =>
      have hcastNat : ((Int.ofNat n : Int) : ZMod N) = (n : ZMod N) := by norm_num
      rw [hcastNat]
      have hn : n ≤ m := by
        apply Int.ofNat_le.mp
        simpa only [Int.ofNat_eq_natCast] using hjBounds.2
      have hcenter : centeredAbs (r * ((n : ZMod N) * d)) ≤
          n * centeredAbs (r * d) := by
        have hmul : r * ((n : ZMod N) * d) = n • (r * d) := by
          simp [nsmul_eq_mul]
          ring
        rw [hmul]
        exact centeredAbs_nsmul_le n (r * d)
      calc
        (centeredAbs (r * ((n : ZMod N) * d)) : Real) ≤
            n * centeredAbs (r * d) := by exact_mod_cast hcenter
        _ ≤ n * (alpha / (32 * Real.pi * (m : Real)) * N) := by
          gcongr
        _ ≤ m * (alpha / (32 * Real.pi * (m : Real)) * N) := by
          gcongr
        _ = alpha / (32 * Real.pi) * N := hcollapse
  | negSucc n =>
      have hn : n + 1 ≤ m := by
        have := hjBounds.1
        omega
      have hcast : ((Int.negSucc n : Int) : ZMod N) * d =
          -(((n + 1 : Nat) : ZMod N) * d) := by
        push_cast
        ring
      rw [hcast, mul_neg, centeredAbs_neg]
      have hcenter : centeredAbs (r * (((n + 1 : Nat) : ZMod N) * d)) ≤
          (n + 1) * centeredAbs (r * d) := by
        have hmul : r * (((n + 1 : Nat) : ZMod N) * d) =
            (n + 1) • (r * d) := by
          simp [nsmul_eq_mul]
          ring
        rw [hmul]
        exact centeredAbs_nsmul_le (n + 1) (r * d)
      calc
        (centeredAbs (r * (((n + 1 : Nat) : ZMod N) * d)) : Real) ≤
            (n + 1) * centeredAbs (r * d) := by exact_mod_cast hcenter
        _ ≤ (n + 1) * (alpha / (32 * Real.pi * (m : Real)) * N) := by
          gcongr
        _ ≤ m * (alpha / (32 * Real.pi * (m : Real)) * N) := by
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hn) hbase
        _ = alpha / (32 * Real.pi) * N := hcollapse

private lemma freiman_map_nat_multiple {N : Nat} [NeZero N]
    (B : Finset (ZMod N)) (psi : ZMod N → ZMod N)
    (hpsi : FreimanHom 2 B psi) (hpsiZero : psi 0 = 0)
    (d : ZMod N) (m : Nat) (hm : 0 < m)
    (hmem : symmetricMultiples d m ⊆ B) (n : Nat) (hn : n ≤ m) :
    psi ((n : ZMod N) * d) = (n : ZMod N) * psi d := by
  have hzero : (0 : ZMod N) ∈ symmetricMultiples d m := by
    rw [symmetricMultiples, Finset.mem_image]
    refine ⟨0, Finset.mem_Icc.mpr ?_, by simp⟩
    constructor <;> omega
  have hd : d ∈ symmetricMultiples d m := by
    rw [symmetricMultiples, Finset.mem_image]
    refine ⟨1, Finset.mem_Icc.mpr ?_, by simp⟩
    constructor <;> omega
  have hpsi' : IsAddFreimanHom 2 (B : Set (ZMod N)) Set.univ psi := hpsi
  induction n with
  | zero => simpa using hpsiZero
  | succ n ih =>
      have hn' : n ≤ m := Nat.le_trans (Nat.le_succ n) hn
      have hnm : ((n : ZMod N) * d) ∈ symmetricMultiples d m := by
        rw [symmetricMultiples, Finset.mem_image]
        refine ⟨(n : Int), Finset.mem_Icc.mpr ?_, by simp⟩
        constructor <;> omega
      have hsucc : (((n + 1 : Nat) : ZMod N) * d) ∈ symmetricMultiples d m := by
        rw [symmetricMultiples, Finset.mem_image]
        refine ⟨(n + 1 : Int), Finset.mem_Icc.mpr ?_, by simp⟩
        constructor <;> omega
      have hadd : ((n + 1 : Nat) : ZMod N) * d + 0 =
          (n : ZMod N) * d + d := by push_cast; ring
      have hmap := hpsi'.add_eq_add (hmem hsucc) (hmem hzero)
        (hmem hnm) (hmem hd) hadd
      rw [hpsiZero, add_zero, ih hn'] at hmap
      convert hmap using 1
      push_cast
      ring_nf

private lemma freiman_map_int_multiple {N : Nat} [NeZero N]
    (B : Finset (ZMod N)) (psi : ZMod N → ZMod N)
    (hpsi : FreimanHom 2 B psi) (hpsiZero : psi 0 = 0)
    (d : ZMod N) (m : Nat) (hm : 0 < m)
    (hmem : symmetricMultiples d m ⊆ B) (j : Int)
    (hj : j ∈ Finset.Icc (-(m : Int)) (m : Int)) :
    psi ((j : ZMod N) * d) = (j : ZMod N) * psi d := by
  have hzero : (0 : ZMod N) ∈ symmetricMultiples d m := by
    rw [symmetricMultiples, Finset.mem_image]
    refine ⟨0, Finset.mem_Icc.mpr ?_, by simp⟩
    constructor <;> omega
  have hpsi' : IsAddFreimanHom 2 (B : Set (ZMod N)) Set.univ psi := hpsi
  cases j with
  | ofNat n =>
      have hn : n ≤ m := by
        have := (Finset.mem_Icc.mp hj).2
        apply Int.ofNat_le.mp
        simpa only [Int.ofNat_eq_natCast] using this
      have h := freiman_map_nat_multiple B psi hpsi hpsiZero d m hm hmem n hn
      convert h using 1 <;> norm_num
  | negSucc n =>
      have hn : n + 1 ≤ m := by
        have := (Finset.mem_Icc.mp hj).1
        omega
      have hpos : (((n + 1 : Nat) : ZMod N) * d) ∈ symmetricMultiples d m := by
        rw [symmetricMultiples, Finset.mem_image]
        refine ⟨(n + 1 : Int), Finset.mem_Icc.mpr ?_, by simp⟩
        constructor <;> omega
      have hneg : (-(((n + 1 : Nat) : ZMod N) * d)) ∈ symmetricMultiples d m := by
        rw [symmetricMultiples, Finset.mem_image]
        refine ⟨Int.negSucc n, Finset.mem_Icc.mpr ?_, ?_⟩
        · constructor <;> omega
        · push_cast
          ring
      have hadd : -(((n + 1 : Nat) : ZMod N) * d) +
          ((n + 1 : Nat) : ZMod N) * d = 0 + 0 := by ring
      have hmap := hpsi'.add_eq_add (hmem hneg) (hmem hpos)
        (hmem hzero) (hmem hzero) hadd
      have hnat := freiman_map_nat_multiple B psi hpsi hpsiZero d m hm hmem (n + 1) hn
      rw [hpsiZero, add_zero, hnat] at hmap
      have hnegValue : psi (-(((n + 1 : Nat) : ZMod N) * d)) =
          -(((n + 1 : Nat) : ZMod N) * psi d) := by linear_combination hmap
      convert hnegValue using 1
      · push_cast
        ring_nf
      · push_cast
        ring_nf

/- **Gowers, Corollary 7.9.** -/
theorem corollary_7_9_holds : corollary_7_9 := by
  classical
  intro N _ A phi alpha hprime halpha hcard hphi
  dsimp only
  intro m hm d hd
  obtain ⟨_, hBhom⟩ := lemma_7_8_holds N A phi alpha halpha hcard hphi
  obtain ⟨psi, hpsi, hagree⟩ := hBhom
  let K := section7Spectrum A alpha
  let B := bohr K (alpha / (32 * Real.pi))
  have hshort : symmetricMultiples d m ⊆ B :=
    bohr_symmetric_multiples_subset K alpha halpha m hm d hd
  have hzeroShort : (0 : ZMod N) ∈ symmetricMultiples d m := by
    rw [symmetricMultiples, Finset.mem_image]
    refine ⟨0, Finset.mem_Icc.mpr ?_, by simp⟩
    constructor <;> omega
  have hNpos : 0 < N := NeZero.pos N
  have hAcard : 0 < A.card := by
    have : (0 : Real) < A.card := by rw [hcard]; positivity
    exact_mod_cast this
  obtain ⟨a, ha⟩ := Finset.card_pos.mp hAcard
  have hpsiZero : psi 0 = 0 := by
    have hag := hagree a ha a ha (hshort (by simpa using hzeroShort))
    simpa using hag.symm
  letI : Fact N.Prime := ⟨hprime⟩
  by_cases hd0 : d = 0
  · refine ⟨0, ?_⟩
    intro x hx y hy hxy
    have hdiff : x - y = 0 := by
      rw [symmetricMultiples, Finset.mem_image] at hxy
      obtain ⟨j, _, hj⟩ := hxy
      simpa [hd0] using hj.symm
    simpa [hdiff, hpsiZero] using hagree x hx y hy (hshort hxy)
  · refine ⟨psi d / d, ?_⟩
    intro x hx y hy hxy
    have hag := hagree x hx y hy (hshort hxy)
    rw [symmetricMultiples, Finset.mem_image] at hxy
    obtain ⟨j, hj, hjxy⟩ := hxy
    have hlin := freiman_map_int_multiple B psi hpsi hpsiZero d m hm hshort j hj
    rw [← hjxy, hlin] at hag
    rw [← hjxy]
    calc
      phi x - phi y = (j : ZMod N) * psi d := hag
      _ = (psi d / d) * ((j : ZMod N) * d) := by
        field_simp

end LeanProofs.GowersSzemeredi
