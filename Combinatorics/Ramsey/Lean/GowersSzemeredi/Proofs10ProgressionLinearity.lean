import GowersSzemeredi.Proofs07ProgressionLinearity
import GowersSzemeredi.Section10

/-!
# Scalar linearity for the multifunction Bohr model

This module proves Gowers's Corollary 10.14.  Its algebraic core is the
short-progression Freiman argument already used for Corollary 7.9; the only
additional work is deriving nonnegativity of the Bohr radius from the
existence of the smaller Bohr element.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

private lemma cor1014_centeredAbs_add_le {N : Nat} [NeZero N] (x y : ZMod N) :
    centeredAbs (x + y) ≤ centeredAbs x + centeredAbs y := by
  unfold centeredAbs
  calc
    (x + y).valMinAbs.natAbs ≤
        (x.valMinAbs + y.valMinAbs).natAbs :=
      ZMod.natAbs_valMinAbs_add_le x y
    _ ≤ x.valMinAbs.natAbs + y.valMinAbs.natAbs := Int.natAbs_add_le _ _

@[simp] private lemma cor1014_centeredAbs_neg {N : Nat} [NeZero N]
    (x : ZMod N) : centeredAbs (-x) = centeredAbs x := by
  unfold centeredAbs
  exact ZMod.natAbs_valMinAbs_neg x

private lemma cor1014_centeredAbs_nsmul_le {N : Nat} [NeZero N]
    (n : Nat) (x : ZMod N) : centeredAbs (n • x) ≤ n * centeredAbs x := by
  induction n with
  | zero => simp [centeredAbs]
  | succ n ih =>
      rw [succ_nsmul, Nat.succ_mul]
      exact le_trans (cor1014_centeredAbs_add_le (n • x) x)
        (Nat.add_le_add_right ih _)

private lemma cor1014_small_bohr_nonnegative {N : Nat} [NeZero N]
    (K : Finset (ZMod N)) (zeta : Real) (m : Nat) (hm : 0 < m)
    (d : ZMod N) (hd : d ∈ bohr K (zeta / m)) (hK : K.Nonempty) :
    0 ≤ zeta := by
  obtain ⟨r, hr⟩ := hK
  rw [bohr, Finset.mem_filter] at hd
  have hbound := hd.2 r hr
  have hmReal : (0 : Real) < m := by exact_mod_cast hm
  have hNReal : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  by_contra hzeta
  have hzetaNeg : zeta < 0 := lt_of_not_ge hzeta
  have hrhs : zeta / (m : Real) * N < 0 :=
    mul_neg_of_neg_of_pos (div_neg_of_neg_of_pos hzetaNeg hmReal) hNReal
  have hlhs : (0 : Real) ≤ centeredAbs (r * d) := by positivity
  linarith

private lemma cor1014_symmetric_multiples_subset {N : Nat} [NeZero N]
    (K : Finset (ZMod N)) (zeta : Real) (hzeta : 0 ≤ zeta)
    (m : Nat) (hm : 0 < m) (d : ZMod N)
    (hd : d ∈ bohr K (zeta / m)) :
    section10SymmetricMultiples d m ⊆ bohr K zeta := by
  classical
  intro z hz
  rw [section10SymmetricMultiples, Finset.mem_image] at hz
  obtain ⟨j, hj, rfl⟩ := hz
  rw [bohr, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  intro r hr
  rw [bohr, Finset.mem_filter] at hd
  have hdr := hd.2 r hr
  have hmReal : (0 : Real) < m := by exact_mod_cast hm
  have hbase : 0 ≤ zeta / (m : Real) * N := by positivity
  have hcollapse :
      (m : Real) * (zeta / (m : Real) * N) = zeta * N := by
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
        exact cor1014_centeredAbs_nsmul_le n (r * d)
      calc
        (centeredAbs (r * ((n : ZMod N) * d)) : Real) ≤
            n * centeredAbs (r * d) := by exact_mod_cast hcenter
        _ ≤ n * (zeta / (m : Real) * N) := by gcongr
        _ ≤ m * (zeta / (m : Real) * N) := by gcongr
        _ = zeta * N := hcollapse
  | negSucc n =>
      have hn : n + 1 ≤ m := by
        have := hjBounds.1
        omega
      have hcast : ((Int.negSucc n : Int) : ZMod N) * d =
          -(((n + 1 : Nat) : ZMod N) * d) := by
        push_cast
        ring
      rw [hcast, mul_neg, cor1014_centeredAbs_neg]
      have hcenter : centeredAbs (r * (((n + 1 : Nat) : ZMod N) * d)) ≤
          (n + 1) * centeredAbs (r * d) := by
        have hmul : r * (((n + 1 : Nat) : ZMod N) * d) =
            (n + 1) • (r * d) := by
          simp [nsmul_eq_mul]
          ring
        rw [hmul]
        exact cor1014_centeredAbs_nsmul_le (n + 1) (r * d)
      calc
        (centeredAbs (r * (((n + 1 : Nat) : ZMod N) * d)) : Real) ≤
            (n + 1) * centeredAbs (r * d) := by exact_mod_cast hcenter
        _ ≤ (n + 1) * (zeta / (m : Real) * N) := by gcongr
        _ ≤ m * (zeta / (m : Real) * N) := by
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hn) hbase
        _ = zeta * N := hcollapse

private lemma cor1014_zero_mem_symmetric {N : Nat} (d : ZMod N) (m : Nat) :
    (0 : ZMod N) ∈ section10SymmetricMultiples d m := by
  rw [section10SymmetricMultiples, Finset.mem_image]
  refine ⟨0, Finset.mem_Icc.mpr ?_, by simp⟩
  constructor <;> omega

/- **Gowers, Corollary 10.14.** -/
theorem corollary_10_14_holds : corollary_10_14 := by
  classical
  intro N _ X _ _ D phi K zeta Y psi1 hprime hmodel m hm d hd
  obtain ⟨hpsi, hagree⟩ := hmodel
  by_cases hY : Y.Nonempty
  · have hshort : section10SymmetricMultiples d m ⊆ bohr K zeta := by
      by_cases hK : K.Nonempty
      · exact cor1014_symmetric_multiples_subset K zeta
          (cor1014_small_bohr_nonnegative K zeta m hm d hd hK) m hm d hd
      · have hKempty : K = ∅ := Finset.not_nonempty_iff_eq_empty.mp hK
        intro z hz
        simp [bohr, hKempty]
    obtain ⟨a, ha⟩ := hY
    have hpsiZero : psi1 0 = 0 := by
      have hag := hagree a ha a ha
        (hshort (by simpa using cor1014_zero_mem_symmetric d m))
      simpa using hag.symm
    letI : Fact N.Prime := ⟨hprime⟩
    by_cases hd0 : d = 0
    · refine ⟨0, ?_⟩
      intro x hx y hy hxy
      have hdiff : D.index x - D.index y = 0 := by
        rw [section10SymmetricMultiples, Finset.mem_image] at hxy
        obtain ⟨j, _, hj⟩ := hxy
        simpa [hd0] using hj.symm
      simpa [hdiff, hpsiZero] using hagree x hx y hy (hshort hxy)
    · refine ⟨psi1 d / d, ?_⟩
      intro x hx y hy hxy
      have hag := hagree x hx y hy (hshort hxy)
      rw [section10SymmetricMultiples, Finset.mem_image] at hxy
      obtain ⟨j, hj, hjxy⟩ := hxy
      have hsame : symmetricMultiples d m = section10SymmetricMultiples d m := rfl
      have hdomain : symmetricMultiples d m ⊆ bohr K zeta := by
        simpa only [hsame] using hshort
      have hlin := freiman_map_int_multiple_of_zero (bohr K zeta) psi1 hpsi
        hpsiZero d m hm hdomain j hj
      rw [← hjxy, hlin] at hag
      rw [← hjxy]
      calc
        phi x - phi y = (j : ZMod N) * psi1 d := hag
        _ = (psi1 d / d) * ((j : ZMod N) * d) := by field_simp
  · refine ⟨0, ?_⟩
    intro x hx
    exact (hY ⟨x, hx⟩).elim

end LeanProofs.GowersSzemeredi
