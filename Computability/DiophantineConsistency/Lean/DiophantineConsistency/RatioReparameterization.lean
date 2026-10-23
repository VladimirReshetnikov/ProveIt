import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic
import Diophantine.Paper1982.NineRatio

/-! # Exact quotient elimination in package 52's ratio registers -/

namespace DiophantineConsistency.RatioReparameterization

def oldH (B C : ℤ) (j : ℕ) : ℤ := B + j * C

def newH (B C F : ℤ) (j : ℕ) : ℤ := C + F * (B + j * C)

/-- Executable forward index: both divisions are exact under the theorem below. -/
def newIndex (B C F H : ℤ) : ℕ := (((H - C) / F - B) / C).toNat

/-- Executable reverse index. -/
def oldIndex (B C F : ℤ) (j : ℕ) : ℕ :=
  (1 + ((F - 1) / C) * B + F * j).toNat

theorem isCoprime_of_congruence {J F : ℤ} (hJF : J ∣ F - 1) : IsCoprime F J := by
  simpa using IsCoprime.add_one_left_of_dvd hJF

/-- The old combined divisibility separates exactly into the two conditions. -/
theorem combined_dvd_iff {J F Q H C : ℤ} (hJF : J ∣ F - 1) :
    J * F ∣ Q * F + J * (H - C) ↔ J ∣ Q ∧ F ∣ H - C := by
  have hcop := isCoprime_of_congruence hJF
  constructor
  · intro h
    have hJ : J ∣ Q * F + J * (H - C) :=
      dvd_trans (show J ∣ J * F from ⟨F, rfl⟩) h
    have hF : F ∣ Q * F + J * (H - C) :=
      dvd_trans (show F ∣ J * F from ⟨J, by ring⟩) h
    have hQF : J ∣ Q * F := by
      simpa using dvd_sub hJ (show J ∣ J * (H - C) from ⟨H - C, rfl⟩)
    have hJHC : F ∣ J * (H - C) := by
      simpa using dvd_sub hF (show F ∣ Q * F from ⟨Q, by ring⟩)
    exact ⟨hcop.symm.dvd_of_dvd_mul_right hQF, hcop.dvd_of_dvd_mul_left hJHC⟩
  · rintro ⟨⟨q, hq⟩, ⟨z, hz⟩⟩
    refine ⟨q + z, ?_⟩
    rw [hq, hz]
    ring

/-- The forward formula preserves the exact old H and extracts J divisibility. -/
theorem newIndex_correct {B C F J Q H : ℤ} {j : ℕ}
    (hB : 0 < B) (hBC : B < C) (hF : 0 < F)
    (hJF : J ∣ F - 1) (hCF : C ∣ F - 1)
    (hj : 1 ≤ j) (hH : H = oldH B C j)
    (hdiv : J * F ∣ Q * F + J * (H - C)) :
    J ∣ Q ∧ H = newH B C F (newIndex B C F H) := by
  have hC : 0 < C := by omega
  obtain ⟨hJQ, hFH⟩ := combined_dvd_iff hJF |>.mp hdiv
  have hjZ : 1 ≤ (j : ℤ) := by exact_mod_cast hj
  have hHC : 0 < H - C := by
    have hprod := mul_nonneg (show 0 ≤ (j : ℤ) - 1 by omega) (le_of_lt hC)
    dsimp [oldH] at hH
    nlinarith only [hH, hB, hprod]
  let z := (H - C) / F
  have hz : 0 < z := Int.ediv_pos_of_pos_of_dvd hHC (le_of_lt hF) hFH
  have hFz : F * z = H - C := by
    have h := Int.ediv_mul_cancel hFH
    dsimp [z]
    nlinarith only [h]
  obtain ⟨t, ht⟩ := hCF
  have hCz : C ∣ z - B := by
    refine ⟨(j : ℤ) - 1 - t * z, ?_⟩
    dsimp [oldH] at hH
    linear_combination hH + hFz - z * ht
  let q := (z - B) / C
  have hCq : C * q = z - B := by
    have h := Int.ediv_mul_cancel hCz
    dsimp [q]
    nlinarith only [h]
  have hq : 0 ≤ q := by
    by_contra h
    have hq' : q ≤ -1 := by omega
    have hmul := mul_le_mul_of_nonneg_left hq' (le_of_lt hC)
    nlinarith only [hCq, hz, hBC, hmul]
  have hcast : (newIndex B C F H : ℤ) = q := by
    exact Int.toNat_of_nonneg hq
  have hznew : z = B + (newIndex B C F H : ℤ) * C := by
    rw [hcast]
    nlinarith only [hCq]
  refine ⟨hJQ, ?_⟩
  dsimp [newH]
  rw [← hznew]
  nlinarith only [hFz]

/-- The reverse index is positive and gives exactly the same H. -/
theorem oldIndex_correct {B C F : ℤ} (hB : 0 < B) (hC : 0 < C)
    (hF : 0 < F) (hCF : C ∣ F - 1) (j : ℕ) :
    1 ≤ oldIndex B C F j ∧ newH B C F j = oldH B C (oldIndex B C F j) := by
  have hquot : 0 ≤ (F - 1) / C :=
    Int.ediv_nonneg (by omega) (le_of_lt hC)
  have hindex : 1 ≤ 1 + ((F - 1) / C) * B + F * j := by
    have hp : 0 ≤ ((F - 1) / C) * B := by positivity
    have hp' : 0 ≤ F * j := by positivity
    omega
  have hcast : (oldIndex B C F j : ℤ) = 1 + ((F - 1) / C) * B + F * j :=
    Int.toNat_of_nonneg (by omega)
  have hpos : 1 ≤ (oldIndex B C F j : ℤ) := by rw [hcast]; exact hindex
  refine ⟨by exact_mod_cast hpos, ?_⟩
  dsimp [oldH, newH]
  rw [hcast]
  have h := Int.ediv_mul_cancel hCF
  linear_combination -B * h

theorem newH_combined_dvd {B C F J Q : ℤ} (hJF : J ∣ F - 1)
    (hJQ : J ∣ Q) (j : ℕ) :
    J * F ∣ Q * F + J * (newH B C F j - C) := by
  apply (combined_dvd_iff hJF).mpr
  refine ⟨hJQ, B + (j : ℤ) * C, ?_⟩
  dsimp [newH]
  ring

/-- Pointwise equivalence at any old positive index. -/
theorem old_div_iff_new_form {B C F J Q H : ℤ} {j : ℕ}
    (hB : 0 < B) (hBC : B < C) (hF : 0 < F)
    (hJF : J ∣ F - 1) (hCF : C ∣ F - 1)
    (hj : 1 ≤ j) (hH : H = oldH B C j) :
    (J * F ∣ Q * F + J * (H - C)) ↔
      J ∣ Q ∧ ∃ t : ℕ, H = newH B C F t := by
  constructor
  · intro hd
    obtain ⟨hJQ, heq⟩ := newIndex_correct hB hBC hF hJF hCF hj hH hd
    exact ⟨hJQ, newIndex B C F H, heq⟩
  · rintro ⟨hJQ, t, rfl⟩
    exact newH_combined_dvd hJF hJQ t

/-- Any further conditions on H are transported without a cofinality premise. -/
theorem exists_old_iff_new {B C F J Q : ℤ} (P : ℤ → Prop)
    (hB : 0 < B) (hBC : B < C) (hF : 0 < F)
    (hJF : J ∣ F - 1) (hCF : C ∣ F - 1) :
    (∃ j : ℕ, 1 ≤ j ∧ P (oldH B C j) ∧
      J * F ∣ Q * F + J * (oldH B C j - C)) ↔
      J ∣ Q ∧ ∃ j : ℕ, P (newH B C F j) := by
  constructor
  · rintro ⟨j, hj, hp, hd⟩
    obtain ⟨hJQ, heq⟩ := newIndex_correct hB hBC hF hJF hCF hj rfl hd
    exact ⟨hJQ, newIndex B C F (oldH B C j), heq ▸ hp⟩
  · rintro ⟨hJQ, j, hp⟩
    obtain ⟨hj, heq⟩ := oldIndex_correct hB (by omega) hF hCF j
    refine ⟨oldIndex B C F j, hj, heq ▸ hp, ?_⟩
    rw [← heq]
    exact newH_combined_dvd hJF hJQ j

/-- The actual ratio F register, with its explicit polynomial coefficient recipe. -/
def F (A i J C D : ℤ) : ℤ := (A ^ 2 - 1) * (i * J * D * C ^ 2) ^ 2 + 1

def FQuotientJ (A i J C D : ℤ) : ℤ := (A ^ 2 - 1) * i ^ 2 * J * D ^ 2 * C ^ 4

def FQuotientC (A i J C D : ℤ) : ℤ := (A ^ 2 - 1) * i ^ 2 * J ^ 2 * D ^ 2 * C ^ 3

theorem F_sub_one_eq_J_mul (A i J C D : ℤ) :
    F A i J C D - 1 = J * FQuotientJ A i J C D := by
  dsimp [F, FQuotientJ]
  ring

theorem F_sub_one_eq_C_mul (A i J C D : ℤ) :
    F A i J C D - 1 = C * FQuotientC A i J C D := by
  dsimp [F, FQuotientC]
  ring

theorem F_congruences (A i J C D : ℤ) :
    J ∣ F A i J C D - 1 ∧ C ∣ F A i J C D - 1 :=
  ⟨⟨FQuotientJ A i J C D, F_sub_one_eq_J_mul A i J C D⟩,
    ⟨FQuotientC A i J C D, F_sub_one_eq_C_mul A i J C D⟩⟩

theorem F_congruences_of_register_identities {A i J C D E Fv : ℤ}
    (hE : E = i * J * D * C ^ 2) (hF : Fv = (A ^ 2 - 1) * E ^ 2 + 1) :
    J ∣ Fv - 1 ∧ C ∣ Fv - 1 := by
  rw [hF, hE]
  exact F_congruences A i J C D

/-- Both congruences hold for the actual registers of the existing numerical
ratio theorem, with no positivity or square hypothesis. -/
theorem vars_F_congruences (v : Jones1982.Nine.Vars) :
    v.J ∣ v.F - 1 ∧ v.C ∣ v.F - 1 :=
  F_congruences_of_register_identities rfl rfl

end DiophantineConsistency.RatioReparameterization
