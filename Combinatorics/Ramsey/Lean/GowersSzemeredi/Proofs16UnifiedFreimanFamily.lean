import GowersSzemeredi.Proofs16SingleRowSelection

/-! Enumerate the selected row frequencies as one bounded family of
Freiman maps on the common progression. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem exists_unified_freiman_family {N m K : Nat} [NeZero N]
    (P : Finset (ZMod N)) (J : Fin 4 → Finset (Fin m))
    (psi : Fin 4 → Fin m → ZMod N → ZMod N) (hJ : ∀ j, (J j).card ≤ K)
    (hpsi : ∀ j, ∀ i ∈ J j, FreimanHom 2 P (psi j i) ∧ psi j i 0 = 0) :
    ∃ (ell : Nat) (theta : Fin ell → ZMod N → ZMod N), ell ≤ 4*K ∧
      (∀ i, FreimanHom 2 P (theta i) ∧ theta i 0 = 0) ∧
      ∀ x, Finset.univ.image (fun i => theta i x) = unifiedRowFrequencies J psi x := by
  let I := (j : Fin 4) × {i // i ∈ J j}
  let e := Fintype.equivFin I
  let theta := fun i : Fin (Fintype.card I) => psi (e.symm i).1 (e.symm i).2.val
  refine ⟨Fintype.card I,theta,?_,?_,?_⟩
  · change Fintype.card ((j : Fin 4) × {i // i ∈ J j}) ≤ _
    rw [Fintype.card_sigma]
    simp only [Fintype.card_coe]
    calc ∑ j : Fin 4, (J j).card ≤ ∑ _j : Fin 4, K := Finset.sum_le_sum fun j _ => hJ j
      _ = _ := by simp
  · intro i
    exact hpsi (e.symm i).1 (e.symm i).2.val (e.symm i).2.property
  · intro x
    rw [unifiedRowFrequencies_eq_image]
    ext v
    simp only [Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨i,hi⟩
      exact ⟨e.symm i,hi⟩
    · rintro ⟨i,hi⟩
      refine ⟨e i,?_⟩
      change (fun z : I => psi z.1 z.2.val x) (e.symm (e i)) = v
      rw [e.symm_apply_apply]
      exact hi

def coherentProgressionDensity (delta kappa : Real) (d : Nat) (r : Real) : Real :=
  rowProgressionQuadrupleDensity delta (uniformAnchorIndexDensity delta kappa d r) d r

def singleProgressionDensity (delta kappa : Real) (d : Nat) (r : Real) : Real :=
  coherentProgressionDensity delta kappa d r/512

def singleProgressionModulusBound (delta kappa : Real) (d : Nat) (r : Real) : Nat :=
  ⌈8/coherentProgressionDensity delta kappa d r⌉₊

theorem coherentProgressionDensity_pos {delta kappa : Real} (hd : 0 < delta) (hk : 0 < kappa)
    (d : Nat) (r : Real) : 0 < coherentProgressionDensity delta kappa d r :=
  rowProgressionQuadrupleDensity_pos (uniformAnchorIndexDensity_pos hd hk d r)

theorem singleProgressionDensity_pos {delta kappa : Real} (hd : 0 < delta) (hk : 0 < kappa)
    (d : Nat) (r : Real) : 0 < singleProgressionDensity delta kappa d r :=
  div_pos (coherentProgressionDensity_pos hd hk d r) (by norm_num)

theorem singleProgressionModulusBound_mass {N d : Nat} {delta kappa r : Real}
    (hd : 0 < delta) (hk : 0 < kappa) (hN : singleProgressionModulusBound delta kappa d r ≤ N) :
    8 ≤ coherentProgressionDensity delta kappa d r*(N : Real) := by
  have hp := coherentProgressionDensity_pos hd hk d r
  have hc : 8/coherentProgressionDensity delta kappa d r ≤ (N : Real) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hN)
  simpa only [mul_comm] using (div_le_iff₀ hp).mp hc

end LeanProofs.GowersSzemeredi
