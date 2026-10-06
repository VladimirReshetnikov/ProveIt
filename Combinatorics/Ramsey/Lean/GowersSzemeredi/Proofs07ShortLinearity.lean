import GowersSzemeredi.Proofs07ModularPartition

/-!
# Affine linearity on short progressions

Over a prime field any map on at most two points extends affinely. On a
three-point arithmetic progression, the remaining affine relation is exactly
a Freiman relation of order two. Thus an order-eight Freiman map restricted
to any progression of length at most three is affine on its domain.
-/

set_option autoImplicit false

noncomputable section

open Finset

namespace LeanProofs.GowersSzemeredi

/-- Any map on at most two points of a prime field agrees with an affine map. -/
theorem linearOn_of_card_le_two {N : Nat} [Fact N.Prime]
    (A : Finset (ZMod N)) (phi : ZMod N → ZMod N) (hA : A.card ≤ 2) :
    LinearOn A phi := by
  classical
  by_cases htwo : A.card = 2
  · obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp htwo
    let a := (phi y - phi x) / (y - x)
    refine ⟨a, phi x - a * x, ?_⟩
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · ring
    · have hzy := Finset.mem_singleton.mp hz
      subst z
      dsimp [a]
      field_simp [sub_ne_zero.mpr hxy.symm]
      ring
  have hone : A.card ≤ 1 := by omega
  by_cases hne : A.Nonempty
  · obtain ⟨x, hx⟩ := hne
    refine ⟨0, phi x, ?_⟩
    intro y hy
    have hyx : y = x := Finset.card_le_one.mp hone y hy x hx
    simp [hyx]
  · have hzero : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    subst A
    exact ⟨0, 0, fun _ h ↦ (Finset.notMem_empty _ h).elim⟩

/-- A Freiman map on the part of a proper progression of length at most
three agrees with an affine map on that part. -/
theorem linearOn_short_progression {N : Nat} [Fact N.Prime]
    (P : ModAP N) (A : Finset (ZMod N)) (phi : ZMod N → ZMod N)
    (hP : P.IsProper) (hlen : P.length ≤ 3) (hA : A ⊆ P.carrier)
    (hphi : FreimanHom 8 A phi) : LinearOn A phi := by
  classical
  by_cases htwo : A.card ≤ 2
  · exact linearOn_of_card_le_two A phi htwo
  have hcard : P.carrier.card = P.length := hP
  have hle : A.card ≤ P.length := (Finset.card_le_card hA).trans_eq hcard
  have hlen3 : P.length = 3 := by omega
  have heq : A = P.carrier := Finset.eq_of_subset_of_card_le hA (by omega)
  subst A
  have hd : P.step ≠ 0 := BaseCase.proper_modAP_step_ne_zero_of_two_le P hP (by omega)
  have hmem (i : Fin 3) : P.start + (i : Nat) * P.step ∈ P.carrier := by
    apply Finset.mem_image.mpr
    exact ⟨⟨i, by omega⟩, Finset.mem_univ _, rfl⟩
  have h₀ := hmem (0 : Fin 3)
  have h₁ := hmem (1 : Fin 3)
  have h₂ := hmem (2 : Fin 3)
  norm_num only [Fin.val_zero, Fin.val_one, Nat.cast_zero, Nat.cast_one,
    zero_mul, one_mul, add_zero] at h₀ h₁
  have hrel : phi P.start + phi (P.start + 2 * P.step) =
      phi (P.start + P.step) + phi (P.start + P.step) := by
    exact (IsAddFreimanHom.mono (by decide : 2 ≤ 8) hphi).add_eq_add
      h₀ h₂ h₁ h₁ (by ring)
  let a := (phi (P.start + P.step) - phi P.start) / P.step
  let b := phi P.start - a * P.start
  have he₀ : phi P.start = a * P.start + b := by dsimp [b]; ring
  have he₁ : phi (P.start + P.step) = a * (P.start + P.step) + b := by
    dsimp [a, b]
    field_simp [hd]
    ring
  have he₂ : phi (P.start + 2 * P.step) = a * (P.start + 2 * P.step) + b := by
    linear_combination he₁ * 2 - he₀ + hrel
  refine ⟨a, b, ?_⟩
  intro x hx
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
  have hi : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by omega
  rcases hi with hi | hi | hi
  · simpa only [hi, Nat.cast_zero, zero_mul, add_zero] using he₀
  · simpa only [hi, Nat.cast_one, one_mul] using he₁
  · simpa only [hi, Nat.cast_ofNat] using he₂

/-- A proper modular progression can be partitioned into affine cells of
length at least any target at most two (and at most the ambient length).
No lower-scale hypothesis is required. -/
theorem short_modular_affine_partition {N : Nat} [Fact N.Prime]
    (R : ModAP N) (A : Finset (ZMod N)) (phi : ZMod N → ZMod N)
    (hR : R.IsProper) (hstep : R.step != 0)
    (hphi : FreimanHom 8 A phi) {t : Real} (ht : t ≤ 2)
    (htR : t ≤ R.length) :
    ∃ M : Nat, ∃ Q : Fin M → ModAP N,
      IsPartition (fun j ↦ (Q j).carrier) R.carrier ∧
      ∀ j, (Q j).step != 0 ∧ (Q j).IsProper ∧ t ≤ (Q j).length ∧
        LinearOn ((Q j).carrier.filter fun x ↦ x ∈ A) phi := by
  classical
  have hlinear (P : ModAP N) (hp : P.IsProper) (hlen : P.length ≤ 3) :
      LinearOn (P.carrier.filter fun x ↦ x ∈ A) phi := by
    apply linearOn_short_progression P _ phi hp hlen (Finset.filter_subset _ _)
    exact IsAddFreimanHom.subset
      (fun x hx ↦ (Finset.mem_filter.mp hx).2) hphi (Set.mapsTo_univ _ _)
  by_cases hshort : R.length ≤ 3
  · refine ⟨1, fun _ ↦ R, ?_, fun _ ↦ ⟨hstep, hR, htR, hlinear R hR hshort⟩⟩
    constructor
    · intro x
      exact ⟨fun hx ↦ ⟨0, hx⟩, fun ⟨_, hx⟩ ↦ hx⟩
    · intro i j hij
      exact (bne_iff_ne.mp hij (Subsingleton.elim i j)).elim
  let P := R.asBox
  have hP : P.IsProper := fun _ ↦ hR
  have hwidth : P.width = R.length := BaseCase.boxOne_width P
  have hLm : 2 * 2 ≤ P.width := by rw [hwidth]; omega
  let Q : Fin (P.width / 2) → ModAP N :=
    fun j ↦ (BaseCase.coarseChildBox P 2 j).axis 0
  have hproper (j : Fin (P.width / 2)) : (Q j).IsProper :=
    BaseCase.coarseChildBox_proper P hP 2 (by norm_num) hLm j 0
  have hlength (j : Fin (P.width / 2)) : 2 ≤ (Q j).length ∧ (Q j).length ≤ 3 := by
    dsimp only [Q, BaseCase.coarseChildBox, BaseCase.coarseChunkLength]
    split_ifs <;> omega
  refine ⟨P.width / 2, Q, ?_, ?_⟩
  · exact box_one_partition_axes P (fun j ↦ BaseCase.coarseChildBox P 2 j)
      (BaseCase.coarseChildBox_partition P hP 2 (by norm_num) hLm)
  · intro j
    refine ⟨hstep, hproper j, ?_, hlinear (Q j) (hproper j) (hlength j).2⟩
    exact ht.trans (by exact_mod_cast (hlength j).1)

end LeanProofs.GowersSzemeredi
