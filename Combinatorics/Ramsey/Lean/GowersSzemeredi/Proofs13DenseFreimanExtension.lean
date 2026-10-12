import GowersSzemeredi.Definitions

/-! Dense partial Freiman maps extend to affine maps. These finite-group
results supply the large-density branch of the printed Section 13 extraction.
No primality hypothesis is needed for the cyclic affine extension. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

theorem finite_common_point_of_small_complements {X : Type*}
    [Fintype X] [DecidableEq X] {r : Nat} (A : Fin r → Finset X)
    (hcard : (∑ i, (Fintype.card X - (A i).card)) < Fintype.card X) :
    ∃ x : X, ∀ i, x ∈ A i := by
  classical
  by_contra hnone
  let B := Finset.univ.biUnion (fun i : Fin r ↦ Finset.univ \ A i)
  have hcover : (Finset.univ : Finset X) ⊆ B := by
    intro x _
    have hnot : ¬ ∀ i, x ∈ A i := fun hx ↦ hnone ⟨x, hx⟩
    obtain ⟨i, hi⟩ := not_forall.mp hnot
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _,
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hi⟩⟩
  have hbc : Fintype.card X ≤ B.card := by
    simpa only [Finset.card_univ] using Finset.card_le_card hcover
  have hc : Fintype.card X ≤ ∑ i : Fin r, (Finset.univ \ A i).card :=
    hbc.trans Finset.card_biUnion_le
  have hs : (∑ i : Fin r, (Finset.univ \ A i).card) =
      ∑ i, (Fintype.card X - (A i).card) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ]
  rw [hs] at hc
  exact Nat.not_lt_of_ge hc hcard

/-- Removing the first common point from one set finds a second point
whenever the sum of complement sizes leaves at least two possible points. -/
theorem finite_two_common_points_of_small_complements {X : Type*}
    [Fintype X] [DecidableEq X] {r : Nat} (A : Fin r → Finset X)
    (hr : 0 < r)
    (hcard : (∑ i, (Fintype.card X - (A i).card)) + 1 < Fintype.card X) :
    ∃ x y : X, x ≠ y ∧ (∀ i, x ∈ A i) ∧ (∀ i, y ∈ A i) := by
  classical
  obtain ⟨x, hx⟩ := finite_common_point_of_small_complements A (by omega)
  let i0 : Fin r := ⟨0, hr⟩
  let T : Fin r → Finset X := fun i ↦ if i = i0 then (A i).erase x else A i
  have hT (i : Fin r) : Fintype.card X - (T i).card =
      (Fintype.card X - (A i).card) + (if i = i0 then 1 else 0) := by
    by_cases hi : i = i0
    · simp only [T, if_pos hi, Finset.card_erase_of_mem (hx i)]
      have hle := Finset.card_le_univ (A i)
      have hpos := Finset.card_pos.mpr ⟨x, hx i⟩
      omega
    · simp only [T, if_neg hi, add_zero]
  obtain ⟨y, hy⟩ := finite_common_point_of_small_complements T (by
    simp only [hT, Finset.sum_add_distrib]
    simpa using hcard)
  have hne : y ≠ x := by
    have hmem : y ∈ (A i0).erase x := by simpa only [T, if_pos rfl] using hy i0
    exact (Finset.mem_erase.mp hmem).1
  refine ⟨x, y, hne.symm, hx, fun i ↦ ?_⟩
  by_cases hi : i = i0
  · have hmem : y ∈ (A i).erase x := by simpa only [T, if_pos hi] using hy i
    exact (Finset.mem_erase.mp hmem).2
  · simpa only [T, if_neg hi] using hy i

theorem finite_common_shift_of_small_complement {G : Type*}
    [AddCommGroup G] [Fintype G] [DecidableEq G] {r : Nat}
    (A : Finset G) (d : Fin r → G)
    (hcard : r * (Fintype.card G - A.card) < Fintype.card G) :
    ∃ x : G, ∀ i, x + d i ∈ A := by
  classical
  let T : Fin r → Finset G := fun i ↦ A.image (fun y ↦ y - d i)
  have hT (i : Fin r) : (T i).card = A.card := by
    apply Finset.card_image_of_injective
    intro x y hxy
    simpa using congrArg (fun z ↦ z + d i) hxy
  obtain ⟨x, hx⟩ := finite_common_point_of_small_complements T (by
    simp only [hT, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact hcard)
  refine ⟨x, fun i ↦ ?_⟩
  obtain ⟨y, hy, heq⟩ := Finset.mem_image.mp (hx i)
  rw [← heq]
  simpa using hy

/-- An order-two partial Freiman map on more than two thirds of a finite
abelian group is the restriction of one affine additive map. -/
theorem dense_freiman_two_affine_extension {G H : Type*}
    [AddCommGroup G] [Fintype G] [DecidableEq G] [AddCommGroup H]
    (A : Finset G) (f : G → H) (hf : FreimanHom 2 A f)
    (hDense : 2 * Fintype.card G < 3 * A.card) :
    ∃ g : G →+ H, ∃ b : H, ∀ x ∈ A, f x = g x + b := by
  classical
  have hAcard : A.card ≤ Fintype.card G := Finset.card_le_univ A
  have hthree : 3 * (Fintype.card G - A.card) < Fintype.card G := by omega
  have htwo : 2 * (Fintype.card G - A.card) < Fintype.card G := by omega
  have hp (d : G) : ∃ x, x ∈ A ∧ x + d ∈ A := by
    obtain ⟨x, hx⟩ := finite_common_shift_of_small_complement A ![0, d] htwo
    exact ⟨x, by simpa using hx 0, by simpa using hx 1⟩
  choose anchor ha had using hp
  let g : G → H := fun d ↦ f (anchor d + d) - f (anchor d)
  have hdiff (d x : G) (hx : x ∈ A) (hxd : x + d ∈ A) :
      g d = f (x + d) - f x := by
    have heq := hf.add_eq_add (had d) hx (ha d) hxd
      (by abel : anchor d + d + x = anchor d + (x + d))
    dsimp only [g]
    exact sub_eq_sub_iff_add_eq_add.mpr (by simpa only [add_comm] using heq)
  have hadd (d e : G) : g (d + e) = g d + g e := by
    obtain ⟨x, hx⟩ := finite_common_shift_of_small_complement A ![0, d, d + e] hthree
    have hx0 : x ∈ A := by simpa using hx 0
    have hxd : x + d ∈ A := by simpa using hx 1
    have hxde : x + (d + e) ∈ A := by simpa using hx 2
    have he : x + d + e ∈ A := by simpa only [add_assoc] using hxde
    rw [hdiff (d + e) x hx0 hxde, hdiff d x hx0 hxd, hdiff e (x + d) hxd he]
    simp only [add_assoc]
    abel
  let gh : G →+ H :=
    { toFun := g
      map_zero' := by
        apply add_left_cancel (a := g 0)
        simpa only [add_zero] using (hadd 0 0).symm
      map_add' := hadd }
  obtain ⟨x0, hx0⟩ := Finset.card_pos.mp (show 0 < A.card by omega)
  refine ⟨gh, f x0 - gh x0, fun x hx ↦ ?_⟩
  have hsum : x0 + (x - x0) = x := by abel
  have hxd : x0 + (x - x0) ∈ A := by rw [hsum]; exact hx
  have hd := hdiff (x - x0) x0 hx0 hxd
  change gh (x - x0) = f (x0 + (x - x0)) - f x0 at hd
  rw [gh.map_sub, hsum] at hd
  calc
    f x = (f x - f x0) + f x0 := by abel
    _ = (gh x - gh x0) + f x0 := by rw [← hd]
    _ = gh x + (f x0 - gh x0) := by abel

/-- Cyclic additive maps are scalar multiplication, so the affine extension
is an ordinary affine formula on every nonzero modulus. -/
theorem dense_freiman_two_linear {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) (f : ZMod N → ZMod N) (hf : FreimanHom 2 A f)
    (hDense : 2 * N < 3 * A.card) : LinearOn A f := by
  obtain ⟨g, b, hformula⟩ := dense_freiman_two_affine_extension A f hf
    (by simpa only [ZMod.card] using hDense)
  have hlin (x : ZMod N) : g x = g 1 * x := by
    have h := g.map_nsmul x.val (1 : ZMod N)
    simpa only [nsmul_eq_mul, Nat.cast_one, mul_one,
      ZMod.natCast_zmod_val, mul_comm] using h
  exact ⟨g 1, b, fun x hx ↦ by rw [hformula x hx, hlin x]⟩

theorem dense_freiman_eight_linear {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) (f : ZMod N → ZMod N) (hf : FreimanHom 8 A f)
    (hDense : 2 * N < 3 * A.card) : LinearOn A f :=
  dense_freiman_two_linear A f (IsAddFreimanHom.mono (by norm_num) hf) hDense

end LeanProofs.GowersSzemeredi
