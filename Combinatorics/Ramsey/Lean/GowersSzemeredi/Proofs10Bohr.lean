import GowersSzemeredi.Proofs05_10
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Bohr-neighborhood arguments from Section 10

This file proves the translation-overlap estimate and its Freiman-homomorphism
corollary.  The cardinal argument is valid for composite moduli as well: the
gcd of a frequency with the modulus simultaneously measures the spacing of
its image and the size of every fibre.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

private lemma centeredAbs_sub_le {N : Nat} [NeZero N] (x y : ZMod N) :
    centeredAbs (x - y) ≤ centeredAbs x + centeredAbs y := by
  unfold centeredAbs
  calc
    (x - y).valMinAbs.natAbs ≤
        (x.valMinAbs + (-y).valMinAbs).natAbs := by
      simpa only [sub_eq_add_neg] using ZMod.natAbs_valMinAbs_add_le x (-y)
    _ ≤ x.valMinAbs.natAbs + (-y).valMinAbs.natAbs := Int.natAbs_add_le _ _
    _ = x.valMinAbs.natAbs + y.valMinAbs.natAbs := by
      rw [ZMod.natAbs_valMinAbs_neg]

private lemma gcd_dvd_centeredAbs_mul {N : Nat} [NeZero N]
    (r x : ZMod N) : N.gcd r.val ∣ centeredAbs (r * x) := by
  unfold centeredAbs
  rw [ZMod.valMinAbs_natAbs_eq_min]
  have hval : N.gcd r.val ∣ (r * x).val := by
    rw [ZMod.val_mul]
    have hprod : N.gcd r.val ∣ r.val * x.val :=
      dvd_mul_of_dvd_left (Nat.gcd_dvd_right _ _) _
    have hmultiple : N.gcd r.val ∣ N * (r.val * x.val / N) :=
      dvd_mul_of_dvd_left (Nat.gcd_dvd_left _ _) _
    exact (Nat.dvd_add_iff_left hmultiple).mpr (by
      rw [Nat.mod_add_div]
      exact hprod)
  have hsub : N.gcd r.val ∣ N - (r * x).val :=
    Nat.dvd_sub (Nat.gcd_dvd_left _ _) hval
  rw [min_def]
  split <;> assumption

/-- At most `h / g` multiples of `g` lie in a real half-open interval of
length `h`, provided `g` divides `h`. -/
private lemma card_multiples_in_real_Ioc (g h : Nat) (hg : 0 < g) (hgh : g ∣ h)
    (A : Real) (S : Finset Nat)
    (hS : ∀ n, n ∈ S → g ∣ n ∧ A - h < n ∧ (n : Real) ≤ A) :
    S.card ≤ h / g := by
  have hgR : (0 : Real) < g := by exact_mod_cast hg
  -- `n ↦ n / g` maps `S` injectively into an integer interval of length `h / g`
  calc S.card ≤ (Finset.Ioc ⌊A / g - (h / g : Nat)⌋ ⌊A / g⌋).card := by
        refine Finset.card_le_card_of_injOn (fun n => ((n / g : Nat) : Int)) (fun n hn => ?_)
          fun n hn m hm hnm => (Nat.div_left_inj (hS n hn).1 (hS m hm).1).mp (Int.ofNat_inj.mp hnm)
        obtain ⟨hgn, hlo, hhi⟩ := hS n hn
        rw [Finset.coe_Ioc, Set.mem_Ioc, Int.floor_lt, Int.le_floor, Int.cast_natCast,
          Nat.cast_div hgn hgR.ne', Nat.cast_div hgh hgR.ne', ← sub_div]
        exact ⟨div_lt_div_of_pos_right hlo hgR, div_le_div_of_nonneg_right hhi hgR.le⟩
    _ = h / g := by rw [Int.card_Ioc, Int.floor_sub_natCast, sub_sub_cancel, Int.toNat_natCast]

private def frequencyBoundary {N : Nat} [NeZero N]
    (r d : ZMod N) (A : Real) : Finset (ZMod N) := by
  classical
  exact Finset.univ.filter fun x =>
    A - centeredAbs (r * d) < centeredAbs (r * x) ∧
      (centeredAbs (r * x) : Real) ≤ A

/-- The boundary crossed by translation by `d` in one Bohr coordinate has
at most twice the centered displacement in that coordinate. -/
private lemma frequencyBoundary_card_le {N : Nat} [NeZero N]
    (r d : ZMod N) (A : Real) :
    (frequencyBoundary r d A).card ≤ 2 * centeredAbs (r * d) := by
  -- `x ↦ r x` has fibres of size `g = gcd(N, r)`, at most two points share a norm, and the norms
  -- of the image are multiples of `g` in an interval of length `|r d|`
  let g : Nat := N.gcd r.val
  let f : ZMod N →+ ZMod N := nsmulAddMonoidHom r.val
  let F : Finset (ZMod N) := frequencyBoundary r d A
  let Y : Finset (ZMod N) := F.image f
  let V : Finset Nat := Y.image centeredAbs
  have hf (x : ZMod N) : f x = r * x := by
    simp only [f, nsmulAddMonoidHom_apply, nsmul_eq_mul, ZMod.natCast_zmod_val]
  have hgh : g ∣ centeredAbs (r * d) := gcd_dvd_centeredAbs_mul r d
  have hkernel : Nat.card f.ker = g := by
    dsimp only [f, g]
    simpa only [ZMod.card, Nat.card_eq_fintype_card] using
      IsAddCyclic.card_nsmulAddMonoidHom_ker (ZMod N) r.val
  have hFY : F.card ≤ g * Y.card := Finset.card_le_mul_card_image_of_maps_to
    (fun x hx => Finset.mem_image.mpr ⟨x, hx, rfl⟩) g fun y hy => by
      obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hy
      calc (F.filter fun z => f z = f x).card ≤ (Finset.univ.filter fun z => f z = f x).card :=
            Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ F))
        _ = (Finset.univ.filter fun z => f z = 0).card :=
            AddMonoidHom.card_fiber_eq_of_mem_range f ⟨x, rfl⟩ ⟨0, map_zero f⟩
        _ = g := by
            rw [← hkernel, Nat.card_eq_fintype_card, ← Fintype.card_subtype (fun z => f z = 0)]
            exact Fintype.card_congr
              (Equiv.subtypeEquiv (Equiv.refl _) fun z => AddMonoidHom.mem_ker)
  have hYV : Y.card ≤ 2 * V.card := Finset.card_le_mul_card_image_of_maps_to
    (fun y hy => Finset.mem_image.mpr ⟨y, hy, rfl⟩) 2 fun n _ => by
      obtain hne | ⟨a, ha⟩ := (Y.filter fun y => centeredAbs y = n).eq_empty_or_nonempty
      · simp [hne]
      · refine (Finset.card_le_card (t := {a, -a}) fun y hy => ?_).trans Finset.card_le_two
        simpa using ZMod.natAbs_valMinAbs_eq_natAbs_valMinAbs.mp
          ((Finset.mem_filter.mp hy).2.trans (Finset.mem_filter.mp ha).2.symm)
  have hV : V.card ≤ centeredAbs (r * d) / g := by
    refine card_multiples_in_real_Ioc g _ (Nat.gcd_pos_of_pos_left _ (NeZero.pos N)) hgh A V
      fun n hn => ?_
    obtain ⟨y, hyY, rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨x, hxF, rfl⟩ := Finset.mem_image.mp hyY
    simp only [F, frequencyBoundary, Finset.mem_filter, Finset.mem_univ, true_and] at hxF
    rw [hf]
    exact ⟨gcd_dvd_centeredAbs_mul r x, hxF⟩
  calc F.card ≤ g * (2 * (centeredAbs (r * d) / g)) :=
        hFY.trans (Nat.mul_le_mul_left g (hYV.trans (Nat.mul_le_mul_left 2 hV)))
    _ = 2 * centeredAbs (r * d) := by rw [mul_left_comm, Nat.mul_div_cancel' hgh]

@[simp] private lemma mem_section10Translate_iff {N : Nat}
    (A : Finset (ZMod N)) (d x : ZMod N) :
    x ∈ section10Translate A d ↔ x - d ∈ A := by
  simp only [section10Translate, Finset.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa
  · intro hx
    exact ⟨x - d, hx, by abel⟩

private lemma bohr_sdiff_translate_card_le {N : Nat} [NeZero N]
    (K : Finset (ZMod N)) (delta zeta : Real) (d : ZMod N)
    (hd : d ∈ bohr K zeta) :
    ((bohr K delta \ section10Translate (bohr K delta) d).card : Real) ≤
      2 * K.card * zeta * N := by
  -- a point leaving `bohr K delta` crosses the boundary of one coordinate `r ∈ K`
  have hsub : bohr K delta \ section10Translate (bohr K delta) d ⊆
      K.biUnion fun r => frequencyBoundary r d (delta * N) := by
    intro x hx
    simp only [bohr, frequencyBoundary, Finset.mem_sdiff, mem_section10Translate_iff,
      Finset.mem_filter, Finset.mem_univ, true_and, not_forall, not_le,
      Finset.mem_biUnion] at hx ⊢
    obtain ⟨hxB, r, hrK, hr⟩ := hx
    have h := centeredAbs_sub_le (r * x) (r * d)
    rw [← mul_sub] at h
    have h' : (centeredAbs (r * (x - d)) : Real) ≤ centeredAbs (r * x) + centeredAbs (r * d) := by
      exact_mod_cast h
    exact ⟨r, hrK, by linarith, hxB r hrK⟩
  simp only [bohr, Finset.mem_filter, Finset.mem_univ, true_and] at hd
  calc _ ≤ ((K.biUnion fun r => frequencyBoundary r d (delta * N)).card : Real) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ ∑ r ∈ K, ((frequencyBoundary r d (delta * N)).card : Real) := by
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _r ∈ K, 2 * (zeta * N) := Finset.sum_le_sum fun r hr => by
        have := (Nat.cast_le (α := Real)).mpr (frequencyBoundary_card_le r d (delta * N))
        push_cast at this
        linarith [hd r hr]
    _ = 2 * K.card * zeta * N := by simp; ring

theorem lemma_10_10_holds : lemma_10_10 := by
  intro N k _ K delta zeta hk hdelta hdeltaOne hzeta _
  dsimp only
  intro d hd
  subst k
  have hBLower : (delta / 2) ^ K.card * (N : Real) ≤ (bohr K delta).card := by
    rcases (show N = 1 ∨ 2 ≤ N by have := NeZero.pos N; omega) with rfl | hN
    · refine le_trans ?_ (Nat.one_le_cast.mpr (Finset.card_pos.mpr ⟨0, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, fun r _ => by simp [centeredAbs]; positivity⟩⟩))
      simpa using pow_le_one₀ (n := K.card) (by positivity) (by linarith : delta / 2 ≤ 1)
    · exact (lemma_7_7_holds N K delta hN hdelta hdeltaOne).1
  have hidentity : (2 : Real) ^ (K.card + 1) * delta ^ (-(K.card : Real)) * K.card * zeta *
      ((delta / 2) ^ K.card * N) = 2 * K.card * zeta * N := by
    rw [Real.rpow_neg hdelta.le, Real.rpow_natCast, div_pow]
    field_simp
    ring
  have hpart : ((bohr K delta \ section10Translate (bohr K delta) d).card : Real) +
      (bohr K delta ∩ section10Translate (bohr K delta) d).card = (bohr K delta).card := by
    exact_mod_cast Finset.card_sdiff_add_card_inter _ _
  linarith [bohr_sdiff_translate_card_le K delta zeta d hd, mul_le_mul_of_nonneg_left hBLower
    (by positivity : (0 : Real) ≤ 2 ^ (K.card + 1) * delta ^ (-(K.card : Real)) * K.card * zeta)]

lemma section10Translate_card {N : Nat}
    (A : Finset (ZMod N)) (d : ZMod N) :
    (section10Translate A d).card = A.card := by
  unfold section10Translate
  exact Finset.card_image_of_injective A (add_left_injective d)

lemma section10Translate_mono {N : Nat}
    {A A' : Finset (ZMod N)} (hAA' : A ⊆ A') (d : ZMod N) :
    section10Translate A d ⊆ section10Translate A' d := by
  intro x hx
  rw [mem_section10Translate_iff] at hx ⊢
  exact hAA' hx

/-- Inclusion-exclusion inside a common finite ambient set. -/
lemma inter_card_lower_of_subsets {X : Type*} [DecidableEq X]
    (S T U : Finset X) (hSU : S ⊆ U) (hTU : T ⊆ U) :
    (S.card : Real) + T.card - U.card ≤ (S ∩ T).card := by
  have hunion : S ∪ T ⊆ U := Finset.union_subset hSU hTU
  have hcardUnion : (S ∪ T).card ≤ U.card := Finset.card_le_card hunion
  have hcardIdentity := Finset.card_union_add_card_inter S T
  have hcardUnionReal : ((S ∪ T).card : Real) ≤ U.card := by exact_mod_cast hcardUnion
  have hcardIdentityReal :
      ((S ∪ T).card : Real) + (S ∩ T).card = S.card + T.card := by
    exact_mod_cast hcardIdentity
  linarith

lemma bohr_zero_mem {N : Nat} [NeZero N]
    (K : Finset (ZMod N)) (delta : Real) (hdelta : 0 ≤ delta) :
    (0 : ZMod N) ∈ bohr K delta := by
  unfold bohr
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, mul_zero,
    centeredAbs, ZMod.valMinAbs_zero, Int.natAbs_zero, Nat.cast_zero]
  intro r _
  positivity

/-- The four-translate intersection used in Corollary 10.11. -/
private lemma exists_dense_bohr_chain {N : Nat}
    (B B' C : Finset (ZMod N)) (hBne : B.Nonempty) (hB'sub : B' ⊆ B)
    (hB'dense : (7 / 8 : Real) * B.card ≤ B'.card)
    (hoverlap : ∀ d, d ∈ C →
      (7 / 8 : Real) * B.card ≤ (B ∩ section10Translate B d).card)
    (d₁ d₂ d₃ : ZMod N)
    (hd₁ : d₁ ∈ C) (hd₂ : d₂ ∈ C) (hd₃ : d₃ ∈ C) :
    ∃ x ∈ B', x - d₁ ∈ B' ∧ x - d₁ - d₂ ∈ B' ∧ x - d₃ ∈ B' := by
  -- otherwise `B` is covered by seven sets of at most `|B| / 8` points each
  let E := B \ B'
  let F (d : ZMod N) := B \ section10Translate B d
  have hE : (E.card : Real) ≤ B.card / 8 := by
    have : (E.card : Real) + B'.card = B.card := by
      exact_mod_cast Finset.card_sdiff_add_card_eq_card hB'sub
    linarith
  have hF (d : ZMod N) (hd : d ∈ C) : ((F d).card : Real) ≤ B.card / 8 := by
    have : ((F d).card : Real) + (B ∩ section10Translate B d).card = B.card := by
      exact_mod_cast Finset.card_sdiff_add_card_inter _ _
    linarith [hoverlap d hd]
  by_contra! hno
  have hsub : B ⊆ E ∪ section10Translate E d₁ ∪ section10Translate E (d₁ + d₂) ∪
      section10Translate E d₃ ∪ F d₁ ∪ section10Translate (F d₂) d₁ ∪ F d₃ := by
    intro x hx
    have := hno x
    simp only [E, F, Finset.mem_union, Finset.mem_sdiff, mem_section10Translate_iff,
      sub_sub] at this ⊢
    tauto
  have hU := (Nat.cast_le (α := Real)).mpr <| (Finset.card_le_card hsub).trans <|
    (card_union_le _ _).trans <| Nat.add_le_add_right ((card_union_le _ _).trans <|
      Nat.add_le_add_right ((card_union_le _ _).trans <| Nat.add_le_add_right
        ((card_union_le _ _).trans <| Nat.add_le_add_right ((card_union_le _ _).trans <|
          Nat.add_le_add_right (card_union_le _ _) _) _) _) _) _
  push_cast [section10Translate_card] at hU
  linarith [hF d₁ hd₁, hF d₂ hd₂, hF d₃ hd₃, (Nat.cast_pos (α := Real)).mpr hBne.card_pos]

lemma corollary_10_11_overlap {N : Nat} [NeZero N]
    (K : Finset (ZMod N)) (delta : Real) (hK : K.Nonempty)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1) :
    let k := K.card
    let B := bohr K delta
    let zeta := (2 : Real) ^ (-((k : Real) + 4)) * delta ^ k / k
    let C := bohr K zeta
    ∀ d, d ∈ C →
      (7 / 8 : Real) * B.card ≤ (B ∩ section10Translate B d).card := by
  dsimp only
  intro d hd
  have hk : 0 < K.card := Finset.card_pos.mpr hK
  have hkR : (1 : Real) ≤ K.card := by exact_mod_cast hk
  -- the loss coefficient of Lemma 10.10 at this radius is exactly `1 / 8`
  have hcoeff : (2 : Real) ^ (K.card + 1) * delta ^ (-(K.card : Real)) * K.card *
      ((2 : Real) ^ (-((K.card : Real) + 4)) * delta ^ K.card / K.card) = 1 / 8 := by
    rw [Real.rpow_neg hdelta.le, Real.rpow_natCast, Real.rpow_neg (by norm_num : (0 : Real) ≤ 2),
      show (K.card : Real) + 4 = ((K.card + 4 : Nat) : Real) by push_cast; ring,
      Real.rpow_natCast]
    field_simp
    ring
  have h := lemma_10_10_holds N K.card K delta _ rfl hdelta hdeltaOne (by positivity)
    ((div_le_self (by positivity) hkR).trans ((mul_le_of_le_one_left (by positivity)
      (Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith))).trans
        (pow_le_of_le_one hdelta.le hdeltaOne hk.ne'))) d hd
  rw [hcoeff] at h
  linarith

theorem corollary_10_11_holds : corollary_10_11 := by
  intro N _ K delta hK hdelta hdeltaOne k B zeta C B' psi hB'sub hB'dense hpsi
  have hCzero : (0 : ZMod N) ∈ C := bohr_zero_mem K zeta (by positivity)
  have hchain := exists_dense_bohr_chain B B' C ⟨0, bohr_zero_mem K delta hdelta.le⟩ hB'sub
    hB'dense (corollary_10_11_overlap K delta hK hdelta hdeltaOne)
  -- each `c ∈ C` is the difference `r c - (r c - c)` of two points of `B'`
  have hpt (c : ZMod N) (hc : c ∈ C) : ∃ x ∈ B', x - c ∈ B' := by
    obtain ⟨x, hx, hxc, -⟩ := hchain c 0 c hc hCzero hc
    exact ⟨x, hx, hxc⟩
  choose! r hr hrc using hpt
  let psi1 : ZMod N → ZMod N := fun c => psi (r c) - psi (r c - c)
  have hinduced : InducesDifferenceMap B' C psi psi1 := fun c hc x hx y hy hxy =>
    sub_eq_sub_iff_add_eq_add.mpr ((hpsi : IsAddFreimanHom 2 (B' : Set (ZMod N)) Set.univ
      psi).add_eq_add hx (hrc c hc) (hr c hc) hy (by linear_combination hxy))
  refine ⟨fun c hc => Finset.mem_sub.mpr ⟨r c, hr c hc, r c - c, hrc c hc, sub_sub_cancel _ _⟩,
    psi1, isAddFreimanHom_two.mpr ⟨Set.mapsTo_univ _ _,
      fun d₁ hd₁ d₂ hd₂ d₃ hd₃ d₄ hd₄ hadd => ?_⟩, hinduced⟩
  obtain ⟨x, hx, hx₁, hx₁₂, hx₃⟩ := hchain d₁ d₂ d₃ hd₁ hd₂ hd₃
  have h₃₄ : x - d₃ - d₄ = x - d₁ - d₂ := by rw [sub_sub, sub_sub, hadd]
  rw [← hinduced d₁ hd₁ x hx _ hx₁ (sub_sub_cancel _ _),
    ← hinduced d₂ hd₂ _ hx₁ _ hx₁₂ (sub_sub_cancel _ _),
    ← hinduced d₃ hd₃ x hx _ hx₃ (sub_sub_cancel _ _),
    ← hinduced d₄ hd₄ _ hx₃ (x - d₃ - d₄) (h₃₄ ▸ hx₁₂) (sub_sub_cancel _ _), h₃₄]
  abel

end LeanProofs.GowersSzemeredi
