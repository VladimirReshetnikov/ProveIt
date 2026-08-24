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
  classical
  let T : Finset Int := Finset.Ioc ⌊A / g - (h / g : Nat)⌋ ⌊A / g⌋
  have hmaps : Set.MapsTo (fun n : Nat => ((n / g : Nat) : Int))
      (S : Set Nat) (T : Set Int) := by
    intro n hn
    have hnprops := hS n hn
    have hnEq : n / g * g = n := Nat.div_mul_cancel hnprops.1
    have hhEq : h / g * g = h := Nat.div_mul_cancel hgh
    have hgReal : (0 : Real) < g := by exact_mod_cast hg
    have hnEqReal : ((n / g : Nat) : Real) * g = n := by exact_mod_cast hnEq
    have hhEqReal : ((h / g : Nat) : Real) * g = h := by exact_mod_cast hhEq
    have hnQuot : ((n / g : Nat) : Real) = (n : Real) / g := by
      apply (eq_div_iff hgReal.ne').2
      exact hnEqReal
    have hhQuot : ((h / g : Nat) : Real) = (h : Real) / g := by
      apply (eq_div_iff hgReal.ne').2
      exact hhEqReal
    have hnLower : A / g - (h / g : Nat) < (n / g : Nat) := by
      rw [hnQuot, hhQuot]
      calc
        A / g - h / g = (A - h) / g := by ring
        _ < n / g := (div_lt_div_iff_of_pos_right hgReal).2 hnprops.2.1
    have hnUpper : ((n / g : Nat) : Real) ≤ A / g := by
      rw [hnQuot]
      exact (div_le_div_iff_of_pos_right hgReal).2 hnprops.2.2
    change ((n / g : Nat) : Int) ∈ T
    rw [Finset.mem_Ioc]
    exact ⟨(Int.floor_lt).2 (by exact_mod_cast hnLower),
      (Int.le_floor).2 (by exact_mod_cast hnUpper)⟩
  have hinj : Set.InjOn (fun n : Nat => ((n / g : Nat) : Int)) (S : Set Nat) := by
    intro n hn m hm hnm
    have hnDvd := (hS n hn).1
    have hmDvd := (hS m hm).1
    have hdiv : n / g = m / g := Int.ofNat_inj.mp hnm
    calc
      n = n / g * g := (Nat.div_mul_cancel hnDvd).symm
      _ = m / g * g := by rw [hdiv]
      _ = m := Nat.div_mul_cancel hmDvd
  have hcard := Finset.card_le_card_of_injOn
    (fun n : Nat => ((n / g : Nat) : Int)) hmaps hinj
  calc
    S.card ≤ T.card := hcard
    _ = h / g := by
      dsimp only [T]
      rw [Int.card_Ioc]
      have hfloor : ⌊A / g - (h / g : Nat)⌋ =
          ⌊A / g⌋ - ((h / g : Nat) : Int) := by
        simpa only [Int.cast_natCast] using
          (Int.floor_sub_intCast (A / g) ((h / g : Nat) : Int))
      rw [hfloor]
      simp only [sub_sub_cancel]
      exact Int.toNat_natCast _

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
  classical
  let g : Nat := N.gcd r.val
  let h : Nat := centeredAbs (r * d)
  let f : ZMod N →+ ZMod N := nsmulAddMonoidHom r.val
  let F : Finset (ZMod N) := frequencyBoundary r d A
  let Y : Finset (ZMod N) := F.image f
  let V : Finset Nat := Y.image centeredAbs
  have hf (x : ZMod N) : f x = r * x := by
    simp only [f, nsmulAddMonoidHom_apply, nsmul_eq_mul, ZMod.natCast_zmod_val]
  have hg : 0 < g := Nat.gcd_pos_of_pos_left _ (NeZero.pos N)
  have hgh : g ∣ h := by
    dsimp only [g, h]
    exact gcd_dvd_centeredAbs_mul r d
  have hkernel : Nat.card f.ker = g := by
    dsimp only [f, g]
    simpa only [ZMod.card, Nat.card_eq_fintype_card] using
      IsAddCyclic.card_nsmulAddMonoidHom_ker (ZMod N) r.val
  have hfiber (y : ZMod N) (hy : y ∈ Y) :
      (F.filter fun x => f x = y).card ≤ g := by
    have hyrange : y ∈ Set.range f := by
      obtain ⟨x, hxF, hxy⟩ := Finset.mem_image.mp hy
      exact ⟨x, hxy⟩
    have hzero : (0 : ZMod N) ∈ Set.range f := ⟨0, map_zero f⟩
    have hallEq : (Finset.univ.filter fun x => f x = y).card =
        (Finset.univ.filter fun x => f x = 0).card :=
      AddMonoidHom.card_fiber_eq_of_mem_range f hyrange hzero
    have hzeroCard : (Finset.univ.filter fun x => f x = 0).card = Nat.card f.ker := by
      rw [Nat.card_eq_fintype_card]
      rw [← Fintype.card_subtype (fun x => f x = 0)]
      exact Fintype.card_congr
        (Equiv.subtypeEquiv (Equiv.refl _) fun x => AddMonoidHom.mem_ker)
    calc
      (F.filter fun x => f x = y).card ≤
          (Finset.univ.filter fun x => f x = y).card :=
        Finset.card_le_card
          (Finset.filter_subset_filter _ (Finset.subset_univ F))
      _ = (Finset.univ.filter fun x => f x = 0).card := hallEq
      _ = Nat.card f.ker := hzeroCard
      _ = g := hkernel
  have hFY : F.card ≤ g * Y.card := by
    exact Finset.card_le_mul_card_image_of_maps_to
      (fun x hx => Finset.mem_image.mpr ⟨x, hx, rfl⟩) g hfiber
  have hnormFiber (n : Nat) (hn : n ∈ V) :
      (Y.filter fun y => centeredAbs y = n).card ≤ 2 := by
    by_cases hne : (Y.filter fun y => centeredAbs y = n).Nonempty
    · obtain ⟨a, ha⟩ := hne
      exact (Finset.card_le_card (t := {a, -a}) (by
        intro y hy
        have haya := (Finset.mem_filter.mp ha).2
        have hyny := (Finset.mem_filter.mp hy).2
        have heq : y.valMinAbs.natAbs = a.valMinAbs.natAbs := by
          unfold centeredAbs at hyny haya
          exact hyny.trans haya.symm
        simpa only [Finset.mem_insert, Finset.mem_singleton] using
          (ZMod.natAbs_valMinAbs_eq_natAbs_valMinAbs.mp heq))).trans
        Finset.card_le_two
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
      exact Nat.zero_le _
  have hYV : Y.card ≤ 2 * V.card := by
    exact Finset.card_le_mul_card_image_of_maps_to
      (fun y hy => Finset.mem_image.mpr ⟨y, hy, rfl⟩) 2 hnormFiber
  have hVprops : ∀ n, n ∈ V →
      g ∣ n ∧ A - h < n ∧ (n : Real) ≤ A := by
    intro n hn
    obtain ⟨y, hyY, hyn⟩ := Finset.mem_image.mp hn
    obtain ⟨x, hxF, hxy⟩ := Finset.mem_image.mp hyY
    have hxBoundary := Finset.mem_filter.mp hxF |>.2
    have hfx : f x = r * x := hf x
    subst y
    subst n
    refine ⟨?_, ?_, ?_⟩
    · simpa only [g, hfx] using gcd_dvd_centeredAbs_mul r x
    · simpa only [F, frequencyBoundary, h, hfx] using hxBoundary.1
    · simpa only [F, frequencyBoundary, h, hfx] using hxBoundary.2
  have hV : V.card ≤ h / g :=
    card_multiples_in_real_Ioc g h hg hgh A V hVprops
  calc
    (frequencyBoundary r d A).card = F.card := rfl
    _ ≤ g * Y.card := hFY
    _ ≤ g * (2 * V.card) := Nat.mul_le_mul_left g hYV
    _ ≤ g * (2 * (h / g)) := Nat.mul_le_mul_left g (Nat.mul_le_mul_left 2 hV)
    _ = 2 * h := by
      calc
        g * (2 * (h / g)) = 2 * ((h / g) * g) := by ac_rfl
        _ = 2 * h := by rw [Nat.div_mul_cancel hgh]
    _ = 2 * centeredAbs (r * d) := rfl

@[simp] private lemma mem_section10Translate_iff {N : Nat}
    (A : Finset (ZMod N)) (d x : ZMod N) :
    x ∈ section10Translate A d ↔ x - d ∈ A := by
  classical
  simp only [section10Translate, Finset.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa
  · intro hx
    exact ⟨x - d, hx, by abel⟩

private lemma bohr_sdiff_translate_subset_boundaries {N : Nat} [NeZero N]
    (K : Finset (ZMod N)) (delta : Real) (d : ZMod N) :
    bohr K delta \ section10Translate (bohr K delta) d ⊆
      K.biUnion fun r => frequencyBoundary r d (delta * N) := by
  classical
  intro x hx
  have hxB := (Finset.mem_sdiff.mp hx).1
  have hxdNot : x - d ∉ bohr K delta := by
    simpa only [mem_section10Translate_iff] using (Finset.mem_sdiff.mp hx).2
  unfold bohr at hxB hxdNot
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hxB hxdNot
  push Not at hxdNot
  obtain ⟨r, hrK, hrxd⟩ := hxdNot
  rw [Finset.mem_biUnion]
  refine ⟨r, hrK, ?_⟩
  unfold frequencyBoundary
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have htriangleNat := centeredAbs_sub_le (r * x) (r * d)
  have htriangle : (centeredAbs (r * (x - d)) : Real) ≤
      centeredAbs (r * x) + centeredAbs (r * d) := by
    rw [mul_sub]
    exact_mod_cast htriangleNat
  exact ⟨by nlinarith, hxB r hrK⟩

private lemma bohr_sdiff_translate_card_le {N : Nat} [NeZero N]
    (K : Finset (ZMod N)) (delta zeta : Real) (d : ZMod N)
    (hd : d ∈ bohr K zeta) :
    ((bohr K delta \ section10Translate (bohr K delta) d).card : Real) ≤
      2 * K.card * zeta * N := by
  classical
  have hsubset := bohr_sdiff_translate_subset_boundaries K delta d
  have hcardNat :
      (bohr K delta \ section10Translate (bohr K delta) d).card ≤
        ∑ r ∈ K, 2 * centeredAbs (r * d) := by
    calc
      (bohr K delta \ section10Translate (bohr K delta) d).card ≤
          (K.biUnion fun r => frequencyBoundary r d (delta * N)).card :=
        Finset.card_le_card hsubset
      _ ≤ ∑ r ∈ K, (frequencyBoundary r d (delta * N)).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ r ∈ K, 2 * centeredAbs (r * d) :=
        Finset.sum_le_sum fun r _ => frequencyBoundary_card_le r d (delta * N)
  have hcardReal :
      ((bohr K delta \ section10Translate (bohr K delta) d).card : Real) ≤
        ∑ r ∈ K, (2 * centeredAbs (r * d) : Nat) := by
    exact_mod_cast hcardNat
  have hd' := hd
  unfold bohr at hd'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd'
  calc
    ((bohr K delta \ section10Translate (bohr K delta) d).card : Real) ≤
        ∑ r ∈ K, (2 * centeredAbs (r * d) : Nat) := hcardReal
    _ = ∑ r ∈ K, (2 * centeredAbs (r * d) : Real) := by norm_cast
    _ ≤ ∑ r ∈ K, 2 * (zeta * N) := by
      exact Finset.sum_le_sum fun r hr => mul_le_mul_of_nonneg_left (hd' r hr) (by positivity)
    _ = 2 * K.card * zeta * N := by simp; ring

theorem lemma_10_10_holds : lemma_10_10 := by
  classical
  intro N k _ K delta zeta hk hdelta hdeltaOne hzeta hzetaDelta
  dsimp only
  intro d hd
  subst k
  let B : Finset (ZMod N) := bohr K delta
  let c : Real :=
    (2 : Real) ^ (K.card + 1) * delta ^ (-(K.card : Real)) * K.card * zeta
  have hNpos : 0 < N := NeZero.pos N
  have hBLower : (delta / 2) ^ K.card * (N : Real) ≤ B.card := by
    by_cases hNone : N = 1
    · subst N
      have hB : B = Finset.univ := by
        ext x
        simp only [B, bohr, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
        intro r hr
        have hrx : r * x = 0 := Subsingleton.elim _ _
        rw [hrx]
        simp only [centeredAbs, ZMod.valMinAbs_zero, Int.natAbs_zero, Nat.cast_zero]
        positivity
      rw [hB]
      simp only [Nat.cast_one]
      have hbase : 0 ≤ delta / 2 := by positivity
      have hbaseOne : delta / 2 ≤ 1 := by linarith
      simpa using (pow_le_one₀ (n := K.card) hbase hbaseOne)
    · have hNtwo : 2 ≤ N := by omega
      exact (lemma_7_7_holds N K delta hNtwo hdelta hdeltaOne).1
  have hcNonneg : 0 ≤ c := by
    dsimp only [c]
    positivity
  have hcancel :
      delta ^ (-(K.card : Real)) * delta ^ (K.card : Nat) = 1 := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_add hdelta]
    norm_num
  have hidentity : c * ((delta / 2) ^ K.card * (N : Real)) =
      2 * K.card * zeta * N := by
    dsimp only [c]
    rw [div_pow, pow_succ]
    have hpowTwo : (0 : Real) < 2 ^ K.card := by positivity
    calc
      (2 : Real) ^ K.card * 2 * delta ^ (-(K.card : Real)) * K.card * zeta *
          (delta ^ K.card / 2 ^ K.card * N) =
          2 * (delta ^ (-(K.card : Real)) * delta ^ K.card) * K.card * zeta * N := by
        field_simp [hpowTwo.ne']
      _ = 2 * K.card * zeta * N := by rw [hcancel]; ring
  have hscaled := mul_le_mul_of_nonneg_left hBLower hcNonneg
  have hlossScale : 2 * K.card * zeta * N ≤ c * B.card := by
    rw [← hidentity]
    exact hscaled
  have hlost := bohr_sdiff_translate_card_le K delta zeta d hd
  have hlost' :
      ((B \ section10Translate B d).card : Real) ≤ c * B.card := by
    have hlostB :
        ((B \ section10Translate B d).card : Real) ≤
          2 * K.card * zeta * N := by
      simpa only [B] using hlost
    exact hlostB.trans hlossScale
  have hpartitionNat := Finset.card_sdiff_add_card_inter B (section10Translate B d)
  have hpartition :
      ((B \ section10Translate B d).card : Real) +
        ((B ∩ section10Translate B d).card : Real) = B.card := by
    exact_mod_cast hpartitionNat
  change (1 - c) * B.card ≤ (B ∩ section10Translate B d).card
  nlinarith

private lemma section10Translate_card {N : Nat}
    (A : Finset (ZMod N)) (d : ZMod N) :
    (section10Translate A d).card = A.card := by
  classical
  unfold section10Translate
  exact Finset.card_image_of_injective A (add_left_injective d)

private lemma section10Translate_mono {N : Nat}
    {A A' : Finset (ZMod N)} (hAA' : A ⊆ A') (d : ZMod N) :
    section10Translate A d ⊆ section10Translate A' d := by
  classical
  intro x hx
  rw [mem_section10Translate_iff] at hx ⊢
  exact hAA' hx

private lemma section10Translate_inter {N : Nat}
    (A A' : Finset (ZMod N)) (d : ZMod N) :
    section10Translate (A ∩ A') d =
      section10Translate A d ∩ section10Translate A' d := by
  classical
  ext x
  simp only [Finset.mem_inter, mem_section10Translate_iff]

private lemma section10Translate_add {N : Nat}
    (A : Finset (ZMod N)) (d e : ZMod N) :
    section10Translate (section10Translate A d) e = section10Translate A (d + e) := by
  classical
  ext x
  simp only [mem_section10Translate_iff]
  constructor <;> intro hx
  · convert hx using 1
    abel
  · convert hx using 1
    abel

/-- Inclusion-exclusion inside a common finite ambient set. -/
private lemma inter_card_lower_of_subsets {X : Type*} [DecidableEq X]
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

private lemma bohr_zero_mem {N : Nat} [NeZero N]
    (K : Finset (ZMod N)) (delta : Real) (hdelta : 0 ≤ delta) :
    (0 : ZMod N) ∈ bohr K delta := by
  classical
  unfold bohr
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, mul_zero,
    centeredAbs, ZMod.valMinAbs_zero, Int.natAbs_zero, Nat.cast_zero]
  intro r hr
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
  classical
  let T₁ := section10Translate B d₁
  let T₁₂ := section10Translate B (d₁ + d₂)
  let T₃ := section10Translate B d₃
  let S₀₁ := B ∩ T₁
  let S₁₂ := T₁ ∩ T₁₂
  let S₀₃ := B ∩ T₃
  let S₀₁₂ := S₀₁ ∩ S₁₂
  let U := S₀₁₂ ∩ S₀₃
  have hS₀₁ : (7 / 8 : Real) * B.card ≤ S₀₁.card := by
    exact hoverlap d₁ hd₁
  have hS₁₂eq : S₁₂ = section10Translate (B ∩ section10Translate B d₂) d₁ := by
    dsimp only [S₁₂, T₁, T₁₂]
    rw [section10Translate_inter, section10Translate_add]
    congr 2
    abel
  have hS₁₂ : (7 / 8 : Real) * B.card ≤ S₁₂.card := by
    rw [hS₁₂eq, section10Translate_card]
    exact hoverlap d₂ hd₂
  have hS₀₃ : (7 / 8 : Real) * B.card ≤ S₀₃.card := by
    exact hoverlap d₃ hd₃
  have hS₀₁sub : S₀₁ ⊆ T₁ := Finset.inter_subset_right
  have hS₁₂sub : S₁₂ ⊆ T₁ := Finset.inter_subset_left
  have hT₁card : T₁.card = B.card := section10Translate_card B d₁
  have hS₀₁₂ : (3 / 4 : Real) * B.card ≤ S₀₁₂.card := by
    have hinter := inter_card_lower_of_subsets S₀₁ S₁₂ T₁
      hS₀₁sub hS₁₂sub
    dsimp only [S₀₁₂]
    rw [hT₁card] at hinter
    nlinarith
  have hS₀₁₂sub : S₀₁₂ ⊆ B := by
    intro x hx
    exact (Finset.mem_inter.mp (Finset.mem_inter.mp hx).1).1
  have hS₀₃sub : S₀₃ ⊆ B := Finset.inter_subset_left
  have hU : (5 / 8 : Real) * B.card ≤ U.card := by
    have hinter := inter_card_lower_of_subsets S₀₁₂ S₀₃ B
      hS₀₁₂sub hS₀₃sub
    dsimp only [U]
    nlinarith
  let T₁' := section10Translate B' d₁
  let T₁₂' := section10Translate B' (d₁ + d₂)
  let T₃' := section10Translate B' d₃
  let U' := ((B' ∩ T₁') ∩ T₁₂') ∩ T₃'
  have hT₁sub : T₁' ⊆ T₁ := section10Translate_mono hB'sub d₁
  have hT₁₂sub : T₁₂' ⊆ T₁₂ :=
    section10Translate_mono hB'sub (d₁ + d₂)
  have hT₃sub : T₃' ⊆ T₃ := section10Translate_mono hB'sub d₃
  have hU'sub : U' ⊆ U := by
    intro x hx
    simp only [U', U, S₀₁₂, S₀₁, S₁₂, S₀₃,
      Finset.mem_inter] at hx ⊢
    exact ⟨⟨⟨hB'sub hx.1.1.1, hT₁sub hx.1.1.2⟩,
      ⟨hT₁sub hx.1.1.2, hT₁₂sub hx.1.2⟩⟩,
      ⟨hB'sub hx.1.1.1, hT₃sub hx.2⟩⟩
  have hdeficit (e : ZMod N) :
      ((section10Translate B e \ section10Translate B' e).card : Real) ≤
        (1 / 8 : Real) * B.card := by
    have hpartNat := Finset.card_sdiff_add_card_eq_card
      (section10Translate_mono hB'sub e)
    have hpartReal :
        ((section10Translate B e \ section10Translate B' e).card : Real) +
          (section10Translate B' e).card = (section10Translate B e).card := by
      exact_mod_cast hpartNat
    rw [section10Translate_card, section10Translate_card] at hpartReal
    nlinarith
  let E₀ := B \ B'
  let E₁ := T₁ \ T₁'
  let E₁₂ := T₁₂ \ T₁₂'
  let E₃ := T₃ \ T₃'
  have hE₀ : (E₀.card : Real) ≤ (1 / 8 : Real) * B.card := by
    dsimp only [E₀]
    have hpartNat := Finset.card_sdiff_add_card_eq_card hB'sub
    have hpartReal : ((B \ B').card : Real) + B'.card = B.card := by
      exact_mod_cast hpartNat
    nlinarith
  have hE₁ : (E₁.card : Real) ≤ (1 / 8 : Real) * B.card := hdeficit d₁
  have hE₁₂ : (E₁₂.card : Real) ≤ (1 / 8 : Real) * B.card :=
    hdeficit (d₁ + d₂)
  have hE₃ : (E₃.card : Real) ≤ (1 / 8 : Real) * B.card := hdeficit d₃
  have hdiffSub : U \ U' ⊆ ((E₀ ∪ E₁) ∪ E₁₂) ∪ E₃ := by
    intro x hx
    have hxU := (Finset.mem_sdiff.mp hx).1
    have hxNot := (Finset.mem_sdiff.mp hx).2
    simp only [U, S₀₁₂, S₀₁, S₁₂, S₀₃,
      Finset.mem_inter] at hxU
    simp only [Finset.mem_union, E₀, E₁, E₁₂, E₃, Finset.mem_sdiff]
    by_cases hx₀ : x ∈ B'
    · by_cases hx₁ : x ∈ T₁'
      · by_cases hx₁₂ : x ∈ T₁₂'
        · by_cases hx₃ : x ∈ T₃'
          · exact False.elim (hxNot (by
              simp only [U', Finset.mem_inter]
              exact ⟨⟨⟨hx₀, hx₁⟩, hx₁₂⟩, hx₃⟩))
          · exact Or.inr ⟨hxU.2.2, hx₃⟩
        · exact Or.inl (Or.inr ⟨hxU.1.2.2, hx₁₂⟩)
      · exact Or.inl (Or.inl (Or.inr ⟨hxU.1.1.2, hx₁⟩))
    · exact Or.inl (Or.inl (Or.inl ⟨hxU.1.1.1, hx₀⟩))
  have hdiffNat : (U \ U').card ≤ E₀.card + E₁.card + E₁₂.card + E₃.card := by
    calc
      (U \ U').card ≤ (((E₀ ∪ E₁) ∪ E₁₂) ∪ E₃).card :=
        Finset.card_le_card hdiffSub
      _ ≤ ((E₀ ∪ E₁) ∪ E₁₂).card + E₃.card :=
        Finset.card_union_le _ _
      _ ≤ ((E₀ ∪ E₁).card + E₁₂.card) + E₃.card := by
        exact Nat.add_le_add_right (Finset.card_union_le _ _) _
      _ ≤ (E₀.card + E₁.card + E₁₂.card) + E₃.card := by
        exact Nat.add_le_add_right
          (Nat.add_le_add_right (Finset.card_union_le _ _) _) _
  have hdiff : ((U \ U').card : Real) ≤ (1 / 2 : Real) * B.card := by
    have hdiffReal : ((U \ U').card : Real) ≤
        E₀.card + E₁.card + E₁₂.card + E₃.card := by
      exact_mod_cast hdiffNat
    nlinarith
  have hpartition : ((U \ U').card : Real) + U'.card = U.card := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hU'sub
  have hU'lower : (1 / 8 : Real) * B.card ≤ U'.card := by nlinarith
  have hBcardPos : (0 : Real) < B.card := by
    exact_mod_cast Finset.card_pos.mpr hBne
  have hU'pos : (0 : Real) < U'.card := by nlinarith
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (by exact_mod_cast hU'pos)
  have hx' := hx
  simp only [U', Finset.mem_inter, T₁', T₁₂', T₃',
    mem_section10Translate_iff] at hx'
  refine ⟨x, hx'.1.1.1, hx'.1.1.2, ?_, hx'.2⟩
  convert hx'.1.2 using 1
  abel

private lemma corollary_10_11_overlap {N : Nat} [NeZero N]
    (K : Finset (ZMod N)) (delta : Real) (hK : K.Nonempty)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1) :
    let k := K.card
    let B := bohr K delta
    let zeta := (2 : Real) ^ (-((k : Real) + 4)) * delta ^ k / k
    let C := bohr K zeta
    ∀ d, d ∈ C →
      (7 / 8 : Real) * B.card ≤ (B ∩ section10Translate B d).card := by
  classical
  dsimp only
  intro d hd
  let k : Nat := K.card
  let zeta : Real := (2 : Real) ^ (-((k : Real) + 4)) * delta ^ k / k
  have hk : 0 < k := Finset.card_pos.mpr hK
  have hkReal : (0 : Real) < k := by exact_mod_cast hk
  have hfactorNonneg : 0 ≤ (2 : Real) ^ (-((k : Real) + 4)) :=
    Real.rpow_nonneg (by norm_num) _
  have hfactorLeOne : (2 : Real) ^ (-((k : Real) + 4)) ≤ 1 := by
    exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by
      have : (0 : Real) ≤ k + 4 := by positivity
      linarith)
  have hdeltaPowNonneg : 0 ≤ delta ^ k := pow_nonneg hdelta.le _
  have hdeltaPowLe : delta ^ k ≤ delta := by
    simpa only [pow_one] using
      pow_le_pow_of_le_one hdelta.le hdeltaOne (Nat.one_le_iff_ne_zero.mpr hk.ne')
  have hzetaPos : 0 < zeta := by
    dsimp only [zeta]
    positivity
  have hzetaLe : zeta ≤ delta := by
    calc
      zeta ≤ 1 * delta ^ k / k := by
        dsimp only [zeta]
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hfactorLeOne hdeltaPowNonneg) hkReal.le
      _ ≤ delta ^ k := by
        simpa only [one_mul] using div_le_self hdeltaPowNonneg (by exact_mod_cast hk)
      _ ≤ delta := hdeltaPowLe
  have htwoCancel :
      (2 : Real) ^ (k + 1) * (2 : Real) ^ (-((k : Real) + 4)) = 1 / 8 := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_add (by norm_num : (0 : Real) < 2)]
    rw [show ((k + 1 : Nat) : Real) + (-((k : Real) + 4)) = -3 by
      norm_num
      ring]
    norm_num [Real.rpow_neg (by norm_num : (0 : Real) ≤ 2)]
  have hdeltaCancel : delta ^ (-(k : Real)) * delta ^ k = 1 := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_add hdelta]
    norm_num
  have hcoeff :
      (2 : Real) ^ (k + 1) * delta ^ (-(k : Real)) * k * zeta = 1 / 8 := by
    dsimp only [zeta]
    calc
      (2 : Real) ^ (k + 1) * delta ^ (-(k : Real)) * k *
          ((2 : Real) ^ (-((k : Real) + 4)) * delta ^ k / k) =
          ((2 : Real) ^ (k + 1) * (2 : Real) ^ (-((k : Real) + 4))) *
            (delta ^ (-(k : Real)) * delta ^ k) := by
        field_simp [hkReal.ne']
      _ = 1 / 8 := by rw [htwoCancel, hdeltaCancel]; norm_num
  have hraw := lemma_10_10_holds N k K delta zeta rfl hdelta hdeltaOne
    hzetaPos.le hzetaLe d hd
  change (1 - (2 : Real) ^ (k + 1) * delta ^ (-(k : Real)) * k * zeta) *
      (bohr K delta).card ≤
        (bohr K delta ∩ section10Translate (bohr K delta) d).card at hraw
  rw [hcoeff] at hraw
  norm_num at hraw ⊢
  exact hraw

theorem corollary_10_11_holds : corollary_10_11 := by
  classical
  intro N _ K delta hK hdelta hdeltaOne
  dsimp only
  intro B' psi hB'sub hB'dense hpsi
  let k : Nat := K.card
  let B : Finset (ZMod N) := bohr K delta
  let zeta : Real := (2 : Real) ^ (-((k : Real) + 4)) * delta ^ k / k
  let C : Finset (ZMod N) := bohr K zeta
  change C ⊆ B' - B' ∧ ∃ psi1 : ZMod N → ZMod N,
    FreimanHom 2 C psi1 ∧ InducesDifferenceMap B' C psi psi1
  have hk : 0 < k := Finset.card_pos.mpr hK
  have hkReal : (0 : Real) < k := by exact_mod_cast hk
  have hzetaPos : 0 < zeta := by
    dsimp only [zeta]
    positivity
  have hBne : B.Nonempty := ⟨0, bohr_zero_mem K delta hdelta.le⟩
  have hCzero : (0 : ZMod N) ∈ C := bohr_zero_mem K zeta hzetaPos.le
  have hoverlap : ∀ d, d ∈ C →
      (7 / 8 : Real) * B.card ≤ (B ∩ section10Translate B d).card := by
    simpa only [k, B, zeta, C] using
      corollary_10_11_overlap K delta hK hdelta hdeltaOne
  have hchain (d₁ d₂ d₃ : ZMod N)
      (hd₁ : d₁ ∈ C) (hd₂ : d₂ ∈ C) (hd₃ : d₃ ∈ C) :
      ∃ x ∈ B', x - d₁ ∈ B' ∧ x - d₁ - d₂ ∈ B' ∧ x - d₃ ∈ B' :=
    exists_dense_bohr_chain B B' C hBne hB'sub hB'dense hoverlap
      d₁ d₂ d₃ hd₁ hd₂ hd₃
  have hCsub : C ⊆ B' - B' := by
    intro c hc
    obtain ⟨x, hxB', hxcB', hxccB', hxagain⟩ := hchain c 0 c hc hCzero hc
    rw [Finset.mem_sub]
    exact ⟨x, hxB', x - c, hxcB', by abel⟩
  refine ⟨hCsub, ?_⟩
  have hpair (c : ZMod N) (hc : c ∈ C) :
      ∃ p : ZMod N × ZMod N, p.1 ∈ B' ∧ p.2 ∈ B' ∧ p.1 - p.2 = c := by
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.mem_sub.mp (hCsub hc)
    exact ⟨(x, y), hx, hy, hxy⟩
  let rep : ZMod N → ZMod N × ZMod N := fun c =>
    if hc : c ∈ C then Classical.choose (hpair c hc) else (0, 0)
  have hrep (c : ZMod N) (hc : c ∈ C) :
      (rep c).1 ∈ B' ∧ (rep c).2 ∈ B' ∧ (rep c).1 - (rep c).2 = c := by
    dsimp only [rep]
    rw [dif_pos hc]
    exact Classical.choose_spec (hpair c hc)
  let psi1 : ZMod N → ZMod N := fun c => psi (rep c).1 - psi (rep c).2
  have hpsi' : IsAddFreimanHom 2 (B' : Set (ZMod N)) Set.univ psi := hpsi
  have hinduced : InducesDifferenceMap B' C psi psi1 := by
    intro c hc x hx y hy hxy
    have hr := hrep c hc
    have hsum : x + (rep c).2 = (rep c).1 + y := by
      apply sub_eq_sub_iff_add_eq_add.mp
      exact hxy.trans hr.2.2.symm
    have hmap := hpsi'.add_eq_add hx hr.2.1 hr.1 hy hsum
    dsimp only [psi1]
    exact sub_eq_sub_iff_add_eq_add.mpr hmap
  refine ⟨psi1, ?_, hinduced⟩
  unfold FreimanHom
  rw [isAddFreimanHom_two]
  refine ⟨Set.mapsTo_univ _ _, ?_⟩
  intro d₁ hd₁ d₂ hd₂ d₃ hd₃ d₄ hd₄ hadd
  change d₁ ∈ C at hd₁
  change d₂ ∈ C at hd₂
  change d₃ ∈ C at hd₃
  change d₄ ∈ C at hd₄
  obtain ⟨x, hx, hx₁, hx₁₂, hx₃⟩ := hchain d₁ d₂ d₃ hd₁ hd₂ hd₃
  have hendpoint : x - d₁ - d₂ = x - d₃ - d₄ := by
    rw [sub_sub, sub_sub, hadd]
  have h₁ : psi x - psi (x - d₁) = psi1 d₁ :=
    hinduced d₁ hd₁ x hx (x - d₁) hx₁ (by abel)
  have h₂ : psi (x - d₁) - psi (x - d₁ - d₂) = psi1 d₂ :=
    hinduced d₂ hd₂ (x - d₁) hx₁ (x - d₁ - d₂) hx₁₂ (by abel)
  have h₃ : psi x - psi (x - d₃) = psi1 d₃ :=
    hinduced d₃ hd₃ x hx (x - d₃) hx₃ (by abel)
  have hx₃₄ : x - d₃ - d₄ ∈ B' := by rw [← hendpoint]; exact hx₁₂
  have h₄ : psi (x - d₃) - psi (x - d₃ - d₄) = psi1 d₄ :=
    hinduced d₄ hd₄ (x - d₃) hx₃ (x - d₃ - d₄) hx₃₄ (by abel)
  rw [← h₁, ← h₂, ← h₃, ← h₄, ← hendpoint]
  abel

end LeanProofs.GowersSzemeredi
