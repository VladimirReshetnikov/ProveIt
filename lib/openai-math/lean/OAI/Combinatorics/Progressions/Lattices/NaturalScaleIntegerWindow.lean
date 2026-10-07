/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import Mathlib

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {ι G : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup G]

noncomputable def centeredIntegerBox (R : ι → ℕ) : Finset (ι → ℤ) :=
  Fintype.piFinset (fun i => Finset.Icc (-(R i : ℤ)) (R i : ℤ))

@[simp] theorem mem_centeredIntegerBox (R : ι → ℕ) (x : ι → ℤ) :
    x ∈ centeredIntegerBox R ↔ ∀ i, |x i| ≤ (R i : ℤ) := by
  simp only [centeredIntegerBox, Fintype.mem_piFinset, Finset.mem_Icc, abs_le]

@[simp] theorem card_centeredIntegerBox (R : ι → ℕ) :
    (centeredIntegerBox R).card = ∏ i, (2 * R i + 1) := by
  rw [centeredIntegerBox, Fintype.card_piFinset]
  apply Finset.prod_congr rfl
  intro i _
  rw [Int.card_Icc]
  omega

theorem card_doubled_centeredIntegerBox_le (R : ι → ℕ) :
    (centeredIntegerBox (fun i => 2 * R i)).card ≤
      2 ^ Fintype.card ι * (centeredIntegerBox R).card := by
  rw [card_centeredIntegerBox, card_centeredIntegerBox]
  calc
    (∏ i, (2 * (2 * R i) + 1)) ≤ ∏ i, (2 * (2 * R i + 1)) := by
      gcongr with i
      omega
    _ = _ := by rw [Finset.prod_mul_distrib]; simp

omit [Fintype ι] [DecidableEq ι] in
theorem card_mul_le_of_kernel_translates (φ : (ι → ℤ) →+ G)
    (S X : Finset (ι → ℤ)) (k : ℕ) (v : ι → ℤ) (hv : v ≠ 0)
    (hker : φ v = 0) (hinj : Set.InjOn φ (S : Set _))
    (hsub : ∀ x ∈ S, ∀ j < k, x + j • v ∈ X) : S.card * k ≤ X.card := by
  classical
  rw [← Finset.card_range k, ← Finset.card_product]
  apply Finset.card_le_card_of_injOn (fun z : (ι → ℤ) × ℕ => z.1 + z.2 • v)
  · intro z hz
    exact hsub z.1 (Finset.mem_product.mp hz).1 z.2
      (Finset.mem_range.mp (Finset.mem_product.mp hz).2)
  · intro x hx y hy hxy
    change x.1 + x.2 • v = y.1 + y.2 • v at hxy
    have hφ : φ x.1 = φ y.1 := by
      have h := congrArg φ hxy
      simpa only [map_add, map_nsmul, hker, nsmul_zero, add_zero] using h
    have hbase : x.1 = y.1 := hinj (Finset.mem_product.mp hx).1
      (Finset.mem_product.mp hy).1 hφ
    apply Prod.ext hbase
    have hmul : x.2 • v = y.2 • v := by
      rw [hbase] at hxy
      exact add_left_cancel hxy
    have hnonzero : ¬ ∀ i, v i = 0 := fun h => hv (funext h)
    obtain ⟨i, hi⟩ := not_forall.mp hnonzero
    have hiEq := congrFun hmul i
    simp only [Pi.smul_apply, nsmul_eq_mul] at hiEq
    exact_mod_cast mul_right_cancel₀ hi hiEq

theorem kernel_eq_zero_of_dense_integer_box (φ : (ι → ℤ) →+ G)
    (S : Finset (ι → ℤ)) (R : ι → ℕ) (k : ℕ)
    (hS : S ⊆ centeredIntegerBox R) (hinj : Set.InjOn φ (S : Set _))
    (hlarge : (centeredIntegerBox (fun i => 2 * R i)).card < S.card * k)
    (v : ι → ℤ) (hker : φ v = 0) (hshort : ∀ i, (k : ℤ) * |v i| ≤ (R i : ℤ)) :
    v = 0 := by
  by_contra hv
  apply (not_le_of_gt hlarge)
  apply card_mul_le_of_kernel_translates φ S (centeredIntegerBox (fun i => 2 * R i)) k v hv hker hinj
  intro x hx j hj
  apply (mem_centeredIntegerBox _ _).mpr
  intro i
  have hxi := (mem_centeredIntegerBox R x).mp (hS hx) i
  have hjk : (j : ℤ) ≤ k := by exact_mod_cast hj.le
  have hbound : |x i + (j : ℤ) * v i| ≤ 2 * (R i : ℤ) := by
    calc
      _ ≤ |x i| + |(j : ℤ) * v i| := abs_add_le _ _
      _ = |x i| + (j : ℤ) * |v i| := by
        rw [abs_mul, abs_of_nonneg (Int.natCast_nonneg j)]
      _ ≤ (R i : ℤ) + (k : ℤ) * |v i| :=
        add_le_add hxi (mul_le_mul_of_nonneg_right hjk (abs_nonneg _))
      _ ≤ 2 * (R i : ℤ) := by linarith only [hshort i]
  change |x i + j • v i| ≤ ((2 * R i : ℕ) : ℤ)
  simpa only [nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat] using hbound

theorem injOn_small_integer_box_of_dense_subset (φ : (ι → ℤ) →+ G)
    (S : Finset (ι → ℤ)) (R r : ι → ℕ) (k : ℕ)
    (hS : S ⊆ centeredIntegerBox R) (hinj : Set.InjOn φ (S : Set _))
    (hlarge : (centeredIntegerBox (fun i => 2 * R i)).card < S.card * k)
    (hscale : ∀ i, 2 * k * r i ≤ R i) :
    Set.InjOn φ (centeredIntegerBox r : Set _) := by
  intro x hx y hy hxy
  apply sub_eq_zero.mp
  apply kernel_eq_zero_of_dense_integer_box φ S R k hS hinj hlarge (x - y)
  · rw [map_sub, hxy, sub_self]
  · intro i
    have hx' := (mem_centeredIntegerBox r x).mp hx i
    have hy' := (mem_centeredIntegerBox r y).mp hy i
    have hscale' : 2 * (k : ℤ) * (r i : ℤ) ≤ R i := by exact_mod_cast hscale i
    calc
      (k : ℤ) * |(x - y) i| ≤ (k : ℤ) * (|x i| + |y i|) :=
        mul_le_mul_of_nonneg_left (abs_sub _ _) (Int.natCast_nonneg k)
      _ ≤ (k : ℤ) * ((r i : ℤ) + (r i : ℤ)) :=
        mul_le_mul_of_nonneg_left (add_le_add hx' hy') (Int.natCast_nonneg k)
      _ = 2 * (k : ℤ) * (r i : ℤ) := by ring
      _ ≤ (R i : ℤ) := hscale'

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem integerSites_card_le {K S : Type*} [Fintype K] [Fintype S]
    (site : S → K → ℤ) (hsite : Function.Injective site) (R : ℕ)
    (hbound : ∀ s k, |site s k| ≤ (R : ℤ)) :
    Fintype.card S ≤ (2*R+1)^Fintype.card K := by
  classical
  let f : S → ↥(centeredIntegerBox (fun _ : K => R)) :=
    fun s => ⟨site s, (mem_centeredIntegerBox _ _).mpr (hbound s)⟩
  have hf : Function.Injective f := fun s t h => hsite (congrArg Subtype.val h)
  simpa only [Fintype.card_coe, card_centeredIntegerBox, Finset.prod_const,
    Finset.card_univ] using Fintype.card_le_of_injective f hf

theorem integerSites_card_le_exp {K S : Type*} [Fintype K] [Fintype S]
    (site : S → K → ℤ) (hsite : Function.Injective site) {P : ℝ} (hP : 0 ≤ P)
    (hK : (Fintype.card K : ℝ) ≤ P)
    (hbound : ∀ s k, |(site s k : ℝ)| ≤ Real.exp P) :
    (Fintype.card S : ℝ) ≤ Real.exp (P*(P+5)) := by
  have hcard := integerSites_card_le site hsite ⌈Real.exp P⌉₊ (fun s k => by
    exact_mod_cast (hbound s k).trans (Nat.le_ceil (Real.exp P)))
  have hceil := (Nat.ceil_lt_add_one (Real.exp_pos P).le).le
  have h1 : 1 ≤ Real.exp P := Real.one_le_exp_iff.mpr hP
  have h5 : (5 : ℝ) ≤ Real.exp 5 := by linarith [Real.add_one_le_exp (5 : ℝ)]
  have hbase : (2*⌈Real.exp P⌉₊+1 : ℝ) ≤ Real.exp (P+5) := by
    calc
      _ ≤ 5*Real.exp P := by linarith
      _ ≤ Real.exp P*Real.exp 5 := by nlinarith [Real.exp_pos P]
      _ = _ := (Real.exp_add P 5).symm
  calc
    _ ≤ ((2*⌈Real.exp P⌉₊+1 : ℕ) : ℝ)^Fintype.card K := by exact_mod_cast hcard
    _ ≤ (Real.exp (P+5))^Fintype.card K :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (by simpa only [Nat.cast_add,
        Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using hbase) _
    _ = Real.exp ((Fintype.card K : ℝ)*(P+5)) := (Real.exp_nat_mul _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hK (by linarith))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem injOn_shrunk_integer_box_of_distinct_points
    {r : ℕ} {G : Type*} [AddCommGroup G] (J : Finset G) (hJ : J.Nonempty)
    (R : Fin r → ℕ) (η : (Fin r → ℤ) →+ G) (a : G)
    (hrepr : ∀ h ∈ J, ∃ x : Fin r → ℤ,
      (∀ i, |x i| ≤ (R i : ℤ)) ∧ h = a + η x) :
    let k := (2 ^ r * ∏ i, (2 * R i + 1)) / J.card + 1
    Set.InjOn η (centeredIntegerBox (fun i => R i / (2 * k)) : Set _) := by
  intro k
  classical
  have hall (h : {h // h ∈ J}) : ∃ x : Fin r → ℤ,
      (∀ i, |x i| ≤ (R i : ℤ)) ∧ h.val = a + η x :=
    hrepr h.val h.property
  choose x hx heq using hall
  have hηx : Function.Injective (η ∘ x) := by
    intro h h' hh
    apply Subtype.ext
    rw [heq h, heq h']
    exact congrArg (fun z => a + z) hh
  have hxinj : Function.Injective x := by
    intro h h' hh
    exact hηx (congrArg η hh)
  let S := Finset.univ.image x
  have hS : S ⊆ centeredIntegerBox R := by
    intro z hz
    obtain ⟨h, _, rfl⟩ := Finset.mem_image.mp hz
    exact (mem_centeredIntegerBox R (x h)).mpr (hx h)
  have hScard : S.card = J.card := by
    rw [show S.card = (Finset.univ.image x).card from rfl,
      Finset.card_image_of_injective _ hxinj, Finset.card_univ, Fintype.card_coe]
  have hinj : Set.InjOn η (S : Set _) := by
    intro z hz w hw hzw
    obtain ⟨h, _, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨h', _, rfl⟩ := Finset.mem_image.mp hw
    exact congrArg x (hηx hzw)
  apply injOn_small_integer_box_of_dense_subset η S R (fun i => R i / (2 * k)) k hS hinj
  · apply (card_doubled_centeredIntegerBox_le R).trans_lt
    rw [card_centeredIntegerBox, Fintype.card_fin, hScard]
    exact Nat.lt_mul_div_succ (2 ^ r * ∏ i, (2 * R i + 1)) hJ.card_pos
  · intro i
    exact Nat.mul_div_le (R i) (2 * k)

theorem injOn_shrunk_integer_box_of_distinct_residues
    {r N : ℕ} [NeZero N] (J : Finset (ZMod N)) (hJ : J.Nonempty)
    (R : Fin r → ℕ) (η : (Fin r → ℤ) →+ ℤ) (a : ℤ)
    (hrepr : ∀ h ∈ J, ∃ x : Fin r → ℤ,
      (∀ i, |x i| ≤ (R i : ℤ)) ∧ (h.val : ℤ) = a + η x) :
    let k := (2 ^ r * ∏ i, (2 * R i + 1)) / J.card + 1
    Set.InjOn ((Int.castAddHom (ZMod N)).comp η)
      (centeredIntegerBox (fun i => R i / (2 * k)) : Set _) := by
  apply injOn_shrunk_integer_box_of_distinct_points J hJ R
    ((Int.castAddHom (ZMod N)).comp η) (a : ZMod N)
  intro h hh
  obtain ⟨x, hx, heq⟩ := hrepr h hh
  refine ⟨x, hx, ?_⟩
  change h = (a : ZMod N) + (η x : ZMod N)
  simpa only [Int.cast_add, Int.cast_natCast, ZMod.natCast_zmod_val] using
    congrArg (fun z : ℤ => (z : ZMod N)) heq

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def naturalScaleIntegerWindow (J : Type*) [Fintype J] (H : ℝ) (N : ℕ) :
    Finset (J → ℤ) := centeredIntegerBox (fun _ : J => ⌈H * (N : ℝ)⌉₊)

theorem mem_naturalScaleIntegerWindow_of_bound {J : Type*} [Fintype J]
    (H : ℝ) (N : ℕ) (z : J → ℤ) (hz : ∀ j, |(z j : ℝ)| ≤ H * N) :
    z ∈ naturalScaleIntegerWindow J H N := by
  apply (mem_centeredIntegerBox _ _).mpr
  intro j
  exact_mod_cast (hz j).trans (Nat.le_ceil (H * (N : ℝ)))

theorem naturalScaleIntegerWindow_card_le (J : Type*) [Fintype J]
    {H : ℝ} (hH : 0 ≤ H) {N : ℕ} (hN : 0 < N) :
    ((naturalScaleIntegerWindow J H N).card : ℝ) ≤
      (2 * H + 3) ^ Fintype.card J * (N : ℝ) ^ Fintype.card J := by
  have hceil := Nat.ceil_lt_add_one (mul_nonneg hH (Nat.cast_nonneg N))
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hb : 2 * (⌈H * (N : ℝ)⌉₊ : ℝ) + 1 ≤ (2 * H + 3) * N := by nlinarith
  have he : ((naturalScaleIntegerWindow J H N).card : ℝ) =
      (2 * (⌈H * (N : ℝ)⌉₊ : ℝ) + 1) ^ Fintype.card J := by
    simp only [naturalScaleIntegerWindow, card_centeredIntegerBox, Finset.prod_const,
      Finset.card_univ, Nat.cast_pow, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  rw [he]
  exact (pow_le_pow_left₀ (by positivity) hb _).trans_eq (mul_pow _ _ _)

noncomputable def naturalScaleProductWindow {A : Type*} [Fintype A]
    (J : A → Type*) [∀ a, Fintype (J a)] (H : A → ℝ) (N : A → ℕ) :
    Finset (∀ a, J a → ℤ) :=
  Fintype.piFinset (fun a => naturalScaleIntegerWindow (J a) (H a) (N a))

theorem mem_naturalScaleProductWindow_iff {A : Type*} [Fintype A]
    (J : A → Type*) [∀ a, Fintype (J a)] (H : A → ℝ) (N : A → ℕ)
    (z : ∀ a, J a → ℤ) :
    z ∈ naturalScaleProductWindow J H N ↔ ∀ a, z a ∈ naturalScaleIntegerWindow (J a) (H a) (N a) := by
  simp only [naturalScaleProductWindow, Fintype.mem_piFinset]

theorem naturalScaleProductWindow_card_le {A : Type*} [Fintype A]
    (J : A → Type*) [∀ a, Fintype (J a)] (H : A → ℝ) (N : A → ℕ)
    (hH : ∀ a, 0 ≤ H a) (hN : ∀ a, 0 < N a) :
    ((naturalScaleProductWindow J H N).card : ℝ) ≤
      (∏ a, (2 * H a + 3) ^ Fintype.card (J a)) *
        ∏ a, (N a : ℝ) ^ Fintype.card (J a) := by
  simp only [naturalScaleProductWindow, Fintype.card_piFinset, Nat.cast_prod]
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _)
    (fun a _ => naturalScaleIntegerWindow_card_le (J a) (hH a) (hN a))

end Erdos3

end

end OAI
