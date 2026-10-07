import OAI.Combinatorics.Progressions.Estimates.CyclicProgressionHom
import OAI.Combinatorics.Progressions.Estimates.DenseCyclicFreimanModel
import OAI.Combinatorics.Progressions.Estimates.DenseTranslate
import OAI.Combinatorics.Progressions.Estimates.FreimanFivefoldCardinality
import OAI.Combinatorics.Progressions.Estimates.NativeGraphSmallDifference
import OAI.Combinatorics.Progressions.Geometry.VariableRoundedGraphCoordinates
import OAI.Combinatorics.Progressions.Lattices.IntegerVectorFreimanEmbedding
import OAI.Combinatorics.Progressions.Lattices.ProperAffineBoxRestriction
import OAI.Combinatorics.Progressions.Lattices.SharedFreeAffineBudget

namespace OAI

section

namespace Erdos3.FreimanModel

def residueBlock {q : ℕ} [NeZero q] (x : ZMod q) : Fin 16 := by
  refine ⟨x.val / (q / 16 + 1), ?_⟩
  apply (Nat.div_lt_iff_lt_mul (Nat.succ_pos _)).mpr
  exact x.val_lt.trans (Nat.lt_mul_div_succ q (by decide))

def residueLift {q : ℕ} (x : ZMod q) : ℤ := x.val

theorem residueBlock_bounds {q : ℕ} [NeZero q] {x : ZMod q} {c : Fin 16}
    (hc : residueBlock x = c) :
    c.val * (q / 16 + 1) ≤ x.val ∧
      x.val ≤ c.val * (q / 16 + 1) + q / 16 := by
  have hdiv : x.val / (q / 16 + 1) = c.val := congrArg Fin.val hc
  have hmod := Nat.mod_lt x.val (Nat.succ_pos (q / 16))
  have hrem : x.val % (q / 16 + 1) ≤ q / 16 := Nat.le_of_lt_succ hmod
  have hid := Nat.mod_add_div x.val (q / 16 + 1)
  rw [hdiv, Nat.mul_comm (q / 16 + 1)] at hid
  omega

theorem residueLift_sum_cast {q : ℕ} [NeZero q] (T : Multiset (ZMod q)) :
    (((T.map residueLift).sum : ℤ) : ZMod q) = T.sum := by
  induction T using Multiset.induction_on with
  | empty => simp
  | @cons x T ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons, Int.cast_add, ih]
      simp [residueLift]

theorem residueLift_sum_bounds {q : ℕ} [NeZero q] {c : Fin 16}
    (T : Multiset (ZMod q)) (hT : T.card = 8)
    (hc : ∀ x ∈ T, residueBlock x = c) :
    (8 : ℤ) * (c.val * (q / 16 + 1) : ℕ) ≤ (T.map residueLift).sum ∧
      (T.map residueLift).sum ≤
        (8 : ℤ) * ((c.val * (q / 16 + 1) : ℕ) + (q / 16 : ℕ)) := by
  have hlo := Multiset.card_nsmul_le_sum
    (s := T.map residueLift) (a := ((c.val * (q / 16 + 1) : ℕ) : ℤ)) (by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hy
      change ((c.val * (q / 16 + 1) : ℕ) : ℤ) ≤ (x.val : ℤ)
      exact_mod_cast (residueBlock_bounds (hc x hx)).1)
  have hhi := Multiset.sum_le_card_nsmul
    (s := T.map residueLift) (n := (((c.val * (q / 16 + 1) : ℕ) + (q / 16 : ℕ)) : ℤ)) (by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hy
      change (x.val : ℤ) ≤ (((c.val * (q / 16 + 1) : ℕ) + (q / 16 : ℕ)) : ℤ)
      exact_mod_cast (residueBlock_bounds (hc x hx)).2)
  simpa only [Multiset.card_map, hT, nsmul_eq_mul, Nat.cast_add, Nat.cast_ofNat]
    using And.intro hlo hhi

theorem residueLift_sum_sub_abs_lt {q : ℕ} [NeZero q] {c : Fin 16}
    (T U : Multiset (ZMod q)) (hT : T.card = 8) (hU : U.card = 8)
    (hcT : ∀ x ∈ T, residueBlock x = c) (hcU : ∀ x ∈ U, residueBlock x = c) :
    |(T.map residueLift).sum - (U.map residueLift).sum| < (q : ℤ) := by
  obtain ⟨hTlo, hThi⟩ := residueLift_sum_bounds T hT hcT
  obtain ⟨hUlo, hUhi⟩ := residueLift_sum_bounds U hU hcU
  have hdiv : (16 : ℤ) * (q / 16 : ℕ) ≤ q := by
    exact_mod_cast Nat.mul_div_le q 16
  have hq : (0 : ℤ) < q := by exact_mod_cast NeZero.pos q
  rw [abs_lt]
  constructor <;> omega

theorem residueLift_sum_eq_iff {q : ℕ} [NeZero q] {c : Fin 16}
    (T U : Multiset (ZMod q)) (hT : T.card = 8) (hU : U.card = 8)
    (hcT : ∀ x ∈ T, residueBlock x = c) (hcU : ∀ x ∈ U, residueBlock x = c) :
    (T.map residueLift).sum = (U.map residueLift).sum ↔ T.sum = U.sum := by
  constructor
  · intro h
    simpa only [residueLift_sum_cast] using congrArg (fun z : ℤ => (z : ZMod q)) h
  · intro h
    have hsmall := abs_lt.mp (residueLift_sum_sub_abs_lt T U hT hU hcT hcU)
    have hdiv : (q : ℤ) ∣ (T.map residueLift).sum - (U.map residueLift).sum := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp
      rw [Int.cast_sub, residueLift_sum_cast, residueLift_sum_cast, h, sub_self]
    apply sub_eq_zero.mp
    apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdiv
    simpa only [Int.natAbs_natCast] using
      int_natAbs_lt_of_neg_lt_and_lt hsmall.1 hsmall.2

end Erdos3.FreimanModel

end

section

namespace Erdos3.FreimanModel

variable {I : Type*} (q : I → ℕ) [∀ i, NeZero (q i)]

def cyclicProductLift (x : ∀ i, ZMod (q i)) : I → ℤ := fun i => residueLift (x i)

def cyclicProductBlock (x : ∀ i, ZMod (q i)) : I → Fin 16 := fun i => residueBlock (x i)

theorem cyclicProductLift_injective : Function.Injective (cyclicProductLift q) := by
  intro x y h
  funext i
  have hi := congrArg (fun z : ℤ => (z : ZMod (q i))) (congrFun h i)
  simpa [cyclicProductLift, residueLift] using hi

omit [∀ i, NeZero (q i)] in
theorem cyclicProductLift_sum_apply (T : Multiset (∀ i, ZMod (q i))) (i : I) :
    ((T.map (cyclicProductLift q)).sum) i = (T.map fun x => residueLift (x i)).sum := by
  induction T using Multiset.induction_on with
  | empty => simp
  | @cons x T ih => simp [ih, cyclicProductLift]

omit [∀ i, NeZero (q i)] in
theorem cyclicProduct_sum_apply (T : Multiset (∀ i, ZMod (q i))) (i : I) :
    T.sum i = (T.map fun x => x i).sum := by
  induction T using Multiset.induction_on with
  | empty => simp
  | @cons x T ih => simp [ih]

theorem cyclicProductLift_sum_eq_iff {c : I → Fin 16}
    (T U : Multiset (∀ i, ZMod (q i))) (hT : T.card = 8) (hU : U.card = 8)
    (hcT : ∀ x ∈ T, cyclicProductBlock q x = c)
    (hcU : ∀ x ∈ U, cyclicProductBlock q x = c) :
    (T.map (cyclicProductLift q)).sum = (U.map (cyclicProductLift q)).sum ↔ T.sum = U.sum := by
  have hi (i : I) :
      ((T.map (cyclicProductLift q)).sum) i = ((U.map (cyclicProductLift q)).sum) i ↔
        T.sum i = U.sum i := by
    rw [cyclicProductLift_sum_apply, cyclicProductLift_sum_apply,
      cyclicProduct_sum_apply, cyclicProduct_sum_apply]
    have ht : ∀ x ∈ T.map (fun x => x i), residueBlock x = c i := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hx
      exact congrFun (hcT y hy) i
    have hu : ∀ x ∈ U.map (fun x => x i), residueBlock x = c i := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hx
      exact congrFun (hcU y hy) i
    simpa only [Multiset.map_map, Function.comp_def] using
      residueLift_sum_eq_iff (T.map fun x => x i) (U.map fun x => x i)
        (by simpa only [Multiset.card_map] using hT)
        (by simpa only [Multiset.card_map] using hU) ht hu
  constructor
  · intro h
    funext i
    exact (hi i).mp (congrFun h i)
  · intro h
    funext i
    exact (hi i).mpr (congrFun h i)

theorem isAddFreimanIso_cyclicProductLift [Fintype I]
    (A : Finset (∀ i, ZMod (q i))) {c : I → Fin 16}
    (hc : ∀ x ∈ A, cyclicProductBlock q x = c) :
    IsAddFreimanIso 8 (A : Set _) (A.image (cyclicProductLift q) : Set (I → ℤ))
      (cyclicProductLift q) := by
  refine ⟨⟨?_, (cyclicProductLift_injective q).injOn, ?_⟩, ?_⟩
  · intro x hx
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  · intro x hx
    exact Finset.mem_image.mp hx
  · intro T U hTA hUA hT hU
    exact cyclicProductLift_sum_eq_iff q T U hT hU
      (fun x hx => hc x (hTA hx)) (fun x hx => hc x (hUA hx))

theorem exists_large_cyclicProduct_integer_lift [Fintype I]
    (A : Finset (∀ i, ZMod (q i))) (hA : A.Nonempty) :
    ∃ J : Finset (∀ i, ZMod (q i)), J.Nonempty ∧ J ⊆ A ∧
      A.card ≤ 16 ^ Fintype.card I * J.card ∧
      IsAddFreimanIso 8 (J : Set _) (J.image (cyclicProductLift q) : Set (I → ℤ))
        (cyclicProductLift q) := by
  classical
  obtain ⟨c, hJ, hsize⟩ := exists_nonempty_large_fiber A hA (cyclicProductBlock q)
  let J := A.filter fun x => cyclicProductBlock q x = c
  refine ⟨J, hJ, Finset.filter_subset _ _, ?_, ?_⟩
  · simpa only [Fintype.card_fun, Fintype.card_fin] using hsize
  · apply isAddFreimanIso_cyclicProductLift q J
    intro x hx
    exact (Finset.mem_filter.mp hx).2

end Erdos3.FreimanModel

end

section

namespace Erdos3.FreimanModel

open scoped Pointwise

theorem exists_dense_cyclic_model_of_integer_vectors {I : Type*} [Fintype I]
    (A : Finset (I → ℤ)) (hA : A.Nonempty) {K : ℝ} (hK : 0 < K)
    (hsmall : ((A - A).card : ℝ) ≤ K * A.card) (s : ℕ) (hs : 0 < s) :
    ∃ (N : ℕ) (J : Finset (I → ℤ)) (B : Finset (ZMod N)) (f : (I → ℤ) → ZMod N),
      0 < N ∧ J.Nonempty ∧ J ⊆ A ∧ A.card ≤ (2 * s) * J.card ∧
      B.Nonempty ∧ B = J.image f ∧ B.card = J.card ∧
      IsAddFreimanIso s (J : Set _) (B : Set _) f ∧
      (N : ℝ) ≤ 2 * K ^ (2 * s) * A.card ∧
      (4 * (s : ℝ) * K ^ (2 * s))⁻¹ ≤ (B.card : ℝ) / N := by
  classical
  obtain ⟨e, he⟩ := exists_integer_freiman_embedding A s
  let X := A.image e
  have hX : X.Nonempty := hA.image e
  have hXcard : X.card = A.card := Finset.card_image_of_injOn he.bijOn.injOn
  have hXsmall : ((X - X).card : ℝ) ≤ K * X.card := by
    have hdiff : X - X = (A - A).image e := by
      ext z
      simp only [X, Finset.mem_sub, Finset.mem_image]
      constructor
      · rintro ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
        exact ⟨x - y, ⟨x, hx, y, hy, rfl⟩, e.map_sub x y⟩
      · rintro ⟨_, ⟨x, hx, y, hy, rfl⟩, rfl⟩
        exact ⟨e x, ⟨x, hx, rfl⟩, e y, ⟨y, hy, rfl⟩, (e.map_sub x y).symm⟩
    rw [hdiff, hXcard]
    exact (show (((A - A).image e).card : ℝ) ≤ (A - A).card by
      exact_mod_cast Finset.card_image_le).trans hsmall
  obtain ⟨N, X', B, g, hN, hX'ne, hX'sub, hsize, hBne, hB, hBcard,
      hg, hNsize, hdensity⟩ := exists_dense_cyclic_model X hX hK hXsmall s hs
  let J := A.filter fun x => e x ∈ X'
  have hJA : J ⊆ A := Finset.filter_subset _ _
  have hJimage : J.image e = X' := by
    ext z
    constructor
    · rintro hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
      exact (Finset.mem_filter.mp hx).2
    · intro hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp (hX'sub hz)
      exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, hz⟩, rfl⟩
  have heJ : IsAddFreimanIso s (J : Set _) (X' : Set ℤ) e := by
    apply he.subset hJA
    refine ⟨?_, he.bijOn.injOn.mono hJA, ?_⟩
    · intro x hx
      exact (Finset.mem_filter.mp hx).2
    · intro z hz
      rw [← hJimage] at hz
      exact Finset.mem_image.mp hz
  have hJcard : X'.card = J.card := by
    rw [← hJimage]
    exact Finset.card_image_of_injOn heJ.bijOn.injOn
  have hJne : J.Nonempty := by
    apply Finset.card_pos.mp
    rw [← hJcard]
    exact hX'ne.card_pos
  have hJsize : A.card ≤ (2 * s) * J.card := by
    simpa only [hXcard, hJcard] using hsize
  have hBimage : B = J.image (g ∘ e) := by
    rw [hB, ← hJimage, Finset.image_image]
  have hNsize' : (N : ℝ) ≤ 2 * K ^ (2 * s) * A.card := by
    simpa only [hXcard] using hNsize
  exact ⟨N, J, B, g ∘ e, hN, hJne, hJA, hJsize, hBne, hBimage,
    hBcard.trans hJcard, hg.comp heJ, hNsize', hdensity⟩

end Erdos3.FreimanModel

end

section

namespace Erdos3.FreimanModel

open scoped Pointwise

theorem exists_dense_cyclicProduct_integer_model {I : Type*} [Fintype I]
    (q : I → ℕ) [∀ i, NeZero (q i)] (A : Finset (∀ i, ZMod (q i)))
    (hA : A.Nonempty) {K : ℝ} (hK : 0 < K)
    (hsmall : ((A - A).card : ℝ) ≤ K * A.card) :
    ∃ (N : ℕ) (J : Finset (∀ i, ZMod (q i))) (B : Finset (ZMod N))
      (g : (I → ℤ) → ZMod N),
      0 < N ∧ J.Nonempty ∧ J ⊆ A ∧
      A.card ≤ 16 ^ (Fintype.card I + 1) * J.card ∧
      B.Nonempty ∧ B = (J.image (cyclicProductLift q)).image g ∧ B.card = J.card ∧
      IsAddFreimanIso 8 (J : Set _) (J.image (cyclicProductLift q) : Set (I → ℤ))
        (cyclicProductLift q) ∧
      IsAddFreimanIso 8 (J.image (cyclicProductLift q) : Set (I → ℤ)) (B : Set _) g ∧
      (N : ℝ) ≤ 2 * (K * 16 ^ Fintype.card I) ^ 16 * A.card ∧
      (32 * (K * 16 ^ Fintype.card I) ^ 16)⁻¹ ≤ (B.card : ℝ) / N := by
  classical
  obtain ⟨A₀, hA₀, hA₀A, hlarge, he⟩ := exists_large_cyclicProduct_integer_lift q A hA
  let e := cyclicProductLift q
  let X := A₀.image e
  let R : ℝ := K * 16 ^ Fintype.card I
  have hR : 0 < R := mul_pos hK (by positivity)
  have hX : X.Nonempty := hA₀.image e
  have hXcard : X.card = A₀.card := Finset.card_image_of_injOn he.bijOn.injOn
  have hdiff : (X - X).card = (A₀ - A₀).card :=
    card_difference_image_of_freiman A₀ e (he.mono (hmn := by decide))
  have hsub : A₀ - A₀ ⊆ A - A := by
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_sub.mp hx
    exact Finset.mem_sub.mpr ⟨a, hA₀A ha, b, hA₀A hb, rfl⟩
  have hlargeR : (A.card : ℝ) ≤ 16 ^ Fintype.card I * A₀.card := by
    exact_mod_cast hlarge
  have hXsmall : ((X - X).card : ℝ) ≤ R * X.card := by
    rw [hdiff, hXcard]
    calc
      ((A₀ - A₀).card : ℝ) ≤ (A - A).card := by exact_mod_cast Finset.card_le_card hsub
      _ ≤ K * A.card := hsmall
      _ ≤ K * (16 ^ Fintype.card I * A₀.card) := mul_le_mul_of_nonneg_left hlargeR hK.le
      _ = R * A₀.card := by simp only [R, mul_assoc]
  obtain ⟨N, X', B, g, hN, hX', hX'X, hsize, hB, hBimage, hBcard, hg, hNsize, hdensity⟩ :=
    exists_dense_cyclic_model_of_integer_vectors X hX hR hXsmall 8 (by decide)
  let J := A₀.filter fun x => e x ∈ X'
  have hJA₀ : J ⊆ A₀ := Finset.filter_subset _ _
  have hJimage : J.image e = X' := by
    ext z
    constructor
    · intro hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
      exact (Finset.mem_filter.mp hx).2
    · intro hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp (hX'X hz)
      exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, hz⟩, rfl⟩
  have heJ : IsAddFreimanIso 8 (J : Set _) (X' : Set (I → ℤ)) e := by
    apply he.subset hJA₀
    refine ⟨?_, he.bijOn.injOn.mono hJA₀, ?_⟩
    · intro x hx
      exact (Finset.mem_filter.mp hx).2
    · intro z hz
      rw [← hJimage] at hz
      exact Finset.mem_image.mp hz
  have hJcard : X'.card = J.card := by
    rw [← hJimage]
    exact Finset.card_image_of_injOn heJ.bijOn.injOn
  have hJ : J.Nonempty := by
    apply Finset.card_pos.mp
    rw [← hJcard]
    exact hX'.card_pos
  have hsize₀ : A₀.card ≤ 16 * J.card := by
    simpa only [hXcard, hJcard, Nat.reduceMul] using hsize
  have hsize' : A.card ≤ 16 ^ (Fintype.card I + 1) * J.card := by
    calc
      A.card ≤ 16 ^ Fintype.card I * A₀.card := hlarge
      _ ≤ 16 ^ Fintype.card I * (16 * J.card) := Nat.mul_le_mul_left _ hsize₀
      _ = _ := by rw [pow_succ, mul_assoc]
  have hBimage' : B = (J.image e).image g := by
    rw [hJimage]
    exact hBimage
  have hNsize' : (N : ℝ) ≤ 2 * R ^ 16 * A.card := by
    have hcard : (X.card : ℝ) ≤ A.card := by rw [hXcard]; exact_mod_cast Finset.card_le_card hA₀A
    have hn : (N : ℝ) ≤ 2 * R ^ 16 * X.card := by
      simpa only [Nat.reduceMul] using hNsize
    exact hn.trans
      (mul_le_mul_of_nonneg_left hcard (by positivity))
  refine ⟨N, J, B, g, hN, hJ, hJA₀.trans hA₀A, hsize', hB, hBimage',
    hBcard.trans hJcard, ?_, ?_, hNsize', ?_⟩
  · change IsAddFreimanIso 8 (J : Set _) (J.image e : Set (I → ℤ)) e
    rw [hJimage]
    exact heJ
  · change IsAddFreimanIso 8 (J.image e : Set (I → ℤ)) (B : Set _) g
    rw [hJimage]
    exact hg
  · norm_num only [Nat.reduceMul, Nat.cast_ofNat, mul_one] at hdensity
    simpa only [R, show (4 : ℝ) * 8 = 32 by norm_num] using hdensity

end Erdos3.FreimanModel

end

section

namespace Erdos3.FreimanModel

open scoped Pointwise

variable {I : Type*}

def variableIntegerGraphLift (N : ℕ) (M : I → ℕ)
    (x : ZMod N × (∀ i, ZMod (M i))) : Option I → ℤ :=
  cyclicProductLift (variableRoundedGraphModuli N M)
    (variableRoundedGraphCoordinateEquiv N M x)

def variableIntegerGraphReduction (N : ℕ) (M : I → ℕ) :
    (Option I → ℤ) →+ (ZMod N × (∀ i, ZMod (M i))) where
  toFun z := ((z none : ZMod N), fun i => (z (some i) : ZMod (M i)))
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp

@[simp] theorem variableIntegerGraphReduction_lift (N : ℕ) (M : I → ℕ)
    [NeZero N] [∀ i, NeZero (M i)] (x : ZMod N × (∀ i, ZMod (M i))) :
    variableIntegerGraphReduction N M (variableIntegerGraphLift N M x) = x := by
  apply Prod.ext
  · change (((x.1.val : ℤ) : ZMod N)) = x.1
    simp only [Int.cast_natCast, ZMod.natCast_zmod_val]
  · funext i
    change ((((x.2 i).val : ℤ) : ZMod (M i))) = x.2 i
    simp only [Int.cast_natCast, ZMod.natCast_zmod_val]

@[simp] theorem variableIntegerGraphLift_none (N : ℕ) (M : I → ℕ)
    (x : ZMod N × (∀ i, ZMod (M i))) :
    variableIntegerGraphLift N M x none = (x.1.val : ℤ) := rfl

@[simp] theorem variableIntegerGraphLift_some (N : ℕ) (M : I → ℕ)
    (x : ZMod N × (∀ i, ZMod (M i))) (i : I) :
    variableIntegerGraphLift N M x (some i) = ((x.2 i).val : ℤ) := rfl

theorem variableIntegerGraphLift_injective (N : ℕ) (M : I → ℕ)
    [NeZero N] [∀ i, NeZero (M i)] : Function.Injective (variableIntegerGraphLift N M) := by
  intro x y h
  have heq := congrArg (variableIntegerGraphReduction N M) h
  simpa only [variableIntegerGraphReduction_lift] using heq

theorem exists_variableIntegerGraph_cyclic_model [Fintype I]
    (N : ℕ) (M : I → ℕ) [NeZero N] [∀ i, NeZero (M i)]
    (A : Finset (ZMod N × (∀ i, ZMod (M i)))) (hA : A.Nonempty)
    {K : ℝ} (hK : 0 < K) (hsmall : ((A - A).card : ℝ) ≤ K * A.card) :
    ∃ (Q : ℕ) (S : Finset (Option I → ℤ)) (B : Finset (ZMod Q))
      (g : (Option I → ℤ) → ZMod Q),
      0 < Q ∧ S.Nonempty ∧ S ⊆ A.image (variableIntegerGraphLift N M) ∧
      A.card ≤ 16 ^ (Fintype.card I + 2) * S.card ∧
      B.Nonempty ∧ B = S.image g ∧ B.card = S.card ∧
      IsAddFreimanIso 8 (S : Set _) (B : Set _) g ∧
      (Q : ℝ) ≤ 2 * (K * 16 ^ (Fintype.card I + 1)) ^ 16 * A.card ∧
      (32 * (K * 16 ^ (Fintype.card I + 1)) ^ 16)⁻¹ ≤ (B.card : ℝ) / Q := by
  classical
  let q : Option I → ℕ := variableRoundedGraphModuli N M
  let _ : ∀ i, NeZero (q i) := variableRoundedGraphModuli_neZero N M
  let e := variableRoundedGraphCoordinateEquiv (I := I) N M
  let X := A.image e
  have he : IsAddFreimanIso 8 (A : Set _) (X : Set _) e :=
    isAddFreimanIso_of_injOn_iterated_sums e.toAddMonoidHom A 8
      e.injective.injOn e.injective.injOn
  have hX : X.Nonempty := hA.image e
  have hXcard : X.card = A.card := Finset.card_image_of_injOn e.injective.injOn
  have hXsmall : ((X - X).card : ℝ) ≤ K * X.card := by
    rw [card_difference_image_of_freiman A e (he.mono (hmn := by decide)), hXcard]
    exact hsmall
  obtain ⟨Q, J, B, g, hQ, hJ, hJX, hsize, hB, hBimage, hBcard, hlift, hg,
      hQsize, hdensity⟩ := exists_dense_cyclicProduct_integer_model q X hX hK hXsmall
  let S := J.image (cyclicProductLift q)
  have hScard : S.card = J.card := Finset.card_image_of_injOn hlift.bijOn.injOn
  have hSA : S ⊆ A.image (variableIntegerGraphLift N M) := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp (hJX hx)
    exact Finset.mem_image.mpr ⟨y, hy, rfl⟩
  refine ⟨Q, S, B, g, hQ, hJ.image _, hSA, ?_, hB, hBimage,
    hBcard.trans hScard.symm, hg, ?_, ?_⟩
  · simpa only [hXcard, hScard, Fintype.card_option, Nat.add_assoc] using hsize
  · simpa only [hXcard, Fintype.card_option] using hQsize
  · simpa only [Fintype.card_option] using hdensity

end Erdos3.FreimanModel

end

section

namespace Erdos3.FreimanModel

open scoped Pointwise BigOperators
open CyclicCrootSisask

theorem exists_bounded_affine_box_of_cyclic_model {G : Type*} [AddCommGroup G] [DecidableEq G]
    {Q : ℕ} [NeZero Q] (A : Finset G) (hA : A.Nonempty) (B : Finset (ZMod Q))
    (hB : B.Nonempty) (f : G → ZMod Q) (hf : IsAddFreimanIso 8 (A : Set _) (B : Set _) f)
    {p : ℝ} (hp : 0 ≤ p) (hdensity : Real.exp (-p) * Q ≤ (B.card : ℝ)) :
    ∃ F ⊆ A, F.Nonempty ∧
      Real.exp (-(quarticBogolyubovProgressionConstant * (p + 1) ^ 8)) * A.card ≤ (F.card : ℝ) ∧
      ∃ (r : ℕ) (R : Fin r → ℕ) (Φ : (Fin r → ℤ) →+ G) (base : G),
        (r : ℝ) ≤ 2 + quarticBogolyubovConstant * (p + 1) ^ 4 ∧
        (∏ i, (2 * R i + 1)) ≤ Q ∧
        Set.InjOn Φ {x | ∀ i, |x i| ≤ (R i : ℤ)} ∧
        ∀ a ∈ F, ∃ x : Fin r → ℤ, (∀ i, |x i| ≤ (R i : ℤ)) ∧ a = base + Φ x := by
  classical
  obtain ⟨T, hrank, hT, hTsub, hTsize⟩ := exists_quartic_bogolyubov_progression B hp hdensity
  obtain ⟨L, hmap, hinj, hzero, hadd⟩ := exists_fourfold_lift_of_eight_iso A B hB f hf
  have hpair (x y z t : T.Param) (h : T.eval x + T.eval y = T.eval z + T.eval t) :
      L (T.eval x) + L (T.eval y) = L (T.eval z) + L (T.eval t) :=
    (hadd _ (hTsub (T.eval_mem_carrier x)) _ (hTsub (T.eval_mem_carrier y))
      _ (hTsub (T.eval_mem_carrier z)) _ (hTsub (T.eval_mem_carrier t))).mpr h
  let Φ := T.freimanHom L
  let S := T.coefficientBox.image Φ
  have hS : S ⊆ 2 • A - 2 • A := by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨y, rfl⟩ := T.mem_coefficientBox.mp hx
    change T.freimanHom L (T.coeff y) ∈ _
    rw [T.freimanHom_coeff L hzero hpair]
    exact hmap (hTsub (T.eval_mem_carrier y))
  have hScard : S.card = T.carrier.card := by
    change (T.coefficientBox.image (T.freimanHom L)).card = T.carrier.card
    rw [T.image_freimanHom L hzero hpair]
    exact Finset.card_image_of_injOn (hinj.mono hTsub)
  have hbound : ((A - S).card : ℝ) ≤ (Q : ℝ) := by
    have h := card_sub_le_of_fourfold_subset A S f (hf.mono (hmn := by decide)) hS
    have h' : (A - S).card ≤ Q := by simpa only [ZMod.card] using h
    exact_mod_cast h'
  have hsize : Real.exp (-(quarticBogolyubovProgressionConstant * (p + 1) ^ 8)) * Q ≤
      (S.card : ℝ) := by rw [hScard]; exact hTsize
  obtain ⟨base, _hbase, F, hFA, hF, hFsize, hFsub⟩ := exists_dense_translate A S hA
    (Real.exp_pos _) (by exact_mod_cast NeZero.pos Q) hbound hsize
  refine ⟨F, hFA, hF, hFsize, T.rank, T.radius, Φ, base, hrank, ?_, ?_, ?_⟩
  · rw [← T.card_carrier_of_proper hT]
    simpa only [ZMod.card] using Finset.card_le_univ T.carrier
  · intro x hx y hy hxy
    exact T.freimanHom_injOn hT L (hinj.mono hTsub) hzero hpair
      (T.mem_coefficientBox_iff_abs_le.mpr hx) (T.mem_coefficientBox_iff_abs_le.mpr hy) hxy
  · intro a ha
    obtain ⟨x, hx, heq⟩ := Finset.mem_image.mp (hFsub a ha)
    refine ⟨x, T.mem_coefficientBox_iff_abs_le.mp hx, ?_⟩
    rw [heq]
    abel

end Erdos3.FreimanModel

end

section

namespace Erdos3.NativeRankRelation.CommonData

open scoped Pointwise BigOperators
open CyclicCrootSisask

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

theorem integer_graph_affine_model {I : Type*} [Fintype I]
    (a : ZMod N → I → ℝ) (c : I → ℝ) (M l : I → ℕ) [∀ i, NeZero (M i)] (ε : I → ℝ)
    (hsmall : ∀ i, (M i : ℝ) * l i * ε i ≤ 1)
    (hnear : ∀ t ∈ D.quadruples, ∃ q ∈ coordinateDenominatorGrid l,
      ∀ i, |c i + (a (rankQuadrupleParameters t 1) i + a (rankQuadrupleParameters t 2) i -
        a (rankQuadrupleParameters t 0) i - a (rankQuadrupleParameters t 3) i) - q i| ≤ ε i) :
    let K := Real.exp (P + 13 * Fintype.card I)
    let z := roundedModelLogBudget P (Fintype.card I)
    let δ := Real.exp (-(quarticBogolyubovProgressionConstant * (z + 1) ^ 8))
    let v := fun h => variableRoundedCoefficient M l (a h)
    ∃ J' ⊆ H, J'.Nonempty ∧
      δ * ((2 ^ 4 : ℝ)⁻¹ * K⁻¹ * H.card) ≤ 16 ^ (Fintype.card I + 2) * (J'.card : ℝ) ∧
      ∃ (r : ℕ) (R : Fin r → ℕ)
        (Φ : (Fin r → ℤ) →+ (Option I → ℤ))
        (base : Option I → ℤ),
        (r : ℝ) ≤ 2 + quarticBogolyubovConstant * (z + 1) ^ 4 ∧
        ((∏ i, (2 * R i + 1) : ℕ) : ℝ) ≤
          2 * ((2 ^ 14 : ℝ) * K ^ 6 * 16 ^ (Fintype.card I + 1)) ^ 16 * H.card ∧
        Set.InjOn Φ {x | ∀ i, |x i| ≤ (R i : ℤ)} ∧
        ∀ h ∈ J', ∃ x : Fin r → ℤ,
          (∀ i, |x i| ≤ (R i : ℤ)) ∧
            FreimanModel.variableIntegerGraphLift N M (h, v h) = base + Φ x := by
  intro K z δ v
  classical
  obtain ⟨J, hJH, hJ, hsize, hsmallJ⟩ :=
    D.variable_graph_small_difference a c M l ε hsmall hnear
  let A := additiveGraph J v
  have hA : A.Nonempty := hJ.image _
  have hAsmall : ((A - A).card : ℝ) ≤ (2 ^ 14 : ℝ) * K ^ 6 * A.card := by
    simpa only [A, additiveGraph_card] using hsmallJ
  obtain ⟨Q, S, B, f, hQ, hS, hSA, hASsize, hB, _hBimage, _hBcard, hf,
      hQsize, hdensity⟩ :=
    FreimanModel.exists_variableIntegerGraph_cyclic_model N M A hA
      (by dsimp [K]; positivity) hAsmall
  let _ : NeZero Q := ⟨hQ.ne'⟩
  have hdensity' : Real.exp (-z) * Q ≤ (B.card : ℝ) := by
    apply (le_div_iff₀ (by exact_mod_cast hQ : (0 : ℝ) < Q)).mp
    exact (exp_neg_roundedModelLogBudget_le_density P (Fintype.card I)).trans hdensity
  obtain ⟨F, hFS, hF, hFsize, r, R, Φ, base, hrank, hbox, hinj, hrepr⟩ :=
    FreimanModel.exists_bounded_affine_box_of_cyclic_model S hS B hB f hf
      (roundedModelLogBudget_nonneg P (Fintype.card I)) hdensity'
  have hboxSize : ((∏ i, (2 * R i + 1) : ℕ) : ℝ) ≤
      2 * ((2 ^ 14 : ℝ) * K ^ 6 * 16 ^ (Fintype.card I + 1)) ^ 16 * H.card := by
    have hcast : ((∏ i, (2 * R i + 1) : ℕ) : ℝ) ≤ Q := by exact_mod_cast hbox
    have hJcard : (A.card : ℝ) ≤ H.card := by
      rw [show A.card = J.card from additiveGraph_card J v]
      exact_mod_cast Finset.card_le_card hJH
    exact hcast.trans (hQsize.trans (mul_le_mul_of_nonneg_left hJcard (by positivity)))
  have hFA : F ⊆ A.image (FreimanModel.variableIntegerGraphLift N M) := hFS.trans hSA
  let π : (Option I → ℤ) → ZMod N := fun z => (z none : ZMod N)
  have hback (z : Option I → ℤ) (hz : z ∈ F) :
      π z ∈ J ∧ FreimanModel.variableIntegerGraphLift N M (π z, v (π z)) = z := by
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp (hFA hz)
    obtain ⟨hyJ, hyv⟩ := (mem_additiveGraph_iff J v y).mp hy
    have hπ : π (FreimanModel.variableIntegerGraphLift N M y) = y.1 := by
      simp [π]
    rw [hπ]
    exact ⟨hyJ, congrArg (FreimanModel.variableIntegerGraphLift N M) (Prod.ext rfl hyv.symm)⟩
  let J' := F.image π
  have hπinj : Set.InjOn π (F : Set _) := by
    intro x hx y hy hxy
    calc
      x = FreimanModel.variableIntegerGraphLift N M (π x, v (π x)) := (hback x hx).2.symm
      _ = FreimanModel.variableIntegerGraphLift N M (π y, v (π y)) := by rw [hxy]
      _ = y := (hback y hy).2
  have hFcard : F.card = J'.card := (Finset.card_image_of_injOn hπinj).symm
  have hJ' : J' ⊆ H := by
    intro h hh
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hh
    exact hJH (hback z hz).1
  have hJS : (J.card : ℝ) ≤ 16 ^ (Fintype.card I + 2) * (S.card : ℝ) := by
    have h : J.card ≤ 16 ^ (Fintype.card I + 2) * S.card := by
      simpa only [A, additiveGraph_card] using hASsize
    exact_mod_cast h
  have hretain : δ * (S.card : ℝ) ≤ (J'.card : ℝ) := by
    simpa only [hFcard] using hFsize
  refine ⟨J', hJ', hF.image _, ?_, r, R, Φ, base, hrank, hboxSize, hinj, ?_⟩
  · calc
      _ ≤ δ * (J.card : ℝ) := mul_le_mul_of_nonneg_left hsize (Real.exp_pos _).le
      _ ≤ δ * (16 ^ (Fintype.card I + 2) * (S.card : ℝ)) :=
        mul_le_mul_of_nonneg_left hJS (Real.exp_pos _).le
      _ = 16 ^ (Fintype.card I + 2) * (δ * S.card) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hretain (by positivity)
  · intro h hh
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hh
    rw [(hback z hz).2]
    exact hrepr z hz

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open scoped BigOperators Pointwise
open CyclicCrootSisask

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

theorem integer_affine_graph_recovery {I : Type*} [Fintype I]
    (a : ZMod N → I → ℝ) (c : I → ℝ) (l : I → ℕ) (hl : ∀ i, 0 < l i)
    (ε : I → ℝ) (hε : ∀ i, 0 < ε i) (hsmall : ∀ i, 2 * (l i : ℝ) * ε i ≤ 1)
    (hnear : ∀ t ∈ D.quadruples, ∃ q ∈ coordinateDenominatorGrid l,
      ∀ i, |c i + (a (rankQuadrupleParameters t 1) i + a (rankQuadrupleParameters t 2) i -
        a (rankQuadrupleParameters t 0) i - a (rankQuadrupleParameters t 3) i) - q i| ≤ ε i) :
    let K := Real.exp (P + 13 * Fintype.card I)
    let z := roundedModelLogBudget P (Fintype.card I)
    let δ := Real.exp (-(quarticBogolyubovProgressionConstant * (z + 1) ^ 8))
    ∃ M : I → ℕ, (∀ i, 0 < M i) ∧
      (∀ i, (M i : ℝ) * l i * ε i ≤ 1) ∧
      (∀ i, 1 / ((M i : ℝ) * l i) ≤ 2 * ε i) ∧
      ∃ J' ⊆ H, J'.Nonempty ∧
        δ * ((2 ^ 4 : ℝ)⁻¹ * K⁻¹ * H.card) ≤ 16 ^ (Fintype.card I + 2) * (J'.card : ℝ) ∧
        ∃ (r : ℕ) (R : Fin r → ℕ)
          (Φ : (Fin r → ℤ) →+ (Option I → ℤ))
          (base : Option I → ℤ),
          (r : ℝ) ≤ 2 + quarticBogolyubovConstant * (z + 1) ^ 4 ∧
          ((∏ i, (2 * R i + 1) : ℕ) : ℝ) ≤
            2 * ((2 ^ 14 : ℝ) * K ^ 6 * 16 ^ (Fintype.card I + 1)) ^ 16 * H.card ∧
          Set.InjOn Φ {x | ∀ i, |x i| ≤ (R i : ℤ)} ∧
          (let reduce := FreimanModel.variableIntegerGraphReduction N M
           let ψ := (AddMonoidHom.snd (ZMod N) (∀ i, ZMod (M i))).comp (reduce.comp Φ)
           let α := variableCoefficientLift l (reduce base).2
           let β := fun j => variableCoefficientLift l (ψ (Pi.single j 1))
           (∀ i, α i ∈ Set.Ico (0 : ℝ) (1 / l i)) ∧
           (∀ j i, β j i ∈ Set.Ico (0 : ℝ) (1 / l i)) ∧
           ∀ h ∈ J', ∃ x : Fin r → ℤ,
             (∀ i, |x i| ≤ (R i : ℤ)) ∧
             (h.val : ℤ) = base none + Φ x none ∧
             FreimanModel.variableIntegerGraphLift N M
               (h, variableRoundedCoefficient M l (a h)) = base + Φ x ∧
             (∀ y : Fin r → ℤ, (∀ i, |y i| ≤ (R i : ℤ)) →
               FreimanModel.variableIntegerGraphLift N M
                 (h, variableRoundedCoefficient M l (a h)) = base + Φ y → y = x) ∧
             ∃ q ∈ coordinateDenominatorGrid l, ∀ i,
               |a h i - (α + ∑ j, (x j : ℝ) • β j) i - q i| ≤ 2 * ε i) := by
  intro K z δ
  obtain ⟨M, hM, hMsmall, hMerror⟩ := exists_coordinate_rounding_moduli l hl ε hε hsmall
  let _ : ∀ i, NeZero (M i) := fun i => ⟨(hM i).ne'⟩
  obtain ⟨J', hJH, hJ, hsize, r, R, Φ, base, hrank, hbox, hinj, hrepr⟩ :=
    D.integer_graph_affine_model a c M l ε hMsmall hnear
  refine ⟨M, hM, hMsmall, hMerror, J', hJH, hJ, hsize, r, R, Φ, base,
    hrank, hbox, hinj, ?_⟩
  dsimp only
  refine ⟨variableCoefficientLift_mem_Ico l hl _, ?_, ?_⟩
  · intro j
    exact variableCoefficientLift_mem_Ico l hl _
  · intro h hh
    obtain ⟨x, hx, heq⟩ := hrepr h hh
    refine ⟨x, hx, ?_, heq, ?_, ?_⟩
    · exact congrFun heq none
    · intro y hy hey
      exact hinj hy hx (add_left_cancel (hey.symm.trans heq))
    · let reduce := FreimanModel.variableIntegerGraphReduction N M
      have hred : (h, variableRoundedCoefficient M l (a h)) =
          reduce base + reduce (Φ x) := by
        have hr := congrArg reduce heq
        simpa only [reduce, FreimanModel.variableIntegerGraphReduction_lift, map_add] using hr
      obtain ⟨q, hq, herr⟩ := exists_variable_unrounded_affine l hl (reduce base).2
        ((AddMonoidHom.snd (ZMod N) (∀ i, ZMod (M i))).comp (reduce.comp Φ)) x (a h)
        (congrArg Prod.snd hred)
      exact ⟨q, hq, fun i => (herr i).trans (hMerror i)⟩

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open scoped Pointwise BigOperators
open CyclicCrootSisask

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

theorem proper_integer_graph_affine_model {I : Type*} [Fintype I]
    (a : ZMod N → I → ℝ) (c : I → ℝ) (M l : I → ℕ) [∀ i, NeZero (M i)] (ε : I → ℝ)
    (hsmall : ∀ i, (M i : ℝ) * l i * ε i ≤ 1)
    (hnear : ∀ t ∈ D.quadruples, ∃ q ∈ coordinateDenominatorGrid l,
      ∀ i, |c i + (a (rankQuadrupleParameters t 1) i + a (rankQuadrupleParameters t 2) i -
        a (rankQuadrupleParameters t 0) i - a (rankQuadrupleParameters t 3) i) - q i| ≤ ε i) :
    let K := Real.exp (P + 13 * Fintype.card I)
    let z := roundedModelLogBudget P (Fintype.card I)
    let δ := Real.exp (-(quarticBogolyubovProgressionConstant * (z + 1) ^ 8))
    let v := fun h => variableRoundedCoefficient M l (a h)
    ∃ J₀ ⊆ H, J₀.Nonempty ∧
      δ * ((2 ^ 4 : ℝ)⁻¹ * K⁻¹ * H.card) ≤ 16 ^ (Fintype.card I + 2) * (J₀.card : ℝ) ∧
      ∃ (r : ℕ) (R : Fin r → ℕ) (Φ : (Fin r → ℤ) →+ (Option I → ℤ)),
        (r : ℝ) ≤ 2 + quarticBogolyubovConstant * (z + 1) ^ 4 ∧
        ((∏ i, (2 * R i + 1) : ℕ) : ℝ) ≤
          2 * ((2 ^ 14 : ℝ) * K ^ 6 * 16 ^ (Fintype.card I + 1)) ^ 16 * H.card ∧
        (let k := (2 ^ r * ∏ i, (2 * R i + 1)) / J₀.card + 1
         let reduce := FreimanModel.variableIntegerGraphReduction N M
         let η := (AddMonoidHom.fst (ZMod N) (∀ i, ZMod (M i))).comp (reduce.comp Φ)
         ∃ J ⊆ J₀, J.Nonempty ∧ J₀.card ≤ (4 * k) ^ r * J.card ∧
           ∃ base : Option I → ℤ,
             Set.InjOn η (centeredIntegerBox (fun i => R i / (2 * k)) : Set _) ∧
             ∀ h ∈ J, ∃ x : Fin r → ℤ,
               (∀ i, |x i| ≤ (R i / (2 * k) : ℕ)) ∧
               FreimanModel.variableIntegerGraphLift N M (h, v h) = base + Φ x) := by
  intro K z δ v
  classical
  obtain ⟨J₀, hJ₀H, hJ₀, hsize, r, R, Φ, base, hrank, hvolume, _hfull, hrepr⟩ :=
    D.integer_graph_affine_model a c M l ε hsmall hnear
  let reduce := FreimanModel.variableIntegerGraphReduction N M
  let η := (AddMonoidHom.fst (ZMod N) (∀ i, ZMod (M i))).comp (reduce.comp Φ)
  have hall (h : {h // h ∈ J₀}) : ∃ x : Fin r → ℤ,
      (∀ i, |x i| ≤ (R i : ℤ)) ∧
      FreimanModel.variableIntegerGraphLift N M (h.val, v h.val) = base + Φ x :=
    hrepr h.val h.property
  choose x hx hgraph using hall
  have hspace (h : {h // h ∈ J₀}) : h.val = (reduce base).1 + η (x h) := by
    change h.val = (reduce base).1 + (reduce (Φ (x h))).1
    have hh := congrArg (fun y => (reduce y).1) (hgraph h)
    simpa only [reduce, FreimanModel.variableIntegerGraphReduction_lift, map_add,
      Prod.fst_add] using hh
  obtain ⟨J, hJJ₀, hJ, hretain, t, hproper, hsmallBox⟩ :=
    exists_dense_proper_coordinate_restriction J₀ hJ₀ R η (reduce base).1 x hx hspace
  refine ⟨J₀, hJ₀H, hJ₀, hsize, r, R, Φ, hrank, hvolume, J, hJJ₀,
    hJ, hretain, base + Φ t, hproper, ?_⟩
  intro h hh
  let h₀ : {h // h ∈ J₀} := ⟨h, hJJ₀ hh⟩
  refine ⟨x h₀ - t, hsmallBox ⟨h, hh⟩, ?_⟩
  rw [hgraph h₀, map_sub]
  abel

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open scoped BigOperators Pointwise
open CyclicCrootSisask

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

theorem proper_affine_graph_recovery {I : Type*} [Fintype I] (hP : 0 ≤ P)
    (a : ZMod N → I → ℝ) (c : I → ℝ) (l : I → ℕ) (hl : ∀ i, 0 < l i)
    (ε : I → ℝ) (hε : ∀ i, 0 < ε i) (hsmall : ∀ i, 2 * (l i : ℝ) * ε i ≤ 1)
    (hnear : ∀ t ∈ D.quadruples, ∃ q ∈ coordinateDenominatorGrid l,
      ∀ i, |c i + (a (rankQuadrupleParameters t 1) i + a (rankQuadrupleParameters t 2) i -
        a (rankQuadrupleParameters t 0) i - a (rankQuadrupleParameters t 3) i) - q i| ≤ ε i) :
    let K := Real.exp (P + 13 * Fintype.card I)
    let z := roundedModelLogBudget P (Fintype.card I)
    let δ := Real.exp (-(quarticBogolyubovProgressionConstant * (z + 1) ^ 8))
    ∃ M : I → ℕ, (∀ i, 0 < M i) ∧
      (∀ i, (M i : ℝ) * l i * ε i ≤ 1) ∧
      (∀ i, 1 / ((M i : ℝ) * l i) ≤ 2 * ε i) ∧
      ∃ J₀ ⊆ H, J₀.Nonempty ∧
        δ * ((2 ^ 4 : ℝ)⁻¹ * K⁻¹ * H.card) ≤ 16 ^ (Fintype.card I + 2) * (J₀.card : ℝ) ∧
        ∃ (r : ℕ) (R : Fin r → ℕ) (Φ : (Fin r → ℤ) →+ (Option I → ℤ)),
          (r : ℝ) ≤ 2 + quarticBogolyubovConstant * (z + 1) ^ 4 ∧
          ((∏ i, (2 * R i + 1) : ℕ) : ℝ) ≤
            2 * ((2 ^ 14 : ℝ) * K ^ 6 * 16 ^ (Fintype.card I + 1)) ^ 16 * H.card ∧
          (let k := (2 ^ r * ∏ i, (2 * R i + 1)) / J₀.card + 1
           let reduce := FreimanModel.variableIntegerGraphReduction N M
           let η := (AddMonoidHom.fst (ZMod N) (∀ i, ZMod (M i))).comp (reduce.comp Φ)
           ∃ J ⊆ J₀, J.Nonempty ∧ J₀.card ≤ (4 * k) ^ r * J.card ∧
             Real.exp (-properAffineRecoveryLogLoss P (Fintype.card I)) * H.card ≤ (J.card : ℝ) ∧
             (k : ℝ) ≤ Real.exp (properAffineScaleLog P (Fintype.card I)) ∧
             ∃ base : Option I → ℤ,
               Set.InjOn η (centeredIntegerBox (fun i => R i / (2 * k)) : Set _) ∧
               (let ψ := (AddMonoidHom.snd (ZMod N) (∀ i, ZMod (M i))).comp (reduce.comp Φ)
                let α := variableCoefficientLift l (reduce base).2
                let β := fun j => variableCoefficientLift l (ψ (Pi.single j 1))
                (∀ i, α i ∈ Set.Ico (0 : ℝ) (1 / l i)) ∧
                (∀ j i, β j i ∈ Set.Ico (0 : ℝ) (1 / l i)) ∧
                ∀ h ∈ J, ∃ x : Fin r → ℤ,
                  (∀ i, |x i| ≤ (R i / (2 * k) : ℕ)) ∧
                  h = (reduce base).1 + η x ∧
                  FreimanModel.variableIntegerGraphLift N M
                    (h, variableRoundedCoefficient M l (a h)) = base + Φ x ∧
                  ∃ q ∈ coordinateDenominatorGrid l, ∀ i,
                    |a h i - (α + ∑ j, (x j : ℝ) • β j) i - q i| ≤ 2 * ε i)) := by
  intro K z δ
  obtain ⟨M, hM, hMsmall, hMerror⟩ := exists_coordinate_rounding_moduli l hl ε hε hsmall
  let _ : ∀ i, NeZero (M i) := fun i => ⟨(hM i).ne'⟩
  obtain ⟨J₀, hJ₀H, hJ₀, hsize, r, R, Φ, hrank, hvolume,
      J, hJJ₀, hJ, hretain, base, hproper, hrepr⟩ :=
    D.proper_integer_graph_affine_model a c M l ε hMsmall hnear
  have hcost := properAffineSelection_bounds hP (Fintype.card I) r
    (∏ i, (2 * R i + 1)) H.card J₀.card J.card hJ₀.card_pos hrank hvolume
    (exp_neg_affineRecoveryLogLoss_card_le P (Fintype.card I) H.card J₀.card hsize) hretain
  refine ⟨M, hM, hMsmall, hMerror, J₀, hJ₀H, hJ₀, hsize, r, R, Φ, hrank, hvolume,
    J, hJJ₀, hJ, hretain, hcost.2, hcost.1, base, hproper, ?_⟩
  dsimp only
  refine ⟨variableCoefficientLift_mem_Ico l hl _, ?_, ?_⟩
  · intro j
    exact variableCoefficientLift_mem_Ico l hl _
  · intro h hh
    obtain ⟨x, hx, heq⟩ := hrepr h hh
    let reduce := FreimanModel.variableIntegerGraphReduction N M
    have hred : (h, variableRoundedCoefficient M l (a h)) =
        reduce base + reduce (Φ x) := by
      have hr := congrArg reduce heq
      simpa only [reduce, FreimanModel.variableIntegerGraphReduction_lift, map_add] using hr
    refine ⟨x, hx, congrArg Prod.fst hred, heq, ?_⟩
    obtain ⟨q, hq, herr⟩ := exists_variable_unrounded_affine l hl (reduce base).2
      ((AddMonoidHom.snd (ZMod N) (∀ i, ZMod (M i))).comp (reduce.comp Φ)) x (a h)
      (congrArg Prod.snd hred)
    exact ⟨q, hq, fun i => (herr i).trans (hMerror i)⟩

end Erdos3.NativeRankRelation.CommonData

end

end OAI
