/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.GowersWeightedDerivative

namespace OAI

section

open scoped BigOperators

namespace Erdos3

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

@[simp] theorem cubeShift_false {j : ℕ} (hs : Fin j → A) :
    cubeShift hs (fun _ ↦ false) = 0 := by simp [cubeShift]

def cubeAxis {j : ℕ} (i : Fin j) : Fin j → Bool := fun k ↦ decide (k = i)

@[simp] theorem cubeShift_axis {j : ℕ} (hs : Fin j → A) (i : Fin j) :
    cubeShift hs (cubeAxis i) = hs i := by simp [cubeShift, cubeAxis]

theorem map_cubeShift (φ : A →+ B) {j : ℕ} (hs : Fin j → A) (ω : Fin j → Bool) :
    φ (cubeShift hs ω) = cubeShift (fun i ↦ φ (hs i)) ω := by
  simp only [cubeShift, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  split_ifs <;> simp

def ReflectsPairSums (φ : A →+ B) (Q : Set A) : Prop :=
  ∀ a ∈ Q, ∀ b ∈ Q, ∀ c ∈ Q, ∀ d ∈ Q,
    φ a + φ b = φ c + φ d → a + b = c + d

theorem ReflectsPairSums.injOn {φ : A →+ B} {Q : Set A}
    (hφ : ReflectsPairSums φ Q) : Set.InjOn φ Q := by
  intro a ha b hb he
  exact add_right_cancel (hφ a ha a ha b hb a ha (by rw [he]))

abbrev SupportedCube (j : ℕ) (Q : Set A) :=
  {p : (Fin j → A) × A // ∀ ω : Fin j → Bool, p.2 + cubeShift p.1 ω ∈ Q}

theorem SupportedCube.base_mem {j : ℕ} {Q : Set A} (p : SupportedCube j Q) : p.val.2 ∈ Q := by
  simpa using p.property (fun _ ↦ false)

theorem SupportedCube.axis_mem {j : ℕ} {Q : Set A} (p : SupportedCube j Q) (i : Fin j) :
    p.val.2 + p.val.1 i ∈ Q := by
  simpa using p.property (cubeAxis i)

def SupportedCube.map (φ : A →+ B) {j : ℕ} {Q : Set A} (p : SupportedCube j Q) :
    SupportedCube j (φ '' Q) :=
  ⟨(fun i ↦ φ (p.val.1 i), φ p.val.2), fun ω ↦
    ⟨p.val.2 + cubeShift p.val.1 ω, p.property ω, by rw [map_add, map_cubeShift]⟩⟩

theorem SupportedCube.map_injective {φ : A →+ B} {Q : Set A}
    (hφ : Set.InjOn φ Q) (j : ℕ) :
    Function.Injective (SupportedCube.map φ : SupportedCube j Q → _) := by
  intro p q he
  have hb : φ p.val.2 = φ q.val.2 := congrArg (fun r ↦ r.val.2) he
  have hx : p.val.2 = q.val.2 := hφ p.base_mem q.base_mem hb
  have hh (i : Fin j) : φ (p.val.1 i) = φ (q.val.1 i) :=
    congrArg (fun r ↦ r.val.1 i) he
  have hi (i : Fin j) : p.val.1 i = q.val.1 i := by
    have hv := hφ (p.axis_mem i) (q.axis_mem i) (by simp only [map_add, hb, hh])
    rw [hx] at hv
    exact add_left_cancel hv
  apply Subtype.ext
  exact Prod.ext (funext hi) hx

theorem exists_lift_cube {φ : A →+ B} {Q : Set A} (hφ : ReflectsPairSums φ Q)
    (j : ℕ) (x : B) (hs : Fin j → B)
    (hQ : ∀ ω : Fin j → Bool, x + cubeShift hs ω ∈ φ '' Q) :
    ∃ a : A, ∃ ds : Fin j → A,
      (∀ ω : Fin j → Bool, a + cubeShift ds ω ∈ Q) ∧ φ a = x ∧ ∀ i, φ (ds i) = hs i := by
  induction j generalizing x with
  | zero =>
    obtain ⟨a, ha, he⟩ := hQ (fun _ ↦ false)
    refine ⟨a, (fun i ↦ Fin.elim0 i), ?_, ?_, fun i ↦ Fin.elim0 i⟩
    · intro ω
      simpa [cubeShift] using ha
    · simpa using he
  | succ j ih =>
    have hface : ∀ ω : Fin j → Bool, x + cubeShift (Fin.tail hs) ω ∈ φ '' Q := by
      intro ω
      have hv := hQ (Fin.cons false ω)
      rw [← Fin.cons_self_tail hs, cubeShift_cons_false] at hv
      exact hv
    obtain ⟨a, ds, hds, ha, hmap⟩ := ih x (Fin.tail hs) hface
    obtain ⟨b, hb, hbmap⟩ := hQ (Fin.cons true (fun _ ↦ false))
    rw [← Fin.cons_self_tail hs, cubeShift_cons_true, cubeShift_false, add_zero] at hbmap
    have hamem : a ∈ Q := by simpa using hds (fun _ ↦ false)
    have hdmap : φ (b - a) = hs 0 := by rw [map_sub, hbmap, ha]; abel
    refine ⟨a, Fin.cons (b - a) ds, ?_, ha, ?_⟩
    · intro ω
      rw [← Fin.cons_self_tail ω]
      cases hω : ω 0 with
      | false => simpa only [cubeShift_cons_false] using hds (Fin.tail ω)
      | true =>
        rw [cubeShift_cons_true]
        obtain ⟨c, hc, hcmap⟩ := hQ (Fin.cons true (Fin.tail ω))
        rw [← Fin.cons_self_tail hs, cubeShift_cons_true] at hcmap
        have hpair : (a + cubeShift ds (Fin.tail ω)) + b = c + a := by
          apply hφ _ (hds (Fin.tail ω)) b hb c hc a hamem
          simp only [map_add, map_cubeShift, hmap, hbmap, hcmap, ha]
          abel
        have he : a + (b - a + cubeShift ds (Fin.tail ω)) = c := by
          apply add_right_cancel (b := a)
          calc
            (a + (b - a + cubeShift ds (Fin.tail ω))) + a =
                (a + cubeShift ds (Fin.tail ω)) + b := by abel
            _ = c + a := hpair
        rwa [he]
    · intro i
      refine Fin.cases ?_ (fun k ↦ ?_) i
      · exact hdmap
      · exact hmap k

theorem SupportedCube.map_surjective {φ : A →+ B} {Q : Set A}
    (hφ : ReflectsPairSums φ Q) (j : ℕ) :
    Function.Surjective (SupportedCube.map φ : SupportedCube j Q → _) := by
  intro p
  obtain ⟨a, ds, hds, ha, hmap⟩ := exists_lift_cube hφ j p.val.2 p.val.1 p.property
  refine ⟨⟨(ds, a), hds⟩, ?_⟩
  apply Subtype.ext
  exact Prod.ext (funext hmap) ha

noncomputable def supportedCubeEquiv {φ : A →+ B} {Q : Set A}
    (hφ : ReflectsPairSums φ Q) (j : ℕ) : SupportedCube j Q ≃ SupportedCube j (φ '' Q) :=
  Equiv.ofBijective (SupportedCube.map φ) ⟨SupportedCube.map_injective hφ.injOn j,
    SupportedCube.map_surjective hφ j⟩

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {A : Type*} [AddCommGroup A]

def SupportedCube.points {j : ℕ} {Q : Set A} (p : SupportedCube j Q) : Q × (Fin j → Q) :=
  (⟨p.val.2, p.base_mem⟩, fun i ↦ ⟨p.val.2 + p.val.1 i, p.axis_mem i⟩)

theorem SupportedCube.points_injective (j : ℕ) (Q : Set A) :
    Function.Injective (SupportedCube.points : SupportedCube j Q → _) := by
  intro p q he
  have hx : p.val.2 = q.val.2 := congrArg (fun r ↦ r.1.val) he
  have hd (i : Fin j) : p.val.1 i = q.val.1 i := by
    have hi : p.val.2 + p.val.1 i = q.val.2 + q.val.1 i :=
      congrArg (fun r ↦ (r.2 i).val) he
    rw [hx] at hi
    exact add_left_cancel hi
  apply Subtype.ext
  exact Prod.ext (funext hd) hx

instance supportedCubeFinite (j : ℕ) (Q : Set A) [Finite Q] : Finite (SupportedCube j Q) :=
  Finite.of_injective SupportedCube.points (SupportedCube.points_injective j Q)

noncomputable instance supportedCubeFintype (j : ℕ) (Q : Set A) [Finite Q] :
    Fintype (SupportedCube j Q) := Fintype.ofFinite _

noncomputable def supportedCubeSum (j : ℕ) (Q : Set A) [Finite Q]
    (F : (Fin j → Bool) → A → ℂ) : ℂ :=
  ∑ p : SupportedCube j Q, mixedCubeProduct F p.val.1 p.val.2

section FiniteAmbient

variable [Fintype A] [DecidableEq A]

noncomputable def supportedCubeFinsetEquiv (j : ℕ) (Q : Finset A) :
    SupportedCube j (Q : Set A) ≃ (groupCubeSet j Q) :=
  Equiv.subtypeEquivRight (fun p ↦ by simp [groupCubeSet])

theorem card_supportedCube (j : ℕ) (Q : Finset A) :
    Nat.card (SupportedCube j (Q : Set A)) = groupCubeCount j Q := by
  rw [Nat.card_congr (supportedCubeFinsetEquiv j Q), Nat.card_eq_fintype_card]
  exact Fintype.card_coe _

theorem supportedCubeSum_eq_sum (j : ℕ) (Q : Finset A) (F : (Fin j → Bool) → A → ℂ) :
    supportedCubeSum j (Q : Set A) F =
      ∑ p ∈ groupCubeSet j Q, mixedCubeProduct F p.1 p.2 := by
  exact (Finset.sum_subtype (groupCubeSet j Q) (fun p ↦ by simp [groupCubeSet])
    (fun p ↦ mixedCubeProduct F p.1 p.2)).symm

omit [Fintype A] in
theorem mixedCubeProduct_restrictTo {j : ℕ} (Q : Finset A)
    (F : (Fin j → Bool) → A → ℂ) (hs : Fin j → A) (x : A) :
    mixedCubeProduct (fun ω ↦ restrictTo Q (F ω)) hs x =
      if ∀ ω : Fin j → Bool, x + cubeShift hs ω ∈ Q then mixedCubeProduct F hs x else 0 := by
  classical
  by_cases hall : ∀ ω : Fin j → Bool, x + cubeShift hs ω ∈ Q
  · rw [ite_eq_left hall]
    unfold mixedCubeProduct
    apply Finset.prod_congr rfl
    intro ω hω
    simp only [restrictTo, ite_eq_left (hall ω)]
  · rw [ite_eq_right hall]
    obtain ⟨ω, hω⟩ := not_forall.mp hall
    unfold mixedCubeProduct
    apply Finset.prod_eq_zero (Finset.mem_univ ω)
    simp only [restrictTo, ite_eq_right hω, map_zero]

theorem mixedGowersMoment_restrict_eq_supportedCubeSum (j : ℕ) (Q : Finset A)
    (F : (Fin j → Bool) → A → ℂ) :
    mixedGowersMoment j (fun ω ↦ restrictTo Q (F ω)) =
      supportedCubeSum j (Q : Set A) F / (Fintype.card A : ℂ) ^ (j + 1) := by
  classical
  rw [mixedGowersMoment_eq_expect_cube]
  simp_rw [mixedCubeProduct_restrictTo]
  rw [← Finset.expect_product', Finset.univ_product_univ,
    Fintype.expect_eq_sum_div_card, supportedCubeSum_eq_sum]
  have hc : (Fintype.card ((Fin j → A) × A) : ℂ) = (Fintype.card A : ℂ) ^ (j + 1) := by
    simp [pow_succ]
  rw [hc]
  congr 1
  simp [groupCubeSet, Finset.sum_filter]

end FiniteAmbient

variable [DecidableEq A]

theorem supportedCubeSum_eq_tsum (j : ℕ) (Q : Finset A) (F : (Fin j → Bool) → A → ℂ) :
    supportedCubeSum j (Q : Set A) F =
      ∑' p : (Fin j → A) × A, mixedCubeProduct (fun ω ↦ restrictTo Q (F ω)) p.1 p.2 := by
  classical
  unfold supportedCubeSum
  rw [← tsum_fintype (L := SummationFilter.unconditional _)]
  change (∑' b : {p : (Fin j → A) × A // ∀ ω : Fin j → Bool, p.2 + cubeShift p.1 ω ∈ Q},
    mixedCubeProduct F b.val.1 b.val.2) = _
  calc
    _ = ∑' p : (Fin j → A) × A,
        if ∀ ω : Fin j → Bool, p.2 + cubeShift p.1 ω ∈ Q then
          mixedCubeProduct F p.1 p.2 else 0 := by
      convert! (tsum_subtype
        {p : (Fin j → A) × A | ∀ ω : Fin j → Bool, p.2 + cubeShift p.1 ω ∈ Q}
        (fun p ↦ mixedCubeProduct F p.1 p.2)) using 1
      simp only [Set.indicator_apply, Set.mem_ofPred_eq]
    _ = _ := tsum_congr (fun p ↦ (mixedCubeProduct_restrictTo Q F p.1 p.2).symm)

omit [DecidableEq A] in
theorem card_supportedCube_le (j : ℕ) (Q : Finset A) :
    Nat.card (SupportedCube j (Q : Set A)) ≤ Q.card ^ (j + 1) := by
  have h := Nat.card_le_card_of_injective SupportedCube.points
    (SupportedCube.points_injective j (Q : Set A))
  simpa [Nat.card_eq_fintype_card, pow_succ, mul_comm] using h

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

noncomputable def imageExtension (φ : A →+ B) (Q : Finset A) (f : A → ℂ) : B → ℂ := by
  classical
  exact fun y ↦ ∑ a ∈ Q, if φ a = y then f a else 0

theorem imageExtension_apply {φ : A →+ B} {Q : Finset A} (hi : Set.InjOn φ (Q : Set A))
    (f : A → ℂ) {a : A} (ha : a ∈ Q) : imageExtension φ Q f (φ a) = f a := by
  classical
  unfold imageExtension
  rw [Finset.sum_eq_single a]
  · simp
  · intro b hb hba
    exact ite_eq_right (fun he ↦ hba (hi hb ha he))
  · intro hna
    exact (hna ha).elim

theorem imageExtension_eq_zero {φ : A →+ B} {Q : Finset A} (f : A → ℂ) {y : B}
    (hy : y ∉ φ '' (Q : Set A)) : imageExtension φ Q f y = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro a ha
  exact ite_eq_right (fun he ↦ hy ⟨a, ha, he⟩)

theorem mixedCubeProduct_imageExtension {φ : A →+ B} {Q : Finset A}
    (hi : Set.InjOn φ (Q : Set A)) {j : ℕ} (F : (Fin j → Bool) → A → ℂ)
    (p : SupportedCube j (Q : Set A)) :
    mixedCubeProduct (fun ω ↦ imageExtension φ Q (F ω))
      (fun i ↦ φ (p.val.1 i)) (φ p.val.2) = mixedCubeProduct F p.val.1 p.val.2 := by
  unfold mixedCubeProduct
  apply Finset.prod_congr rfl
  intro ω hω
  rw [← map_cubeShift, ← map_add]
  exact congrArg (conjugationPower (booleanWeight ω))
    (imageExtension_apply hi (F ω) (p.property ω))

variable [Fintype B] [DecidableEq B]

omit [Fintype B] in
theorem restrictTo_imageExtension (φ : A →+ B) (Q : Finset A) (f : A → ℂ) :
    restrictTo (Q.image φ) (imageExtension φ Q f) = imageExtension φ Q f := by
  classical
  funext y
  by_cases hy : y ∈ Q.image φ
  · simp only [restrictTo, ite_eq_left hy]
  · rw [restrictTo, ite_eq_right hy]
    exact (imageExtension_eq_zero f (by
      rintro ⟨a, ha, he⟩
      exact hy (Finset.mem_image.mpr ⟨a, ha, he⟩))).symm

omit [Fintype B] [DecidableEq B] in
theorem supportedCubeSum_imageExtension {φ : A →+ B} {Q : Finset A}
    (hφ : ReflectsPairSums φ (Q : Set A)) (j : ℕ) (F : (Fin j → Bool) → A → ℂ) :
    supportedCubeSum j (φ '' (Q : Set A)) (fun ω ↦ imageExtension φ Q (F ω)) =
      supportedCubeSum j (Q : Set A) F := by
  classical
  symm
  apply Fintype.sum_equiv (supportedCubeEquiv hφ j)
  intro p
  exact (mixedCubeProduct_imageExtension hφ.injOn F p).symm

theorem mixedGowersMoment_imageExtension {φ : A →+ B} {Q : Finset A}
    (hφ : ReflectsPairSums φ (Q : Set A)) (j : ℕ) (F : (Fin j → Bool) → A → ℂ) :
    mixedGowersMoment j (fun ω ↦ imageExtension φ Q (F ω)) =
      supportedCubeSum j (Q : Set A) F / (Fintype.card B : ℂ) ^ (j + 1) := by
  classical
  have hr : (fun ω ↦ imageExtension φ Q (F ω)) =
      (fun ω ↦ restrictTo (Q.image φ) (imageExtension φ Q (F ω))) := by
    funext ω
    exact (restrictTo_imageExtension φ Q (F ω)).symm
  rw [hr, mixedGowersMoment_restrict_eq_supportedCubeSum]
  simp only [Finset.coe_image, supportedCubeSum_imageExtension hφ]

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {A : Type*} [AddCommGroup A] [DecidableEq A]

def cubeDifferenceSupport (Q : Finset A) : Finset A :=
  (Q ×ˢ Q).image (fun p ↦ p.2 - p.1)

theorem mem_cubeDifferenceSupport (Q : Finset A) (h : A) :
    h ∈ cubeDifferenceSupport Q ↔ (derivativeSupport Q h).Nonempty := by
  constructor
  · intro hh
    obtain ⟨⟨x, y⟩, hp, rfl⟩ := Finset.mem_image.mp hh
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp hp
    refine ⟨x, Finset.mem_filter.mpr ⟨hx, ?_⟩⟩
    simpa using hy
  · rintro ⟨x, hx⟩
    obtain ⟨hx, hxh⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_image.mpr ⟨(x, x + h), Finset.mem_product.mpr ⟨hx, hxh⟩, by simp⟩

theorem SupportedCube.first_mem_difference {j : ℕ} {Q : Finset A}
    (p : SupportedCube (j + 1) (Q : Set A)) : p.val.1 0 ∈ cubeDifferenceSupport Q :=
  Finset.mem_image.mpr ⟨(p.val.2, p.val.2 + p.val.1 0),
    Finset.mem_product.mpr ⟨p.base_mem, p.axis_mem 0⟩, by simp⟩

def SupportedCube.tail {j : ℕ} {Q : Finset A} (p : SupportedCube (j + 1) (Q : Set A)) :
    SupportedCube j (derivativeSupport Q (p.val.1 0) : Set A) := by
  refine ⟨(Fin.tail p.val.1, p.val.2), ?_⟩
  intro ω
  apply Finset.mem_filter.mpr
  have hfalse := p.property (Fin.cons false ω)
  have htrue := p.property (Fin.cons true ω)
  rw [← Fin.cons_self_tail p.val.1, cubeShift_cons_false] at hfalse
  rw [← Fin.cons_self_tail p.val.1, cubeShift_cons_true] at htrue
  exact ⟨hfalse, by simpa only [Finset.mem_coe, add_assoc, add_left_comm, add_comm] using htrue⟩

def SupportedCube.cons {j : ℕ} {Q : Finset A} (h : A)
    (p : SupportedCube j (derivativeSupport Q h : Set A)) : SupportedCube (j + 1) (Q : Set A) := by
  refine ⟨(Fin.cons h p.val.1, p.val.2), ?_⟩
  intro ω
  obtain ⟨hfalse, htrue⟩ := Finset.mem_filter.mp (p.property (Fin.tail ω))
  rw [← Fin.cons_self_tail ω]
  cases ω 0 with
  | false => simpa only [Finset.mem_coe, cubeShift_cons_false] using hfalse
  | true => simpa only [Finset.mem_coe, cubeShift_cons_true, add_assoc, add_left_comm, add_comm] using htrue

def supportedCubeDerivativeEquiv (j : ℕ) (Q : Finset A) :
    SupportedCube (j + 1) (Q : Set A) ≃
      Σ h : cubeDifferenceSupport Q, SupportedCube j (derivativeSupport Q h.val : Set A) where
  toFun p := ⟨⟨p.val.1 0, p.first_mem_difference⟩, p.tail⟩
  invFun p := p.2.cons p.1.val
  left_inv p := by
    apply Subtype.ext
    change (Fin.cons (p.val.1 0) (Fin.tail p.val.1), p.val.2) = p.val
    rw [Fin.cons_self_tail]
  right_inv p := by
    rcases p with ⟨h, p⟩
    rfl

theorem card_supportedCube_succ (j : ℕ) (Q : Finset A) :
    Nat.card (SupportedCube (j + 1) (Q : Set A)) =
      ∑ h ∈ cubeDifferenceSupport Q, Nat.card (SupportedCube j (derivativeSupport Q h : Set A)) := by
  rw [Nat.card_congr (supportedCubeDerivativeEquiv j Q)]
  simp only [Nat.card_eq_fintype_card, Fintype.card_sigma]
  exact Finset.sum_coe_sort (cubeDifferenceSupport Q)
    (fun h ↦ Fintype.card (SupportedCube j (derivativeSupport Q h : Set A)))

theorem supportedCubeSum_derivative (j : ℕ) (Q : Finset A)
    (F : (Fin (j + 1) → Bool) → A → ℂ) :
    supportedCubeSum (j + 1) (Q : Set A) F =
      ∑ h ∈ cubeDifferenceSupport Q, supportedCubeSum j (derivativeSupport Q h : Set A)
        (fun ω ↦ crossDerivative (F (Fin.cons false ω)) (F (Fin.cons true ω)) h) := by
  let he := (supportedCubeDerivativeEquiv j Q).symm
  calc
    _ = ∑ p : Σ h : cubeDifferenceSupport Q,
        SupportedCube j (derivativeSupport Q h.val : Set A),
        mixedCubeProduct F (Fin.cons p.1.val p.2.val.1) p.2.val.2 := by
      symm
      apply Fintype.sum_equiv he
      intro p
      rfl
    _ = _ := by
      simp only [Fintype.sum_sigma, mixedCubeProduct_cons,
        ← mixedCubeProduct_crossDerivative, supportedCubeSum]
      exact Finset.sum_coe_sort (cubeDifferenceSupport Q)
        (fun h ↦ supportedCubeSum j (derivativeSupport Q h : Set A)
          (fun ω ↦ crossDerivative (F (Fin.cons false ω)) (F (Fin.cons true ω)) h))

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

noncomputable def finiteSupportGowersNorm (j : ℕ) (Q : Finset A) (f : A → ℂ) : ℝ :=
  ((supportedCubeSum j (Q : Set A) (fun _ ↦ f)).re /
    Nat.card (SupportedCube j (Q : Set A))) ^ (((2 ^ j : ℕ) : ℝ)⁻¹)

theorem supportedCubeSum_one (j : ℕ) (Q : Finset A) :
    supportedCubeSum j (Q : Set A) (fun _ _ ↦ 1) =
      (Nat.card (SupportedCube j (Q : Set A)) : ℂ) := by
  classical
  simp [supportedCubeSum, mixedCubeProduct, Nat.card_eq_fintype_card]

theorem finiteSupportGowersNorm_one (j : ℕ) {Q : Finset A} (hQ : Q.Nonempty) :
    finiteSupportGowersNorm j Q (fun _ ↦ 1) = 1 := by
  classical
  obtain ⟨a, ha⟩ := hQ
  let : Nonempty (SupportedCube j (Q : Set A)) :=
    ⟨⟨((fun _ ↦ 0), a), fun ω ↦ by simpa [cubeShift] using ha⟩⟩
  have hcard : (Nat.card (SupportedCube j (Q : Set A)) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  simp only [finiteSupportGowersNorm, supportedCubeSum_one, Complex.natCast_re,
    div_self hcard, Real.one_rpow]

theorem imageExtension_add (φ : A →+ B) (Q : Finset A) (f g : A → ℂ) :
    imageExtension φ Q (fun x ↦ f x + g x) =
      (fun y ↦ imageExtension φ Q f y + imageExtension φ Q g y) := by
  classical
  funext y
  simp only [imageExtension, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  split_ifs <;> simp

variable [Fintype B] [DecidableEq B]

theorem card_supportedCube_image {φ : A →+ B} {Q : Finset A}
    (hφ : ReflectsPairSums φ (Q : Set A)) (j : ℕ) :
    Nat.card (SupportedCube j (Q : Set A)) = groupCubeCount j (Q.image φ) := by
  classical
  rw [Nat.card_congr (supportedCubeEquiv hφ j)]
  simpa only [Finset.coe_image] using card_supportedCube j (Q.image φ)

theorem gowersMoment_imageExtension_re {φ : A →+ B} {Q : Finset A}
    (hφ : ReflectsPairSums φ (Q : Set A)) (j : ℕ) (f : A → ℂ) :
    (gowersMoment j (imageExtension φ Q f)).re =
      (supportedCubeSum j (Q : Set A) (fun _ ↦ f)).re /
        (Fintype.card B : ℝ) ^ (j + 1) := by
  have hm := congrArg Complex.re (mixedGowersMoment_imageExtension hφ j (fun _ ↦ f))
  simpa only [mixedGowersMoment_const, ← Nat.cast_pow, Complex.div_natCast_re] using hm

theorem restrictedGowersNorm_imageExtension_pow {φ : A →+ B} {Q : Finset A}
    (hφ : ReflectsPairSums φ (Q : Set A)) (j : ℕ) (f : A → ℂ) :
    restrictedGowersNorm (j + 1) (Q.image φ) (imageExtension φ Q f) ^ (2 ^ (j + 1)) =
      (supportedCubeSum (j + 1) (Q : Set A) (fun _ ↦ f)).re /
        Nat.card (SupportedCube (j + 1) (Q : Set A)) := by
  simp only [restrictedGowersNorm, div_pow, gowersNorm_pow,
    restrictTo_imageExtension, gowersMoment_imageExtension_re hφ, gowersMoment_indicator_re]
  rw [← card_supportedCube_image hφ]
  exact div_div_div_cancel_right₀
    (pow_ne_zero _ (by exact_mod_cast Fintype.card_ne_zero : (Fintype.card B : ℝ) ≠ 0)) _ _

theorem finiteSupportGowersNorm_eq_restricted {φ : A →+ B} {Q : Finset A}
    (hφ : ReflectsPairSums φ (Q : Set A)) (j : ℕ) (f : A → ℂ) :
    finiteSupportGowersNorm (j + 1) Q f =
      restrictedGowersNorm (j + 1) (Q.image φ) (imageExtension φ Q f) := by
  unfold finiteSupportGowersNorm
  rw [← restrictedGowersNorm_imageExtension_pow hφ]
  exact Real.pow_rpow_inv_natCast (restrictedGowersNorm_nonneg j _ _)
    (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0))

theorem finiteSupportGowersNorm_add_of_embedding {φ : A →+ B} {Q : Finset A}
    (hφ : ReflectsPairSums φ (Q : Set A)) (j : ℕ) (f g : A → ℂ) :
    finiteSupportGowersNorm (j + 1) Q (fun x ↦ f x + g x) ≤
      finiteSupportGowersNorm (j + 1) Q f + finiteSupportGowersNorm (j + 1) Q g := by
  simp only [finiteSupportGowersNorm_eq_restricted hφ, imageExtension_add]
  exact restrictedGowersNorm_add j _ _ _

theorem norm_supportedCubeSum_le_of_embedding {φ : A →+ B} {Q : Finset A}
    (hφ : ReflectsPairSums φ (Q : Set A)) (j : ℕ) (F : (Fin (j + 1) → Bool) → A → ℂ) :
    ‖supportedCubeSum (j + 1) (Q : Set A) F‖ /
        Nat.card (SupportedCube (j + 1) (Q : Set A)) ≤
      ∏ ω, finiteSupportGowersNorm (j + 1) Q (F ω) := by
  have h := norm_mixedGowersMoment_restrict_le j (Q.image φ)
    (fun ω ↦ imageExtension φ Q (F ω))
  simp only [restrictTo_imageExtension, mixedGowersMoment_imageExtension hφ,
    norm_div, norm_pow, Complex.norm_natCast, gowersMoment_indicator_re,
    ← card_supportedCube_image hφ, ← finiteSupportGowersNorm_eq_restricted hφ] at h
  rwa [div_div_div_cancel_right₀
    (pow_ne_zero _ (by exact_mod_cast Fintype.card_ne_zero : (Fintype.card B : ℝ) ≠ 0))] at h

theorem finiteSupportGowersNorm_ambient_comparison {φ : A →+ B} {Q : Finset A}
    (hφ : ReflectsPairSums φ (Q : Set A)) (j : ℕ) (f : A → ℂ) :
    gowersNorm (j + 1) (imageExtension φ Q f) ^ (2 ^ (j + 1)) =
      ((Nat.card (SupportedCube (j + 1) (Q : Set A)) : ℝ) /
        (Fintype.card B : ℝ) ^ (j + 2)) * finiteSupportGowersNorm (j + 1) Q f ^ (2 ^ (j + 1)) := by
  have h := gowersNorm_restrict_cubeCount j (Q.image φ) (imageExtension φ Q f)
  simpa only [restrictTo_imageExtension, ← card_supportedCube_image hφ,
    ← finiteSupportGowersNorm_eq_restricted hφ] using h

theorem finiteSupportGowersNorm_degree_one_of_embedding {φ : A →+ B} {Q : Finset A}
    (hφ : ReflectsPairSums φ (Q : Set A)) (hQ : Q.Nonempty) (f : A → ℂ) :
    finiteSupportGowersNorm 1 Q f = ‖𝔼 x ∈ Q, f x‖ := by
  classical
  rw [finiteSupportGowersNorm_eq_restricted hφ 0,
    restrictedGowersNorm_degree_one (hQ.image φ)]
  simp only [Finset.expect_eq_sum_div_card]
  rw [Finset.card_image_of_injOn hφ.injOn, Finset.sum_image]
  · congr 2
    apply Finset.sum_congr rfl
    intro x hx
    exact imageExtension_apply hφ.injOn f hx
  · exact hφ.injOn

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

theorem ReflectsPairSums.mono {φ : A →+ B} {Q R : Set A}
    (hφ : ReflectsPairSums φ Q) (hRQ : R ⊆ Q) : ReflectsPairSums φ R := by
  intro a ha b hb c hc d hd he
  exact hφ a (hRQ ha) b (hRQ hb) c (hRQ hc) d (hRQ hd) he

theorem card_supportedCube_pos (j : ℕ) {Q : Finset A} (hQ : Q.Nonempty) :
    0 < Nat.card (SupportedCube j (Q : Set A)) := by
  obtain ⟨a, ha⟩ := hQ
  let : Nonempty (SupportedCube j (Q : Set A)) :=
    ⟨⟨((fun _ ↦ 0), a), fun ω ↦ by simpa [cubeShift] using ha⟩⟩
  exact Nat.card_pos

variable [DecidableEq A]

theorem sum_supportedCube_weights (j : ℕ) {Q : Finset A} (hQ : Q.Nonempty) :
    (∑ h ∈ cubeDifferenceSupport Q,
      (Nat.card (SupportedCube j (derivativeSupport Q h : Set A)) : ℝ) /
        Nat.card (SupportedCube (j + 1) (Q : Set A))) = 1 := by
  rw [← Finset.sum_div, ← Nat.cast_sum, ← card_supportedCube_succ]
  exact div_self (by exact_mod_cast (card_supportedCube_pos (j + 1) hQ).ne')

variable [Fintype B] [DecidableEq B]

omit [DecidableEq A] in
theorem finiteSupportGowersNorm_pow_mul_count {φ : A →+ B} {Q : Finset A}
    (hφ : ReflectsPairSums φ (Q : Set A)) (hQ : Q.Nonempty) (j : ℕ) (f : A → ℂ) :
    (Nat.card (SupportedCube (j + 1) (Q : Set A)) : ℝ) *
        finiteSupportGowersNorm (j + 1) Q f ^ (2 ^ (j + 1)) =
      (supportedCubeSum (j + 1) (Q : Set A) (fun _ ↦ f)).re := by
  rw [finiteSupportGowersNorm_eq_restricted hφ, restrictedGowersNorm_imageExtension_pow hφ]
  have hC : (Nat.card (SupportedCube (j + 1) (Q : Set A)) : ℝ) ≠ 0 := by
    exact_mod_cast (card_supportedCube_pos (j + 1) hQ).ne'
  field_simp

theorem finiteSupportGowersNorm_derivative_mul_count {φ : A →+ B} {Q : Finset A}
    (hφ : ReflectsPairSums φ (Q : Set A)) (hQ : Q.Nonempty) (j : ℕ) (f : A → ℂ) :
    (Nat.card (SupportedCube (j + 2) (Q : Set A)) : ℝ) *
        finiteSupportGowersNorm (j + 2) Q f ^ (2 ^ (j + 2)) =
      ∑ h ∈ cubeDifferenceSupport Q,
        (Nat.card (SupportedCube (j + 1) (derivativeSupport Q h : Set A)) : ℝ) *
          finiteSupportGowersNorm (j + 1) (derivativeSupport Q h)
            (multiplicativeDerivative f h) ^ (2 ^ (j + 1)) := by
  rw [finiteSupportGowersNorm_pow_mul_count hφ hQ]
  have he := congrArg Complex.re (supportedCubeSum_derivative (j + 1) Q (fun _ ↦ f))
  simp only [crossDerivative_self, Complex.re_sum] at he
  rw [he]
  apply Finset.sum_congr rfl
  intro h hh
  have hφh : ReflectsPairSums φ (derivativeSupport Q h : Set A) :=
    hφ.mono (fun _ hx ↦ (Finset.mem_filter.mp hx).1)
  exact (finiteSupportGowersNorm_pow_mul_count hφh
    ((mem_cubeDifferenceSupport Q h).mp hh) j (multiplicativeDerivative f h)).symm

theorem finiteSupportGowersNorm_derivative {φ : A →+ B} {Q : Finset A}
    (hφ : ReflectsPairSums φ (Q : Set A)) (hQ : Q.Nonempty) (j : ℕ) (f : A → ℂ) :
    finiteSupportGowersNorm (j + 2) Q f ^ (2 ^ (j + 2)) =
      ∑ h ∈ cubeDifferenceSupport Q,
        ((Nat.card (SupportedCube (j + 1) (derivativeSupport Q h : Set A)) : ℝ) /
          Nat.card (SupportedCube (j + 2) (Q : Set A))) *
          finiteSupportGowersNorm (j + 1) (derivativeSupport Q h)
            (multiplicativeDerivative f h) ^ (2 ^ (j + 1)) := by
  have hC : (Nat.card (SupportedCube (j + 2) (Q : Set A)) : ℝ) ≠ 0 := by
    exact_mod_cast (card_supportedCube_pos (j + 2) hQ).ne'
  calc
    _ = ((Nat.card (SupportedCube (j + 2) (Q : Set A)) : ℝ) *
        finiteSupportGowersNorm (j + 2) Q f ^ (2 ^ (j + 2))) /
          Nat.card (SupportedCube (j + 2) (Q : Set A)) := by field_simp
    _ = _ := by
      rw [finiteSupportGowersNorm_derivative_mul_count hφ hQ, Finset.sum_div]
      simp only [div_mul_eq_mul_div]

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

theorem supportedCubeSum_congr_on (j : ℕ) (Q : Finset A)
    (F G : (Fin j → Bool) → A → ℂ) (h : ∀ ω x, x ∈ Q → F ω x = G ω x) :
    supportedCubeSum j (Q : Set A) F = supportedCubeSum j (Q : Set A) G := by
  unfold supportedCubeSum
  apply Finset.sum_congr rfl
  intro p _
  unfold mixedCubeProduct
  apply Finset.prod_congr rfl
  intro ω _
  rw [h ω _ (p.property ω)]

theorem finiteSupportGowersNorm_congr_on (j : ℕ) (Q : Finset A) (f g : A → ℂ)
    (h : ∀ x ∈ Q, f x = g x) : finiteSupportGowersNorm j Q f = finiteSupportGowersNorm j Q g := by
  unfold finiteSupportGowersNorm
  rw [supportedCubeSum_congr_on j Q (fun _ => f) (fun _ => g) (fun _ => h)]

theorem reflectsPairSums_of_addEquiv (e : A ≃+ B) (Q : Set A) :
    ReflectsPairSums e.toAddMonoidHom Q := by
  intro a ha b hb c hc d hd he
  change e a + e b = e c + e d at he
  apply e.injective
  exact (map_add e a b).trans (he.trans (map_add e c d).symm)

theorem card_supportedCube_image_eq [DecidableEq B] {φ : A →+ B} {Q : Finset A}
    (hφ : ReflectsPairSums φ (Q : Set A)) (j : ℕ) :
    Nat.card (SupportedCube j (Q.image φ : Set B)) = Nat.card (SupportedCube j (Q : Set A)) := by
  simpa only [Finset.coe_image] using (Nat.card_congr (supportedCubeEquiv hφ j)).symm

theorem finiteSupportGowersNorm_imageExtension [DecidableEq B] {φ : A →+ B} {Q : Finset A}
    (hφ : ReflectsPairSums φ (Q : Set A)) (j : ℕ) (f : A → ℂ) :
    finiteSupportGowersNorm j (Q.image φ) (imageExtension φ Q f) = finiteSupportGowersNorm j Q f := by
  unfold finiteSupportGowersNorm
  rw [card_supportedCube_image_eq hφ]
  simp only [Finset.coe_image, supportedCubeSum_imageExtension hφ]

theorem finiteSupportGowersNorm_addEquiv [DecidableEq B] (e : A ≃+ B)
    (j : ℕ) (Q : Finset A) (f : B → ℂ) :
    finiteSupportGowersNorm j (Q.image e) f = finiteSupportGowersNorm j Q (fun x => f (e x)) := by
  have hφ := reflectsPairSums_of_addEquiv e (Q : Set A)
  calc
    _ = finiteSupportGowersNorm j (Q.image e) (imageExtension e.toAddMonoidHom Q (fun x => f (e x))) := by
      apply finiteSupportGowersNorm_congr_on
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      exact (imageExtension_apply hφ.injOn (fun x => f (e x)) hx).symm
    _ = _ := finiteSupportGowersNorm_imageExtension hφ j _

theorem finiteCorrelation_addEquiv [DecidableEq B] (e : A ≃+ B)
    (Q : Finset A) (f g : B → ℂ) :
    finiteCorrelation (Q.image e) f g = finiteCorrelation Q (fun x => f (e x)) (fun x => g (e x)) := by
  unfold finiteCorrelation
  exact Finset.expect_image e.injective.injOn

end Erdos3

end

end OAI
