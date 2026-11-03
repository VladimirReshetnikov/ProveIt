import DiophantineConsistency.ModelRelationCombining

/-! # Jones's combined conditions in every model of `𝗜𝚺₁`

For the free-quantity record `NinePolynomial.RingVars` over a discretely
ordered commutative ring with square divisibility, Jones's four conditions
(two Pell squares, one divisibility, one positive margin; `Jones1982.Nine.Vars.Conds`
over ℤ) hold iff the closed two-radicand combiner vanishes at a nonnegative
witness. This is the internal counterpart of `Jones1982.Nine.conds_iff_value`;
the divisor `(J·F)²` is nonzero by the same elementary argument. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.ModelNineConds
open DiscreteOrderedRingFacts NinePolynomial ModelRelationCombining

section Generic
variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Jones's four conditions on the free quantities. -/
def Conds (v : RingVars R) : Prop :=
  IsSquare ((v.P ^ 2 - 1) * v.K ^ 2 + 1) ∧ IsSquare (v.D * v.F * v.I) ∧
    v.J * v.F ∣ v.Q * v.F + v.J * (v.H - v.C) ∧
    0 < v.K ^ 2 * v.G - 4 * (v.C - v.K * v.Y) ^ 2 * v.G - 8 * v.g * v.K ^ 2

variable (hd : Discrete R)
include hd

theorem J_ne_zero (v : RingVars R) : v.J ≠ 0 := by
  intro h
  simp only [RingVars.J] at h
  rcases lt_or_ge v.A 2 with hA | hA
  · have : v.A ≤ 1 := le_of_lt_add_one hd (by linarith)
    linarith
  · linarith

theorem five_not_dvd_unit (e : R) (he : e = 1 ∨ e = -1) : ¬ (5 : R) ∣ e := by
  rintro ⟨k, hk⟩
  have hk0 : k ≠ 0 := by rintro rfl; rcases he with h | h <;> simp_all
  have h1 : 1 ≤ |k| := abs_ge_one hd hk0
  have habs : |e| = 5 * |k| := by rw [hk, abs_mul, abs_of_pos (by norm_num : (0 : R) < 5)]
  have he1 : |e| = 1 := by rcases he with h | h <;> simp [h]
  linarith

theorem F_ne_zero (v : RingVars R) : v.F ≠ 0 := by
  intro h0
  simp only [RingVars.F] at h0
  have hE : v.E * (-((v.A ^ 2 - 1) * v.E)) = 1 := by linear_combination -h0
  have hE1 := eq_one_or_neg_one_of_mul_eq_one hd hE
  have hEsq : v.E ^ 2 = 1 := by rcases hE1 with h | h <;> simp [h]
  have hA : v.A ^ 2 = 0 := by
    have : (v.A ^ 2 - 1) * v.E ^ 2 + 1 = 0 := h0
    rw [hEsq] at this; linarith
  have hA0 : v.A = 0 := (pow_eq_zero_iff two_ne_zero).mp hA
  apply five_not_dvd_unit hd v.E hE1
  refine ⟨-(v.i * v.D * v.C ^ 2), ?_⟩
  simp only [RingVars.E, RingVars.J, hA0]
  ring

theorem JF_ne_zero (v : RingVars R) : v.J * v.F ≠ 0 :=
  mul_ne_zero (J_ne_zero hd v) (F_ne_zero hd v)

variable (hsq : ∀ m s : R, m ≠ 0 → m ^ 2 ∣ s ^ 2 → m ∣ s)
include hsq

theorem sq_dvd_sq_iff (m s : R) (hm : m ≠ 0) : m ^ 2 ∣ s ^ 2 ↔ m ∣ s :=
  ⟨hsq m s hm, fun h => pow_dvd_pow_of_dvd h 2⟩

/-- Internal counterpart of `Jones1982.Nine.conds_iff_value`. -/
theorem conds_iff_value (v : RingVars R) :
    Conds v ↔ ∃ n : R, 0 ≤ n ∧
      RefinedPair.value (v.rad 0) (v.rad 1) (v.wt 0) (v.wt 1) n v.dvsr v.dvnd v.marg = 0 := by
  have hJF := JF_ne_zero hd v
  have hB : 0 < v.dvsr := by
    simp only [RingVars.dvsr]
    exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hJF))
  have hC : 0 ≤ v.dvnd := by simp only [RingVars.dvnd]; exact sq_nonneg _
  have key := conditions_iff_value hd hsq (v.rad 0) (v.rad 1) v.dvsr v.dvnd v.marg hB hC
  have hw0 : v.wt 0 = v.rad 0 ^ 2 + 2 := rfl
  have hw1 : v.wt 1 = v.rad 1 ^ 2 + 2 := rfl
  rw [hw0, hw1, ← key]
  have hr0 : v.rad 0 = (v.P ^ 2 - 1) * v.K ^ 2 + 1 := rfl
  have hr1 : v.rad 1 = v.D * v.F * v.I := rfl
  have hdiv : v.dvsr ∣ v.dvnd ↔ v.J * v.F ∣ v.Q * v.F + v.J * (v.H - v.C) := by
    simp only [RingVars.dvsr, RingVars.dvnd]
    exact sq_dvd_sq_iff hd hsq _ _ hJF
  rw [hr0, hr1, hdiv]
  rfl

end Generic

section Model
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ModelDifferenceRing ModelArithmetic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- **Jones's conditions in every model**: they hold iff the combiner
vanishes at some model natural. -/
theorem model_conds_iff_value (v : RingVars (DiffRing V)) :
    Conds v ↔ ∃ n : V,
      RefinedPair.value (v.rad 0) (v.rad 1) (v.wt 0) (v.wt 1) (ι n) v.dvsr v.dvnd v.marg = 0 := by
  rw [conds_iff_value model_discrete sq_dvd_sq v]
  constructor
  · rintro ⟨n, hn, hz⟩
    obtain ⟨a, rfl⟩ := nonneg_iff.mp hn
    exact ⟨a, hz⟩
  · rintro ⟨a, hz⟩
    exact ⟨ι a, ι_nonneg a, hz⟩

end Model

end DiophantineConsistency.ModelNineConds
