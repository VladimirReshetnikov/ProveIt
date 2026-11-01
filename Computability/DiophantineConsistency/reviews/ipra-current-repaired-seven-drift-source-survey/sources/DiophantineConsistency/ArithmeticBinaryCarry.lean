import DiophantineConsistency.ArithmeticBinaryPopulation

/-! Internal population subadditivity and the exact no-carry test, at every
internal pair of every model of IΣ1. `NoCarry a b` is the bounded statement that
no binary position carries two ones; population is additive exactly when it holds.
The proofs are genuine internal order inductions over the represented population. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticBinaryCarry
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticBinaryPopulation
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- No binary position of `a` and `b` holds two ones (bounded form). -/
def NoCarry (a b : V) : Prop := ∀ i < a + b + 1, fbit a i + fbit b i ≤ 1

instance noCarry_definable : 𝚺₀-Relation (NoCarry : V → V → Prop) := by
  unfold NoCarry; definability

theorem noCarry_iff (a b : V) : NoCarry a b ↔ ∀ i, fbit a i + fbit b i ≤ 1 := by
  constructor
  · intro h i
    by_cases hi : i < a + b + 1
    · exact h i hi
    · have habi : a + b ≤ i := le_trans le_self_add (not_lt.mp hi)
      have hai : ‖a‖ ≤ i := le_trans (length_le a) (le_trans (le_add_right le_rfl) habi)
      have hbi : ‖b‖ ≤ i := le_trans (length_le b) (le_trans (le_add_left le_rfl) habi)
      rw [fbit_eq_zero_of_le hai, fbit_eq_zero_of_le hbi]
      simp
  · intro h i _; exact h i

theorem fbit_binary_zero (a r : V) (hr : r ≤ 1) : fbit (2*a+r) 0 = r := by
  rcases le_one_iff_eq_zero_or_one.mp hr with rfl | rfl <;>
    simp [fbit_two_mul_zero_eq_zero, fbit_two_mul_add_one_zero_eq_one]

theorem fbit_binary_succ (a r j : V) (hr : r ≤ 1) : fbit (2*a+r) (j+1) = fbit a j := by
  rcases le_one_iff_eq_zero_or_one.mp hr with rfl | rfl <;>
    simp [fbit_mul_two_mul, fbit_mul_two_add_one_mul]

theorem noCarry_binary (a b r s : V) (hr : r ≤ 1) (hs : s ≤ 1) :
    NoCarry (2*a+r) (2*b+s) ↔ r + s ≤ 1 ∧ NoCarry a b := by
  rw [noCarry_iff, noCarry_iff]
  constructor
  · intro h
    refine ⟨by simpa [fbit_binary_zero a r hr, fbit_binary_zero b s hs] using h 0, fun j => ?_⟩
    simpa [fbit_binary_succ a r j hr, fbit_binary_succ b s j hs] using h (j+1)
  · rintro ⟨h0, h⟩ i
    rcases zero_or_succ i with rfl | ⟨j, rfl⟩
    · simpa [fbit_binary_zero a r hr, fbit_binary_zero b s hs] using h0
    · simpa [fbit_binary_succ a r j hr, fbit_binary_succ b s j hs] using h j

private theorem decompose (a : V) : 2*(a/2)+a%2 = a := div_add_mod a 2
private theorem mod_two_le (a : V) : a % 2 ≤ 1 := lt_two_iff_le_one.mp (by simp)

/-- The successor adds at most one to the population. -/
theorem population_succ_le (a : V) : population (a+1) ≤ population a + 1 := by
  induction a using ISigma1.sigma1_order_induction
  · definability
  case ind a ih =>
    rcases zero_or_succ a with rfl | ⟨a', ha'⟩
    · simp
    · have ha : 0 < a := by rw [ha']; simp
      have hu : a/2 < a := div_lt_of_pos_of_one_lt ha (by norm_num)
      have he := decompose a
      rcases le_one_iff_eq_zero_or_one.mp (mod_two_le a) with hr | hr
      · have h1 : a + 1 = 2*(a/2)+1 := by rw [← he, hr]; simp
        have h0 : a = 2*(a/2)+0 := by rw [← hr]; exact he.symm
        rw [h1, population_binary _ 1 le_rfl]
        conv_rhs => rw [h0, population_binary _ 0 (by simp)]
        simp
      · have h1 : a + 1 = 2*(a/2+1)+0 := by
          have h2 : a + 1 = 2*(a/2)+a%2+1 := by rw [he]
          rw [h2, hr]; ring
        have h0 : a = 2*(a/2)+1 := by rw [← hr]; exact he.symm
        rw [h1, population_binary _ 0 (by simp)]
        conv_rhs => rw [h0, population_binary _ 1 le_rfl]
        have := ih (a/2) hu
        simpa using le_trans this (by simp)

/-- **Subadditivity and the exact equality characterization.** -/
theorem population_add (a b : V) :
    population (a+b) ≤ population a + population b ∧
      (population (a+b) = population a + population b ↔ NoCarry a b) := by
  have key : ∀ N : V, ∀ a ≤ N, ∀ b ≤ N, a + b = N →
      population (a+b) ≤ population a + population b ∧
        (population (a+b) = population a + population b ↔ NoCarry a b) := by
    intro N
    induction N using ISigma1.sigma1_order_induction
    · definability
    case ind N ih =>
      intro a _ b _ hab
      rcases zero_or_succ N with rfl | ⟨N', hN'⟩
      · have ha : a = 0 := le_antisymm (by rw [← hab]; exact le_add_right le_rfl) (Arithmetic.zero_le _)
        have hb : b = 0 := le_antisymm (by rw [← hab]; exact le_add_left le_rfl) (Arithmetic.zero_le _)
        subst ha; subst hb
        refine ⟨by simp, ⟨fun _ => ?_, fun _ => by simp⟩⟩
        rw [noCarry_iff]; intro i; simp
      · have hN : 0 < N := by rw [hN']; simp
        set A := a/2
        set B := b/2
        set r := a%2
        set s := b%2
        have ha : 2*A+r = a := decompose a
        have hb : 2*B+s = b := decompose b
        have hr : r ≤ 1 := mod_two_le a
        have hs : s ≤ 1 := mod_two_le b
        set H := A + B
        have hsum : a + b = 2*H + (r+s) := by
          rw [← ha, ← hb]; simp only [H]; ring
        have hHN : H < N := by
          rcases zero_or_succ H with h0 | ⟨h, hh⟩
          · rw [h0]; exact hN
          · have hHpos : 0 < H := by rw [hh]; simp
            calc H < 2*H := by
                    have := lt_add_of_pos_left H hHpos
                    simpa [two_mul] using this
              _ ≤ 2*H + (r+s) := le_add_right le_rfl
              _ = N := by rw [← hsum, hab]
        have ih' := ih H hHN A (le_add_right le_rfl) B (le_add_left le_rfl) rfl
        have hpa : population a = population A + r := by
          conv_lhs => rw [← ha]
          exact population_binary A r hr
        have hpb : population b = population B + s := by
          conv_lhs => rw [← hb]
          exact population_binary B s hs
        have hnc : NoCarry a b ↔ r + s ≤ 1 ∧ NoCarry A B := by
          rw [← noCarry_binary A B r s hr hs, ha, hb]
        by_cases hrs : r + s ≤ 1
        · have hp : population (a+b) = population H + (r+s) := by
            rw [hsum]; exact population_binary H (r+s) hrs
          rw [hp, hpa, hpb, hnc]
          refine ⟨?_, ?_⟩
          · have := ih'.1
            calc population H + (r+s) ≤ population A + population B + (r+s) := by
                  simpa using add_le_add_right this (r+s)
              _ = population A + r + (population B + s) := by ring
          · constructor
            · intro he
              refine ⟨hrs, ih'.2.mp ?_⟩
              have : population H + (r+s) = population A + population B + (r+s) := by
                rw [he]; ring
              exact add_right_cancel this
            · rintro ⟨-, h⟩
              rw [ih'.2.mpr h]; ring
        · have hr1 : r = 1 := by
            exact (le_one_iff_eq_zero_or_one.mp hr).resolve_left (fun h => hrs (by simpa [h] using hs))
          have hs1 : s = 1 := by
            exact (le_one_iff_eq_zero_or_one.mp hs).resolve_left (fun h => hrs (by simpa [h] using hr))
          have hp : population (a+b) = population (H+1) := by
            rw [hsum, hr1, hs1, show (2:V)*H+(1+1) = 2*(H+1)+0 by ring]
            simpa using population_binary (H+1) 0 (by simp)
          have hlt : population (a+b) < population a + population b := by
            rw [hp, hpa, hpb, hr1, hs1]
            calc population (H+1) ≤ population H + 1 := population_succ_le H
              _ ≤ population A + population B + 1 := by simpa using add_le_add_right ih'.1 1
              _ < population A + 1 + (population B + 1) := by
                simpa [add_assoc, add_comm, add_left_comm] using
                  lt_add_one (population A + population B + 1)
          refine ⟨le_of_lt hlt, ⟨fun he => absurd he (ne_of_lt hlt), fun h => ?_⟩⟩
          exact absurd (hnc.mp h).1 hrs
  exact key (a+b) a (le_add_right le_rfl) b (le_add_left le_rfl) rfl

theorem population_subadditive (a b : V) :
    population (a+b) ≤ population a + population b := (population_add a b).1

theorem population_add_eq_iff (a b : V) :
    population (a+b) = population a + population b ↔ NoCarry a b := (population_add a b).2

end DiophantineConsistency.ArithmeticBinaryCarry
