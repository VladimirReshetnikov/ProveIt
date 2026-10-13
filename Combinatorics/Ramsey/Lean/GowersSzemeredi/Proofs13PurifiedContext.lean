import GowersSzemeredi.Proofs12Combination
import GowersSzemeredi.Proofs13PreparedFrequencyGraph

/-! Recover the original 2^-73 arrangement error from Lemma 13.11, with a
stronger density exponent. Purification permits every integral error exponent
up to 2^30 while retaining density (alpha/2)^(2^64). -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- Lemma13.11 with an adjustable arrangement-error exponent and stronger density. -/
def lemma_13_11_purified (b : Nat) : Prop :=
  ∀ alpha : Real, 0 < alpha → alpha ≤ 1 → ∃ N0 : Nat,
    ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
      ∀ f : ZMod N → Complex, DiscValued f →
        ¬ UniformOfDegree f alpha 3 →
        ∃ A : Finset (Pair N), ∃ phi : Pair N → ZMod N,
          (alpha / 2) ^ ((2 : Nat) ^ 64) * (N : Real) ^ 2 ≤ A.card ∧
          SeparatelyFreimanEight A phi ∧
          MostlyRespectsEight A phi ((2 : Real) ^ (-(b : Int))) ∧
          ∀ z, z ∈ A →
            alpha * N / 2 ≤ ‖secondDifferenceFourier f z.1 z.2 (phi z)‖

private lemma purified_eta_eq (b : Nat) :
    (1 / 2 : Real) ^ b = (2 : Real) ^ (-(b : Int)) := by
  simp only [zpow_neg, zpow_natCast, one_div, inv_pow]


private lemma purified_prefactor_lower (a : Real) (ha : 0 ≤ a)
    (haHalf : a ≤ 1 / 2) :
    a ^ ((2 : Nat) ^ 37) ≤ (2 : Real) ^ (-((2 : Real) ^ 37)) := by
  have ha2 : a ^ 2 ≤ (4 : Real)⁻¹ := by
    calc
      a ^ 2 ≤ (1 / 2 : Real) ^ 2 := pow_le_pow_left₀ ha haHalf 2
      _ = (4 : Real)⁻¹ := by norm_num
  calc
    a ^ ((2 : Nat) ^ 37) = (a ^ 2) ^ ((2 : Nat) ^ 36) := by
      rw [← pow_mul]
      congr 1
    _ ≤ ((4 : Real)⁻¹) ^ ((2 : Nat) ^ 36) :=
      pow_le_pow_left₀ (by positivity) ha2 _
    _ = (2 : Real) ^ (-((2 : Real) ^ 37)) := by
      symm
      rw [Real.rpow_neg (by positivity)]
      rw [show (2 : Real) ^ 37 =
          2 * (((2 : Nat) ^ 36 : Nat) : Real) by norm_num]
      rw [Real.rpow_mul_natCast (by norm_num : (0 : Real) ≤ 2)]
      norm_num only [Real.rpow_two]
      rw [← inv_pow]
      norm_num


private lemma purified_coefficient_lower (b : Nat) (hb : b ≤ 2 ^ 30)
    (a : Real) (ha : 0 < a) (haHalf : a ≤ 1 / 2) (haOne : a ≤ 1) :
    a ^ (14 * (2 : Nat) ^ 64) ≤
      (2 : Real) ^ (-((2 : Real) ^ 37)) *
        (a ^ ((2 : Nat) ^ 24)) ^ ((2 : Nat) ^ 43) *
        a ^ ((2 : Nat) ^ 45) *
        ((1 / 2 : Real) ^ b) ^ ((2 : Nat) ^ 36) := by
  have hpref := purified_prefactor_lower a ha.le haHalf
  have heta : a ^ (b * (2 : Nat) ^ 36) ≤
      ((1 / 2 : Real) ^ b) ^ ((2 : Nat) ^ 36) := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (by positivity)
      (pow_le_pow_left₀ ha.le haHalf b) _
  have hexponent : (2 : Nat) ^ 37 + (2 : Nat) ^ 67 +
      (2 : Nat) ^ 45 + b * (2 : Nat) ^ 36 ≤ 14 * (2 : Nat) ^ 64 := by
    have hmul := Nat.mul_le_mul_right ((2 : Nat) ^ 36) hb
    norm_num at hmul ⊢
    omega
  have hbeta : (a ^ ((2 : Nat) ^ 24)) ^ ((2 : Nat) ^ 43) =
      a ^ ((2 : Nat) ^ 67) := by
    rw [← pow_mul]
    congr 1
  calc
    _ ≤ a ^ ((2 : Nat) ^ 37 + (2 : Nat) ^ 67 +
          (2 : Nat) ^ 45 + b * (2 : Nat) ^ 36) :=
      pow_le_pow_of_le_one ha.le haOne hexponent
    _ = a ^ ((2 : Nat) ^ 37) *
          (a ^ ((2 : Nat) ^ 24)) ^ ((2 : Nat) ^ 43) *
          a ^ ((2 : Nat) ^ 45) * a ^ (b * (2 : Nat) ^ 36) := by
      rw [pow_add, pow_add, pow_add, hbeta]
    _ ≤ _ := by
      have hp := mul_le_mul_of_nonneg_right hpref
        (show 0 ≤ (a ^ ((2 : Nat) ^ 24)) ^ ((2 : Nat) ^ 43) by positivity)
      have hpg := mul_le_mul_of_nonneg_right hp
        (show 0 ≤ a ^ ((2 : Nat) ^ 45) by positivity)
      exact mul_le_mul hpg heta (by positivity) (by positivity)


private lemma purified_card_lower_of_arrangements {N : Nat} [NeZero N]
    (a : Real) (ha : 0 < a) (haOne : a ≤ 1)
    (A : Finset (Pair N))
    (harr : a ^ (14 * (2 : Nat) ^ 64) * (N : Real) ^ 32 ≤
      arrangementCount 8 A) :
    a ^ ((2 : Nat) ^ 64) * (N : Real) ^ 2 ≤ A.card := by
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hN2 : 0 < (N : Real) ^ 2 := pow_pos hN 2
  have hupperNat := context_arrangementCount_le_card_pow A
  have hupper : (arrangementCount 8 A : Real) ≤
      (A.card : Real) ^ 15 * (N : Real) ^ 2 := by
    exact_mod_cast hupperNat
  by_contra hcard
  have hcardlt : (A.card : Real) <
      a ^ ((2 : Nat) ^ 64) * (N : Real) ^ 2 := lt_of_not_ge hcard
  have hpowlt : (A.card : Real) ^ 15 <
      (a ^ ((2 : Nat) ^ 64) * (N : Real) ^ 2) ^ 15 :=
    pow_lt_pow_left₀ hcardlt (by positivity) (by norm_num)
  have hcoefficient :
      (a ^ ((2 : Nat) ^ 64)) ^ 15 ≤ a ^ (14 * (2 : Nat) ^ 64) := by
    rw [← pow_mul]
    exact pow_le_pow_of_le_one ha.le haOne (by norm_num)
  have hcontra : (arrangementCount 8 A : Real) <
      a ^ (14 * (2 : Nat) ^ 64) * (N : Real) ^ 32 := by
    calc
      (arrangementCount 8 A : Real) ≤
          (A.card : Real) ^ 15 * (N : Real) ^ 2 := hupper
      _ < (a ^ ((2 : Nat) ^ 64) * (N : Real) ^ 2) ^ 15 *
          (N : Real) ^ 2 := mul_lt_mul_of_pos_right hpowlt hN2
      _ = (a ^ ((2 : Nat) ^ 64)) ^ 15 * (N : Real) ^ 32 := by ring
      _ ≤ a ^ (14 * (2 : Nat) ^ 64) * (N : Real) ^ 32 :=
        mul_le_mul_of_nonneg_right hcoefficient (by positivity)
  exact (not_lt_of_ge harr) hcontra


theorem lemma_13_11_purified_holds {b : Nat} (hb : b ≤ 2 ^ 30) :
    lemma_13_11_purified b := by
  intro alpha halpha halphaOne
  let a : Real := alpha / 2
  let beta : Real := a ^ ((2 : Nat) ^ 24)
  let eta : Real := (1 / 2 : Real) ^ b
  have ha : 0 < a := by dsimp only [a]; positivity
  have haHalf : a ≤ 1 / 2 := by dsimp only [a]; nlinarith
  have haOne : a ≤ 1 := haHalf.trans (by norm_num)
  have hbeta : 0 < beta := pow_pos ha _
  have heta : 0 < eta := by dsimp only [eta]; positivity
  have hetaOne : eta ≤ 1 := by
    dsimp only [eta]
    exact pow_le_one₀ (by norm_num) (by norm_num)
  obtain ⟨N0, hN0⟩ :=
    lemma_12_6_holds beta a eta hbeta ha heta hetaOne
  refine ⟨N0, ?_⟩
  intro N _ _ hN f hf hnotUniform
  classical
  have hprime : Nat.Prime N := Fact.out
  have hNreal : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hN2 : 0 < (N : Real) ^ 2 := pow_pos hNreal 2
  obtain ⟨B2, phi, hB2exact, hB2freiman, hB2large⟩ :=
    section13_prepared_frequency_graph alpha halpha halphaOne f hf hnotUniform
  have hbetaPower : beta ≤ a ^ 14409429 := by
    dsimp only [beta]
    exact pow_le_pow_of_le_one ha.le haOne (by norm_num)
  have hB2card : beta * (N : Real) ^ 2 ≤ B2.card :=
    (mul_le_mul_of_nonneg_right hbetaPower hN2.le).trans hB2exact
  obtain ⟨A, hAsub, harrRaw, hmostly⟩ :=
    hN0 N hN f B2 phi hf hB2card hB2large
  have harr : a ^ (14 * (2 : Nat) ^ 64) * (N : Real) ^ 32 ≤
      arrangementCount 8 A :=
    (mul_le_mul_of_nonneg_right
      (purified_coefficient_lower b hb a ha haHalf haOne) (by positivity)).trans harrRaw
  refine ⟨A, phi, ?_, ?_, ?_, ?_⟩
  · simpa only [a] using purified_card_lower_of_arrangements a ha haOne A harr
  · constructor
    · intro x
      have hsec : (↑(verticalSection A x) : Set (ZMod N)) ⊆
          ↑(verticalSection B2 x) := by
        intro y hy
        have hyA : (x, y) ∈ A := by simpa [verticalSection] using hy
        have hyB1 := hAsub hyA
        simpa [verticalSection] using hyB1
      exact IsAddFreimanHom.subset hsec (hB2freiman.1 x) (Set.mapsTo_univ _ _)
    · intro y
      have hsec : (↑(horizontalSection A y) : Set (ZMod N)) ⊆
          ↑(horizontalSection B2 y) := by
        intro x hx
        have hxA : (x, y) ∈ A := by simpa [horizontalSection] using hx
        simpa [horizontalSection] using hAsub hxA
      exact IsAddFreimanHom.subset hsec (hB2freiman.2 y) (Set.mapsTo_univ _ _)
  · simpa only [MostlyRespectsEight, eta, purified_eta_eq b] using hmostly
  · intro z hz
    have hzlarge := hB2large z (hAsub hz)
    convert hzlarge using 1
    ring

theorem lemma_13_11_purified_seventy_three : lemma_13_11_purified 73 := by
  exact @lemma_13_11_purified_holds 73 (by decide)


/-- The original 2^-73 clause with the printed density exponent. -/
def lemma_13_11_original_error : Prop :=
  ∀ alpha : Real, 0 < alpha → alpha ≤ 1 → ∃ N0 : Nat,
    ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
      ∀ f : ZMod N → Complex, DiscValued f →
        ¬ UniformOfDegree f alpha 3 →
        ∃ A : Finset (Pair N), ∃ phi : Pair N → ZMod N,
          (alpha / 2) ^ ((2 : Nat) ^ 66) * (N : Real) ^ 2 ≤ A.card ∧
          SeparatelyFreimanEight A phi ∧
          MostlyRespectsEight A phi ((2 : Real) ^ (-(73 : Int))) ∧
          ∀ z, z ∈ A →
            alpha * N / 2 ≤ ‖secondDifferenceFourier f z.1 z.2 (phi z)‖

/-- Restore the original error without weakening any of its other conclusions. -/
theorem lemma_13_11_original_error_holds : lemma_13_11_original_error := by
  intro alpha ha haone
  obtain ⟨N0, hN0⟩ := lemma_13_11_purified_seventy_three alpha ha haone
  refine ⟨N0, ?_⟩
  intro N _ _ hN f hf hnot
  obtain ⟨A, phi, hcard, hfreiman, hmostly, hlarge⟩ := hN0 N hN f hf hnot
  refine ⟨A, phi, ?_, hfreiman, hmostly, hlarge⟩
  have hbase : alpha / 2 ≤ 1 := by linarith only [haone]
  have hp : (alpha / 2) ^ ((2 : Nat) ^ 66) ≤
      (alpha / 2) ^ ((2 : Nat) ^ 64) :=
    pow_le_pow_of_le_one (a := alpha / 2)
      (m := (2 : Nat) ^ 64) (n := (2 : Nat) ^ 66)
      (by positivity) hbase (by decide)
  exact (mul_le_mul_of_nonneg_right hp (by positivity)).trans hcard


end LeanProofs.GowersSzemeredi
