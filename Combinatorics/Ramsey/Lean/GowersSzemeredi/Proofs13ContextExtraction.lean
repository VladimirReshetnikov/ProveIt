import GowersSzemeredi.Proofs13PreparedFrequencyGraph
import GowersSzemeredi.Proofs12Combination

/-!
# Extracting the separately Freiman context

This file proves Lemma 13.11.  There is a quantitative omission in the paper's
proof: on a fibre of density `rho`, Proposition 6.1 and Corollary 7.6 must be
used with additive parameter `rho * (alpha / 2) ^ 8`, not `rho`.  Keeping this
factor through both fibre restrictions gives density `(alpha / 2) ^ (2 ^ 24)`.
Lemma 12.6 then gives `(alpha / 2) ^ (2 ^ 68) * N ^ 32` arrangements.  The
sharp elementary upper bound `arrangementCount 8 A ≤ A.card ^ 15 * N ^ 2`
recovers the stated cardinality `(alpha / 2) ^ (2 ^ 66) * N ^ 2`.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

private lemma context_eta_eq :
    (1 / 2 : Real) ^ 44 = (2 : Real) ^ (-(44 : Int)) := by
  rw [show (-(44 : Int)) = Int.negSucc 43 by decide, zpow_negSucc,
    one_div, inv_pow]

private lemma context_prefactor_lower (a : Real) (ha : 0 ≤ a)
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

private lemma context_coefficient_lower (a : Real) (ha : 0 < a)
    (haHalf : a ≤ 1 / 2) (haOne : a ≤ 1) :
    a ^ ((2 : Nat) ^ 68) ≤
      (2 : Real) ^ (-((2 : Real) ^ 37)) *
        (a ^ ((2 : Nat) ^ 24)) ^ ((2 : Nat) ^ 43) *
        a ^ ((2 : Nat) ^ 45) *
        ((1 / 2 : Real) ^ 44) ^ ((2 : Nat) ^ 36) := by
  have hpref := context_prefactor_lower a ha.le haHalf
  have ha44 : a ^ 44 ≤ (1 / 2 : Real) ^ 44 :=
    pow_le_pow_left₀ ha.le haHalf 44
  have hetaRaw : a ^ (44 * ((2 : Nat) ^ 36)) ≤
      ((1 / 2 : Real) ^ 44) ^ ((2 : Nat) ^ 36) := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (by positivity) ha44 _
  have heta : a ^ ((2 : Nat) ^ 42) ≤
      ((1 / 2 : Real) ^ 44) ^ ((2 : Nat) ^ 36) := by
    exact (pow_le_pow_of_le_one ha.le haOne (by norm_num)).trans hetaRaw
  have hexponent :
      (2 : Nat) ^ 37 + (2 : Nat) ^ 67 + (2 : Nat) ^ 45 + (2 : Nat) ^ 42 ≤
        (2 : Nat) ^ 68 := by norm_num
  have hbetaExponent :
      (a ^ ((2 : Nat) ^ 24)) ^ ((2 : Nat) ^ 43) =
        a ^ ((2 : Nat) ^ 67) := by
    rw [← pow_mul]
    congr 1
  calc
    a ^ ((2 : Nat) ^ 68) ≤
        a ^ ((2 : Nat) ^ 37 + (2 : Nat) ^ 67 +
          (2 : Nat) ^ 45 + (2 : Nat) ^ 42) :=
      pow_le_pow_of_le_one ha.le haOne hexponent
    _ = a ^ ((2 : Nat) ^ 37) * a ^ ((2 : Nat) ^ 67) *
          a ^ ((2 : Nat) ^ 45) * a ^ ((2 : Nat) ^ 42) := by
      rw [pow_add, pow_add, pow_add]
    _ = a ^ ((2 : Nat) ^ 37) *
          (a ^ ((2 : Nat) ^ 24)) ^ ((2 : Nat) ^ 43) *
          a ^ ((2 : Nat) ^ 45) * a ^ ((2 : Nat) ^ 42) := by
      rw [hbetaExponent]
    _ ≤ (2 : Real) ^ (-((2 : Real) ^ 37)) *
          (a ^ ((2 : Nat) ^ 24)) ^ ((2 : Nat) ^ 43) *
          a ^ ((2 : Nat) ^ 45) *
          ((1 / 2 : Real) ^ 44) ^ ((2 : Nat) ^ 36) := by
      have hmiddle : 0 ≤
          (a ^ ((2 : Nat) ^ 24)) ^ ((2 : Nat) ^ 43) := by positivity
      have hgamma : 0 ≤ a ^ ((2 : Nat) ^ 45) := by positivity
      have hpref' :
          a ^ ((2 : Nat) ^ 37) *
              (a ^ ((2 : Nat) ^ 24)) ^ ((2 : Nat) ^ 43) ≤
            (2 : Real) ^ (-((2 : Real) ^ 37)) *
              (a ^ ((2 : Nat) ^ 24)) ^ ((2 : Nat) ^ 43) :=
        mul_le_mul_of_nonneg_right hpref hmiddle
      have hpref'' :
          a ^ ((2 : Nat) ^ 37) *
                (a ^ ((2 : Nat) ^ 24)) ^ ((2 : Nat) ^ 43) *
              a ^ ((2 : Nat) ^ 45) ≤
            (2 : Real) ^ (-((2 : Real) ^ 37)) *
                (a ^ ((2 : Nat) ^ 24)) ^ ((2 : Nat) ^ 43) *
              a ^ ((2 : Nat) ^ 45) :=
        mul_le_mul_of_nonneg_right hpref' hgamma
      exact mul_le_mul hpref'' heta (by positivity) (by positivity)

private lemma context_card_lower_of_arrangements {N : Nat} [NeZero N]
    (a : Real) (ha : 0 < a) (haOne : a ≤ 1)
    (A : Finset (Pair N))
    (harr : a ^ ((2 : Nat) ^ 68) * (N : Real) ^ 32 ≤
      arrangementCount 8 A) :
    a ^ ((2 : Nat) ^ 66) * (N : Real) ^ 2 ≤ A.card := by
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hN2 : 0 < (N : Real) ^ 2 := pow_pos hN 2
  have hupperNat := context_arrangementCount_le_card_pow A
  have hupper : (arrangementCount 8 A : Real) ≤
      (A.card : Real) ^ 15 * (N : Real) ^ 2 := by
    exact_mod_cast hupperNat
  by_contra hcard
  have hcardlt : (A.card : Real) <
      a ^ ((2 : Nat) ^ 66) * (N : Real) ^ 2 := lt_of_not_ge hcard
  have hpowlt : (A.card : Real) ^ 15 <
      (a ^ ((2 : Nat) ^ 66) * (N : Real) ^ 2) ^ 15 :=
    pow_lt_pow_left₀ hcardlt (by positivity) (by norm_num)
  have hcoefficient :
      (a ^ ((2 : Nat) ^ 66)) ^ 15 ≤ a ^ ((2 : Nat) ^ 68) := by
    rw [← pow_mul]
    exact pow_le_pow_of_le_one ha.le haOne (by norm_num)
  have hcontra : (arrangementCount 8 A : Real) <
      a ^ ((2 : Nat) ^ 68) * (N : Real) ^ 32 := by
    calc
      (arrangementCount 8 A : Real) ≤
          (A.card : Real) ^ 15 * (N : Real) ^ 2 := hupper
      _ < (a ^ ((2 : Nat) ^ 66) * (N : Real) ^ 2) ^ 15 *
          (N : Real) ^ 2 := mul_lt_mul_of_pos_right hpowlt hN2
      _ = (a ^ ((2 : Nat) ^ 66)) ^ 15 * (N : Real) ^ 32 := by ring
      _ ≤ a ^ ((2 : Nat) ^ 68) * (N : Real) ^ 32 :=
        mul_le_mul_of_nonneg_right hcoefficient (by positivity)
  exact (not_lt_of_ge harr) hcontra

/-- **Gowers, Lemma 13.11.** Failure of cubic uniformity yields a large
two-dimensional domain on which the selected Fourier frequency is separately
an order-eight Freiman homomorphism and respects almost every arrangement. -/
theorem lemma_13_11_holds : lemma_13_11 := by
  intro alpha halpha halphaOne
  let a : Real := alpha / 2
  let beta : Real := a ^ ((2 : Nat) ^ 24)
  let eta : Real := (1 / 2 : Real) ^ 44
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
  have harr : a ^ ((2 : Nat) ^ 68) * (N : Real) ^ 32 ≤
      arrangementCount 8 A :=
    (mul_le_mul_of_nonneg_right
      (context_coefficient_lower a ha haHalf haOne) (by positivity)).trans harrRaw
  refine ⟨A, phi, ?_, ?_, ?_, ?_⟩
  · simpa only [a] using context_card_lower_of_arrangements a ha haOne A harr
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
  · simpa only [MostlyRespectsEight, eta, context_eta_eq] using hmostly
  · intro z hz
    have hzlarge := hB2large z (hAsub hz)
    convert hzlarge using 1
    ring

end LeanProofs.GowersSzemeredi
