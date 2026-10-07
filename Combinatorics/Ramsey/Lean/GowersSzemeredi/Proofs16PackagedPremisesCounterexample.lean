import GowersSzemeredi.Proofs16NonMultiplyLinearWords
import GowersSzemeredi.Proofs16AlphabetPackagedCover
import GowersSzemeredi.Proofs16FullGoodDomain
import Mathlib.Data.Nat.Prime.Infinite

/-! The two premises currently packaged in `lemma_16_10` do not entail its
conclusion. This preserves the predicate being refuted and makes no claim
against the paper's lemma with all of its preceding structural hypotheses. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem lemma_16_10_packaged_premises_counterexample : ¬ lemma_16_10 := by
  classical
  intro hlemma
  obtain ⟨R, N₀, hR, hRbound, hwords⟩ := exists_non_multiplyLinear_finite_word 1
  obtain ⟨N, hN, hprime⟩ := Nat.exists_infinite_primes N₀
  letI : Fact N.Prime := ⟨hprime⟩
  letI : NeZero N := ⟨hprime.ne_zero⟩
  obtain ⟨S, f, hS, hf, hnot⟩ := hwords N hN
  let phi : Point N 2 → ZMod N := fun z => f (section16Last z)
  have hdom := section16GoodDomain_full (N := N) (k := 1) (fun _ => 0)
  have hphi := section16PhiOne_last_function (k := 1) f (fun _ => 0)
  have hconclusion := hlemma N 1 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    Finset.univ phi Finset.univ (fun _ => Finset.univ) (fun _ => 0)
  dsimp only at hconclusion
  rw [hdom, show section16PhiOne phi (fun _ => 0) = phi from hphi] at hconclusion
  apply hnot
  apply hconclusion
  · apply finalCoordinateSections_of_last_function Finset.univ f (by norm_num) (by norm_num)
    have hr8 := section16Lemma9R_unit_one_ge_eight
    have heq : section16Lemma9R 1 1 1 =
        (1 : Real) ^ (-(2 : Int)) * multipleS ((2 : Real) ^ (-(1 + 2 : Real)) * 1) 1 1 := by
      simp only [section16Lemma9R, Nat.pow_one, Nat.reduceSub, Nat.cast_one, one_mul]
    rw [heq] at hr8
    simp only [Nat.cast_one]
    linarith
  · apply finiteAlphabet_allBoxLineCovers_unit Finset.univ phi S
    · intro z hz
      exact hf _
    · rw [hS]
      exact hRbound

end LeanProofs.GowersSzemeredi
