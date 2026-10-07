import OAI.Combinatorics.Progressions.Fourier.CharacterCenteredCounting
import OAI.Combinatorics.Progressions.Fourier.ConfigurationCharacters

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_configuration_centered_counting (s : ℕ) (hs : 1 ≤ s)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C : ℕ, 2 ≤ C ∧ ∃ xi : ℝ, 0 < xi ∧
    ∀ {N : ℕ} [NeZero N] {p : ℝ}, 2 ≤ p → Odd N → Real.exp ((p + 2) ^ C) ≤ N →
      ∀ mu : ZMod N → ℝ, (∀ x, 0 ≤ mu x ∧ mu x ≤ Real.exp p) → (𝔼 x, mu x) = 1 →
      CyclicNiltestUpperComparison.{0} s N ((p + 2) ^ C)
        (Real.exp (-((p + 2) ^ C))) mu (fun _ => 1 + xi) →
      ∀ {I : Type} [Fintype I] [DecidableEq I] [Nonempty I], Fintype.card I ≤ s + 2 →
      ∀ (slopes : I → ZMod N), (∀ i j, i ≠ j → IsUnit (slopes i - slopes j)) →
      ∀ Psi : AddChar (ZMod N × ZMod N) ℂ,
      ‖𝔼 x, 𝔼 d, Psi (x, d) * (∏ i, ((mu (x + slopes i * d) - 1 : ℝ) : ℂ))‖ ≤ epsilon := by
  classical
  obtain ⟨C, hC, xi, hxi, hcount⟩ := exists_character_centered_counting s hs hepsilon
  refine ⟨C, hC, xi, hxi, ?_⟩
  intro N _ p hp hodd hN mu hmu hmean hcompare I _ _ _ hI slopes hsep Psi
  by_cases hsmall : Fintype.card I ≤ 1
  · let : Subsingleton I := Fintype.card_le_one_iff_subsingleton.mp hsmall
    let i : I := Classical.arbitrary I
    obtain ⟨chi, hchi⟩ := exists_single_slope_character_bound (slopes i) Psi
      (fun u => ((mu u - 1 : ℝ) : ℂ))
    have hsingle := hcount hp hodd hN mu hmu hmean hcompare (I := Unit)
      (by simp) (fun _ => (0 : ZMod N)) (fun _ => chi)
      (fun i j hij => (hij (Subsingleton.elim i j)).elim)
    have hsingle' : ‖𝔼 u, chi u * ((mu u - 1 : ℝ) : ℂ)‖ ≤ epsilon := by
      simpa using hsingle
    have hprod (x d : ZMod N) :
        (∏ j : I, ((mu (x + slopes j * d) - 1 : ℝ) : ℂ)) =
          ((mu (x + slopes i * d) - 1 : ℝ) : ℂ) := Fintype.prod_subsingleton _ i
    simp only [hprod]
    exact hchi.trans hsingle'
  obtain ⟨i, _, j, _, hij⟩ := Finset.one_lt_card.mp
    (show 1 < (Finset.univ : Finset I).card by simpa using (show 1 < Fintype.card I by omega))
  obtain ⟨chi, rho, hfactor⟩ := exists_two_slope_characters (slopes i) (slopes j)
    (hsep j i (Ne.symm hij)) Psi
  let theta : I → AddChar (ZMod N) ℂ := fun k => if k = i then chi else if k = j then rho else 0
  have htheta (x d : ZMod N) :
      (∏ k : I, theta k (x + slopes k * d)) = Psi (x, d) := by
    rw [← Finset.mul_prod_erase Finset.univ (fun k => theta k (x + slopes k * d)) (Finset.mem_univ i)]
    have hi : theta i (x + slopes i * d) = chi (x + slopes i * d) := by simp [theta]
    have hj : (∏ k ∈ (Finset.univ : Finset I).erase i, theta k (x + slopes k * d)) =
        rho (x + slopes j * d) := by
      rw [Finset.prod_eq_single_of_mem j (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩)]
      · simp [theta, Ne.symm hij]
      · intro k hk hkj
        simp [theta, Finset.ne_of_mem_erase hk, hkj]
    rw [hi, hj, ← hfactor]
  have h := hcount hp hodd hN mu hmu hmean hcompare hI slopes theta hsep
  simpa only [Finset.prod_mul_distrib, htheta] using h

end Erdos3

end

end OAI
