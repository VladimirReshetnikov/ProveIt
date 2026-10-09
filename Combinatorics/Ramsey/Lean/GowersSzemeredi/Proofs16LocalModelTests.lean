import GowersSzemeredi.Proofs16FreimanNonvanishing
import GowersSzemeredi.Proofs16SeparatingFrequencies

/-! Count evaluations and characters which detect a nonzero local model
while staying inside all required column domains. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical
open scoped BigOperators

def localSeparatingTests {N : Nat} [NeZero N] (B : Finset (ZMod N))
    (f : ZMod N → ZMod N) : Finset (ZMod N × ZMod N) :=
  (B ×ˢ Finset.univ).filter (fun p => Separates p.2 (f p.1))

theorem localSeparatingTests_card {N : Nat} [NeZero N] (B : Finset (ZMod N))
    (f : ZMod N → ZMod N) :
    (localSeparatingTests B f).card =
      ∑ y ∈ B, (Finset.univ.filter (fun g : ZMod N => Separates g (f y))).card := by
  simp only [localSeparatingTests,Finset.card_filter,Finset.sum_product]

/-- Every nonzero value is detected by at least half the characters. -/
theorem localSeparatingTests_card_lower {N : Nat} [NeZero N] [Fact N.Prime]
    (h7 : 7 ≤ N) (B : Finset (ZMod N)) (f : ZMod N → ZMod N) :
    N*(B.filter (fun y => f y ≠ 0)).card ≤ 2*(localSeparatingTests B f).card := by
  have hpoint : ∀ y, (if f y ≠ 0 then N else 0) ≤
      2*(Finset.univ.filter (fun g : ZMod N => Separates g (f y))).card := by
    intro y
    by_cases hy : f y = 0
    · simp [hy]
    · rw [if_pos hy]
      have hb := small_multiples_card_le h7 hy
      have he := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (ZMod N)))
        (fun g => Separates g (f y))
      simp only [Finset.card_univ,ZMod.card] at he
      omega
  rw [localSeparatingTests_card,Finset.mul_sum]
  calc
    _ = ∑ y ∈ B, (if f y ≠ 0 then N else 0) := by
      rw [Finset.card_filter,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : f y = 0 <;> simp [hy]
    _ ≤ _ := Finset.sum_le_sum fun y _ => hpoint y

/-- The test density is uniform over all extra spectra of bounded rank. -/
theorem freiman_local_separating_tests {N d e : Nat} [NeZero N] [Fact N.Prime]
    (T U : Finset (ZMod N)) (f : ZMod N → ZMod N) {rho r : Real}
    (hrho : 0 < rho) (hr : 0 < r) (hrle : r ≤ rho)
    (hT : T.card ≤ d) (hU : U.card ≤ e)
    (hf : IsFreimanLinearOn (bohr T rho) f) (hf0 : f 0 = 0)
    (hne : ∃ y ∈ bohr T (refinementKernelRadius d e rho (r/2)), f y ≠ 0)
    (hN : refinementKernelCap d e rho (r/2) < N) (h7 : 7 ≤ N) :
    (N : Real)^2 / (4*(refinementCells (r/2) : Real)^(d+e)) ≤
      (localSeparatingTests (bohr (T ∪ U) r) f).card := by
  have hnz := freiman_nonzero_card_with_extra_frequencies T U f hrho hr hrle hT hU hf hf0 hne hN
  have hsep := localSeparatingTests_card_lower h7 (bohr (T ∪ U) r) f
  have hprod : N^2 ≤ 4*(refinementCells (r/2))^(d+e)*
      (localSeparatingTests (bohr (T ∪ U) r) f).card := by
    calc N^2 = N*N := by ring
      _ ≤ N*(2*(refinementCells (r/2))^(d+e)*((bohr (T ∪ U) r).filter (fun y => f y ≠ 0)).card) :=
        Nat.mul_le_mul_left N hnz
      _ = (2*(refinementCells (r/2))^(d+e))*(N*((bohr (T ∪ U) r).filter (fun y => f y ≠ 0)).card) := by ring
      _ ≤ (2*(refinementCells (r/2))^(d+e))*(2*(localSeparatingTests (bohr (T ∪ U) r) f).card) :=
        Nat.mul_le_mul_left _ hsep
      _ = _ := by ring
  have hQ : 0 < refinementCells (r/2) := Nat.ceil_pos.mpr (by positivity)
  apply (div_le_iff₀ (by positivity : (0 : Real) < 4*(refinementCells (r/2) : Real)^(d+e))).mpr
  have hR : (N : Real)^2 ≤ 4*(refinementCells (r/2) : Real)^(d+e)*
      (localSeparatingTests (bohr (T ∪ U) r) f).card := by exact_mod_cast hprod
  nlinarith only [hR]

end LeanProofs.GowersSzemeredi
