import GowersSzemeredi.Proofs13FejerPurifiedDensity
import GowersSzemeredi.Proofs12Amplification

/-! Propagate uniform Fejer purification through the prepared frequency
graph. The retained density exponent is 4,207,554,485, with the exact
mostly-respected and Fourier hypotheses required for square extraction.

`section13_fejer_frequency_graph` is in `Proofs13FejerFrequencyGraphSide`,
outside the final route. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem section13_fejer_graph_coefficient {a : Real} (ha : 0 < a) (hahalf : a ≤ 1 / 2) :
    a ^ (4207554485 : Nat) ≤ ((2 : Real) ^ 77)⁻¹ *
      ((a ^ (14409429 : Nat)) ^ 97 * a ^ 336) ^ 3 * ((1 / 2 : Real) ^ 44) ^ 3 * a ^ (14409429 : Nat) := by
  have hc : a ^ 209 ≤ ((2 : Real) ^ 77)⁻¹ * ((1 / 2 : Real) ^ 44) ^ 3 := by
    calc
      _ ≤ (1 / 2 : Real) ^ 209 := pow_le_pow_left₀ ha.le hahalf _
      _ = _ := by norm_num
  calc
    _ = a ^ 209 * ((((a ^ (14409429 : Nat)) ^ 97 * a ^ 336) ^ 3) * a ^ (14409429 : Nat)) := by
      simp only [← pow_mul, ← pow_add]
    _ ≤ (((2 : Real) ^ 77)⁻¹ * ((1 / 2 : Real) ^ 44) ^ 3) *
        ((((a ^ (14409429 : Nat)) ^ 97 * a ^ 336) ^ 3) * a ^ (14409429 : Nat)) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by ring

theorem separatelyFreimanEight_subset {N : Nat} [NeZero N]
    {A B : Finset (Pair N)} {phi : Pair N → ZMod N}
    (hAB : A ⊆ B) (hB : SeparatelyFreimanEight B phi) : SeparatelyFreimanEight A phi := by
  constructor
  · intro x
    have hsec : (↑(verticalSection A x) : Set (ZMod N)) ⊆ ↑(verticalSection B x) := by
      intro y hy
      have hyA : (x, y) ∈ A := by simpa [verticalSection] using hy
      simpa [verticalSection] using hAB hyA
    exact IsAddFreimanHom.subset hsec (hB.1 x) (Set.mapsTo_univ _ _)
  · intro y
    have hsec : (↑(horizontalSection A y) : Set (ZMod N)) ⊆ ↑(horizontalSection B y) := by
      intro x hx
      have hxA : (x, y) ∈ A := by simpa [horizontalSection] using hx
      simpa [horizontalSection] using hAB hxA
    exact IsAddFreimanHom.subset hsec (hB.2 y) (Set.mapsTo_univ _ _)

def section13FrequencyGraphThreshold (alpha : Real) : Nat :=
  let a := alpha / 2
  let delta := a ^ (14409429 : Nat)
  fejerPurificationThreshold delta (delta ^ 97 * a ^ 336) ((1 / 2 : Real) ^ 44)

theorem section13_fejer_frequency_graph_explicit (alpha : Real) (halpha : 0 < alpha) (halpha1 : alpha ≤ 1) :
    ∀ (N : Nat) [NeZero N] [Fact N.Prime], section13FrequencyGraphThreshold alpha ≤ N →
      ∀ f : ZMod N → Complex, DiscValued f → ¬ UniformOfDegree f alpha 3 →
      ∃ A : Finset (Pair N), ∃ phi : Pair N → ZMod N,
        (alpha / 2) ^ (4207554485 : Nat) * (N : Real) ^ 2 ≤ A.card ∧
        SeparatelyFreimanEight A phi ∧ MostlyRespectsEight A phi ((2 : Real) ^ (-(44 : Int))) ∧
        ∀ z, z ∈ A → alpha * N / 2 ≤ ‖secondDifferenceFourier f z.1 z.2 (phi z)‖ := by
  let a : Real := alpha / 2
  let delta : Real := a ^ (14409429 : Nat)
  let rho : Real := delta ^ 97 * a ^ 336
  let eta : Real := (1 / 2 : Real) ^ 44
  have ha : 0 < a := by positivity
  have hahalf : a ≤ 1 / 2 := by dsimp [a]; linarith only [halpha1]
  have ha1 : a ≤ 1 := hahalf.trans (by norm_num)
  have hd : 0 < delta := pow_pos ha _
  have hr1 : rho ≤ 1 :=
    mul_le_one₀ (pow_le_one₀ hd.le (pow_le_one₀ ha.le ha1)) (by positivity) (pow_le_one₀ ha.le ha1)
  intro N _ _ hN f hf hnot
  obtain ⟨U, phi, hU, hfreiman, hfourier⟩ :=
    section13_prepared_frequency_graph alpha halpha halpha1 f hf hnot
  have hn2 : (0 : Real) < (N : Real) ^ 2 := pow_pos (by exact_mod_cast NeZero.pos N) _
  let beta : Real := (U.card : Real) / (N : Real) ^ 2
  have hdb : delta ≤ beta := (le_div_iff₀ hn2).mpr hU
  have hb : 0 < beta := hd.trans_le hdb
  have hcard : (U.card : Real) = beta * (N : Real) ^ 2 := (div_mul_cancel₀ _ hn2.ne').symm
  have habundance : rho * beta ^ 15 * (N : Real) ^ 32 ≤ respectedArrangementCount 8 U phi := by
    refine le_trans ?_ (lemma_12_4_holds N beta a f U phi hb ha hf hcard hfourier)
    rw [show 112 = 97 + 15 from rfl, pow_add, mul_right_comm (beta ^ 97)]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ hd.le hdb 97) (pow_nonneg ha.le 336)) (pow_nonneg hb.le 15))
      (pow_nonneg (Nat.cast_nonneg N) 32)
  obtain ⟨A, hAU, hmass, hmostly⟩ := section13_fejer_density_explicit delta rho eta hd
    (by positivity) hr1 (by positivity) (pow_le_one₀ (by norm_num) (by norm_num)) N hN U phi beta
    hdb hcard habundance
  refine ⟨A, phi, le_trans ?_ hmass, separatelyFreimanEight_subset hAU hfreiman, ?_,
    fun z hz => Eq.trans_le (by ring) (hfourier z (hAU hz))⟩
  · exact mul_le_mul_of_nonneg_right ((section13_fejer_graph_coefficient ha hahalf).trans
      (mul_le_mul_of_nonneg_left hdb (by positivity))) hn2.le
  · simpa only [MostlyRespectsEight, eta,
      show (1 / 2 : Real) ^ 44 = (2 : Real) ^ (-(44 : Int)) by norm_num] using hmostly

end LeanProofs.GowersSzemeredi
