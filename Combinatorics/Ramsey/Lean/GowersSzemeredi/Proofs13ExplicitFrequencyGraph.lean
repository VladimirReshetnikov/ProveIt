import GowersSzemeredi.Proofs13FejerFrequencyGraph
import GowersSzemeredi.Proofs13ExplicitFejerPurification

/-! Explicit starting modulus for the purified cubic frequency graph. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

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
  have ha : 0 < a := by dsimp [a]; positivity
  have hahalf : a ≤ 1 / 2 := by dsimp [a]; linarith only [halpha1]
  have ha1 : a ≤ 1 := hahalf.trans (by norm_num)
  have hd : 0 < delta := pow_pos ha _
  have hd1 : delta ≤ 1 := pow_le_one₀ ha.le ha1
  have hr : 0 < rho := by dsimp [rho]; positivity
  have hr1 : rho ≤ 1 := mul_le_one₀ (pow_le_one₀ hd.le hd1) (by positivity) (pow_le_one₀ ha.le ha1)
  have he : 0 < eta := by dsimp [eta]; positivity
  have he1 : eta ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  intro N _ _ hN f hf hnot
  obtain ⟨U, phi, hU, hfreiman, hfourier⟩ := section13_prepared_frequency_graph alpha halpha halpha1 f hf hnot
  have hn : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hn2 : (0 : Real) < (N : Real) ^ 2 := pow_pos hn _
  let beta : Real := (U.card : Real) / (N : Real) ^ 2
  have hdb : delta ≤ beta := (le_div_iff₀ hn2).mpr hU
  have hb : 0 < beta := hd.trans_le hdb
  have hcard : (U.card : Real) = beta * (N : Real) ^ 2 := (div_mul_cancel₀ _ hn2.ne').symm
  have hrb : rho * beta ^ 15 ≤ beta ^ 112 * a ^ 336 := by
    calc
      _ = (delta ^ 97 * beta ^ 15) * a ^ 336 := by dsimp only [rho]; ac_rfl
      _ ≤ (beta ^ 97 * beta ^ 15) * a ^ 336 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hd.le hdb 97) (pow_nonneg hb.le 15)) (pow_nonneg ha.le 336)
      _ = _ := by rw [← pow_add]
  have habundance : rho * beta ^ 15 * (N : Real) ^ 32 ≤ respectedArrangementCount 8 U phi :=
    (mul_le_mul_of_nonneg_right hrb (pow_nonneg hn.le 32)).trans
      (lemma_12_4_holds N beta a f U phi hb ha hf hcard hfourier)
  obtain ⟨A, hAU, hmass, hmostly⟩ := section13_fejer_density_explicit delta rho eta hd hr hr1 he he1 N hN U phi beta hdb hcard habundance
  have hcoef : a ^ (4207554485 : Nat) ≤ ((2 : Real) ^ 77)⁻¹ * rho ^ 3 * eta ^ 3 * beta :=
    (section13_fejer_graph_coefficient ha hahalf).trans
      (mul_le_mul_of_nonneg_left hdb
        (mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hr.le 3)) (pow_nonneg he.le 3)))
  refine ⟨A, phi, (mul_le_mul_of_nonneg_right hcoef hn2.le).trans hmass,
    separatelyFreimanEight_subset hAU hfreiman, ?_, ?_⟩
  · simpa only [MostlyRespectsEight, eta, show (1 / 2 : Real) ^ 44 = (2 : Real) ^ (-(44 : Int)) by norm_num] using hmostly
  · intro z hz
    have ht := hfourier z (hAU hz)
    convert ht using 1
    ring

end LeanProofs.GowersSzemeredi
