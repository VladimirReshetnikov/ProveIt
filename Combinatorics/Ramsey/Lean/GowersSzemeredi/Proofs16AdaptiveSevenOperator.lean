import GowersSzemeredi.Proofs16BudgetedDenseGraph
import GowersSzemeredi.Proofs16TupleRowCompletion

/-! A dense tuple row configuration produces a proper progression of filled
rows in the seven-operator set. Graph regularity, witness counts, and the
filling error budget are all constructed in the proof. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- Quantitative seven-operator completion from initial dense tuple geometry. -/
theorem exists_adaptive_seven_operator_progression {N Q H : Nat} [NeZero N] [NeZero Q] [NeZero H]
    [Fact N.Prime] {κ : Type*} [Fintype κ] (A : Finset (ZMod N × ZMod N))
    (W F Gamma : Finset (ZMod N)) (L : κ → ZMod N → ZMod N) (a : ZMod N)
    {sigma alpha eta : Real} (hsigma : 0 < sigma)
    (hsigmaMax : sigma ≤ 1 / (8 * Real.pi)) (ha : 0 < alpha)
    (heta : 0 < eta) (hetaQuarter : eta < 1 / 4)
    (hQ : 4 ≤ sigma * Q) (hH : (2 : Real)^(Fintype.card κ) ≤ eta * H)
    (hN : adaptiveGraphModulusBound
      (adaptiveFillingError alpha Q H
        (F.card + Fintype.card κ * Fintype.card κ + 2 * Fintype.card κ)) H
      (F.card + Fintype.card κ * Fintype.card κ + 2 * Fintype.card κ)
      Q (Fintype.card κ) (max Gamma.card F.card) ≤ N)
    (hW : W ⊆ bohr Gamma (sigma / 4))
    (hL : ∀ j, IsFreimanLinearOn (bohr Gamma sigma) (L j))
    (hzero : ∀ j, L j 0 = 0) (hcard : alpha * N ≤ W.card)
    (hgeom : tupleRowGeometry A W F L a eta) :
    let k := Fintype.card κ
    let m := F.card + k * k + 2 * k
    let e := adaptiveFillingError alpha Q H m
    ∃ s : Nat, s ≤ k - Module.finrank (ZMod N) (relationSubmodule (bohr Gamma sigma) L) ∧
    let D := (adaptiveGraphState e H m Q k)^[s] (max Gamma.card F.card)
    let rho := eta / (2 : Real)^s
    ∃ (S V F' U : Finset (ZMod N)) (a' : ZMod N)
      (P : OAI.Erdos3.BohrProgression.CyclicCenteredGAP N),
      Gamma ⊆ S ∧ S.card ≤ D ∧
      bohr S sigma ⊆ bohr Gamma sigma ∧ bohr S (sigma / 4) ⊆ bohr Gamma (sigma / 4) ∧
      V.Nonempty ∧ V ⊆ bohr S (sigma / 4) ∧
      (alpha / (Q : Real)^D) * N ≤ V.card ∧ F ⊆ F' ∧ F'.card ≤ F.card + s * k ∧
      tupleRowGeometry A V F' L a' rho ∧
      (U.card : Real) ≤ 16 / (alpha / (Q : Real)^D)^2 ∧
      P.rank ≤ U.card + 1 ∧ P.Proper ∧ 0 ∈ P.carrier ∧
      (∀ y ∈ P.carrier, -y ∈ P.carrier) ∧ P.carrier ⊆ bohr S sigma ∧
      Real.exp (-(((U.card : Real) + 1) * Real.log (1 + Real.pi) +
        10 * ((U.card : Real) + 1)^2)) * N ≤ P.carrier.card ∧
      ∀ y ∈ P.carrier, ∀ d ∈ bohr (F' ∪ Finset.univ.image (fun j => L j y)) (rho / 4 / 2),
        (d, y) ∈ horDiff (verDiff (verDiff A)) := by
  let k := Fintype.card κ
  let m := F.card + k * k + 2 * k
  let e := adaptiveFillingError alpha Q H m
  obtain ⟨s, hs, S, V, F', a', delta, hGS, hS, hFstate, hfull, hquarter,
      hVne, hV, hVcard, hFF', hFcard, hgeom', hd, hd1, hbox, hbudget⟩ :=
    exists_budgeted_dense_graph A W F Gamma L a hsigma hsigmaMax ha heta hetaQuarter
      hQ hH hN hW hL hzero hcard hgeom
  let D := (adaptiveGraphState e H m Q k)^[s] (max Gamma.card F.card)
  let rho := eta / (2 : Real)^s
  let mu : Real := V.card / N
  have hNpos : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hQpos : (0 : Real) < Q := by exact_mod_cast NeZero.pos Q
  have h4H : (0 : Real) < ((4 * H : Nat) : Real) := by
    have hHpos : (0 : Real) < H := by exact_mod_cast NeZero.pos H
    push_cast; positivity
  have hmu : 0 < mu := div_pos (by exact_mod_cast hVne.card_pos) hNpos
  have hmuCard : (V.card : Real) = mu * N := by dsimp [mu]; rw [div_mul_cancel₀ _ hNpos.ne']
  have hmuLower : alpha / (Q : Real)^D ≤ mu := (le_div_iff₀ hNpos).mpr hVcard
  have hsk : s ≤ k := hs.trans (Nat.sub_le _ _)
  have hrho : 0 < rho := by dsimp [rho]; positivity
  have hrhoH : 1 ≤ rho * H := by
    have hp : (2 : Real)^s ≤ (2 : Real)^k := pow_le_pow_right₀ (by norm_num) hsk
    dsimp only [rho]
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ (by positivity)).mpr (by simpa only [one_mul] using hp.trans hH)
  have hfreq : F'.card + 2 * Fintype.card κ ≤ m := by
    have hskk := Nat.mul_le_mul_right k hsk
    change F'.card ≤ F.card + s * k at hFcard
    dsimp only [m]
    omega
  have hLS : ∀ j, IsFreimanLinearOn (bohr S sigma) (L j) := by
    intro j x₁ x₂ x₃ x₄ h₁ h₂ h₃ h₄ heq
    exact hL j x₁ x₂ x₃ x₄ (hfull h₁) (hfull h₂) (hfull h₃) (hfull h₄) heq
  have hdelta : 0 < delta := (show 0 < (1 / ((4 * H : Nat) : Real)^m) / 2 by positivity).trans_le hd
  have hcell : 4 ≤ rho * ((4 * H : Nat) : Real) := by push_cast; nlinarith only [hrhoH]
  obtain ⟨U, P, hU, hPrank, hPproper, hP0, hPneg, hPS, hPsize, hrows⟩ :=
    proper_progression_tuple_completion (Q := 4 * H) (r := m) A V (bohr S (sigma / 4)) S F'
      L a' hmu hmuCard hV hsigma.le hrho ⟨0, zero_mem_bohr S (by positivity)⟩
      hdelta hd1 (adaptiveFillingError_pos_le ha Q H m D).1.le hV hLS hzero hgeom'
      hbox hfreq hcell hbudget
  refine ⟨s, hs, S, V, F', U, a', P, hGS, hS, hfull, hquarter, hVne, hV, hVcard,
    hFF', hFcard, hgeom', ?_, hPrank, hPproper, hP0, hPneg, hPS, hPsize, hrows⟩
  apply hU.trans
  exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
    (pow_le_pow_left₀ (by positivity) hmuLower 2)

end LeanProofs.GowersSzemeredi
