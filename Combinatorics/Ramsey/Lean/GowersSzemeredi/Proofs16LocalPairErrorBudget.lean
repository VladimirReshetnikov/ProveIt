import GowersSzemeredi.Proofs16LocalPairSelection

/-! Choose the frequency accuracy before selecting local pairs or chart windows.
The fixed source quadruple and local anchor densities control every loss. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def localPairSelectionError (kappa lambda : Real) : Real := kappa*lambda^8/128

theorem localPairSelectionError_pos {kappa lambda : Real} (hk : 0 < kappa) (hl : 0 < lambda) :
    0 < localPairSelectionError kappa lambda := by unfold localPairSelectionError; positivity

/-- Vertex, repeat and twelve-tuple losses fit half the source mass at this accuracy. -/
theorem local_pair_selection_loss_budget {N : Nat} [NeZero N] {kappa lambda : Real}
    (hk : 0 < kappa) (hl : 0 < lambda) (hl1 : lambda ≤ 1) (hN : 24 ≤ kappa*(N : Real)) :
    (8*localPairSelectionError kappa lambda/lambda^2)*(N : Real)^3+6*(N : Real)^2+
      (16*localPairSelectionError kappa lambda/lambda^8)*(N : Real)^3 ≤ (kappa/2)*(N : Real)^3 := by
  have he4 : 8*localPairSelectionError kappa lambda/lambda^2 = kappa*lambda^6/16 := by
    unfold localPairSelectionError
    field_simp
    ring
  have he12 : 16*localPairSelectionError kappa lambda/lambda^8 = kappa/8 := by
    unfold localPairSelectionError
    field_simp
    ring
  have hp : lambda^6 ≤ 1 := pow_le_one₀ hl.le hl1
  have hfirst : (kappa*lambda^6/16)*(N : Real)^3 ≤ (kappa/16)*(N : Real)^3 := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply div_le_div_of_nonneg_right _ (by norm_num)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hp hk.le
  have hrepeat : 6*(N : Real)^2 ≤ (kappa/4)*(N : Real)^3 := by
    have h := mul_le_mul_of_nonneg_right hN (sq_nonneg (N : Real))
    nlinarith only [h]
  rw [he4,he12]
  have hnonneg : 0 ≤ kappa*(N : Real)^3 := by positivity
  linarith only [hfirst,hrepeat,hnonneg]

/-- Local selection retains half the source quadruple density with an
accuracy fixed from the source and anchor densities, not from later charts. -/
theorem exists_local_pair_selection_half {N : Nat} [NeZero N]
    (S : Finset (ZMod N)) (A : ZMod N → Finset (ZMod N))
    (Q : Finset (Fin 4 → ZMod N)) (Bad4 : Finset (ZMod N × ZMod N × ZMod N))
    (Bad12 : Finset (Fin 11 → ZMod N)) {lambda kappa : Real}
    (hl : 0 < lambda) (hl1 : lambda ≤ 1) (hk : 0 < kappa)
    (hA : ∀ a ∈ S, lambda*(N : Real) ≤ ((A a).card : Real))
    (hQ : ∀ q ∈ Q, q 0+q 1 = q 2+q 3 ∧ ∀ j, q j ∈ S)
    (hmass : kappa*(N : Real)^3 ≤ (Q.card : Real))
    (hBad4 : (Bad4.card : Real) ≤ localPairSelectionError kappa lambda*(N : Real)^3)
    (hBad12 : (Bad12.card : Real) ≤ localPairSelectionError kappa lambda*(N : Real)^11)
    (hN : 24 ≤ kappa*(N : Real)) :
    ∃ (X : Finset (ZMod N)) (c : ZMod N → ZMod N × ZMod N)
      (R : Finset (Fin 4 → ZMod N)),
      X = S \ localCandidateBadVertices S A Bad4 lambda ∧
      (∀ a ∈ X, c a ∈ localCandidateGoodPairs A Bad4 a) ∧
      (∀ q ∈ R, q ∈ Q ∧ Function.Injective q ∧ (∀ j, q j ∈ X) ∧
        twelveOf q (fun j => c (q j)) ∉ Bad12) ∧
      (kappa/2)*(N : Real)^3 ≤ R.card := by
  obtain ⟨X,c,R,hX,hc,hR,hcount⟩ := exists_local_pair_selection S A Q Bad4 Bad12 hl hA hQ hBad4 hBad12
  refine ⟨X,c,R,hX,hc,hR,?_⟩
  have hbudget := local_pair_selection_loss_budget hk hl hl1 hN
  linarith only [hcount,hbudget,hmass]

end LeanProofs.GowersSzemeredi
