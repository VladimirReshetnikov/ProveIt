import GowersSzemeredi.Proofs16MatchingKeys

/-! Cauchy--Schwarz gives many equal-key pairs without discarding
multiplicities of the original indexed configurations. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem card_sq_le_keyMatchingCount {X I : Type*} [Fintype I] [DecidableEq I]
    (Q : Finset X) (key : X → I) :
    Q.card^2 ≤ keyMatchingCount Q Q key key*Fintype.card I := by
  have hsum : (∑ i : I, (Q.filter fun q => key q = i).card) = Q.card := by
    simpa only [Finset.mem_univ,Finset.filter_true] using
      Finset.sum_card_fiberwise_eq_card_filter Q Finset.univ key
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (R := Nat) Finset.univ
    (fun i => (Q.filter fun q => key q = i).card) (fun _ => 1)
  simpa only [mul_one,hsum,one_pow,Finset.sum_const,Finset.card_univ,smul_eq_mul,
    ← keyMatchingCount_eq_sum,sq] using hcs

end LeanProofs.GowersSzemeredi
