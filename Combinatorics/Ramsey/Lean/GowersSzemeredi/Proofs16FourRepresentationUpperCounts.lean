import GowersSzemeredi.Proofs16FourRepresentationFlatten

/-! A fixed four-term sum has at most `N^3` representations. This bounds
only the coordinate whose old representative is unused in replacement counts. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem four_difference_representations_card_le {N : Nat} [NeZero N]
    (U : Finset (ZMod N)) (t : ZMod N) : (fourDifferenceRepresentations U t).card ≤ N^3 := by
  have hcard : (fourDifferenceRepresentations U t).card ≤
      (Finset.univ : Finset (ZMod N × ZMod N × ZMod N)).card := by
    apply Finset.card_le_card_of_injOn (fun q => (q.1,q.2.1,q.2.2.1))
    · intro q hq
      exact Finset.mem_univ _
    · intro q hq r hr he
      have h0 := congrArg Prod.fst he
      have h1 := congrArg (fun p : ZMod N × ZMod N × ZMod N => p.2.1) he
      have h2 := congrArg (fun p : ZMod N × ZMod N × ZMod N => p.2.2) he
      have eqQ := (Finset.mem_filter.mp hq).2
      have eqR := (Finset.mem_filter.mp hr).2
      have h3 : q.2.2.2 = r.2.2.2 := by linear_combination -eqQ+eqR+h0-h1+h2
      exact Prod.ext h0 (Prod.ext h1 (Prod.ext h2 h3))
  simpa only [Finset.card_univ,Fintype.card_prod,ZMod.card,pow_succ,pow_zero,Nat.mul_one,Nat.one_mul,Nat.mul_assoc] using hcard

end LeanProofs.GowersSzemeredi
