import GowersSzemeredi.Proofs16MixedCoordinateDensity

/-! Projection of additive quadruples to their first pair loses at most
one factor of the ambient cardinality, even with repeated coordinates. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem additive_quadruples_pair_card_le {N : Nat} [NeZero N]
    (Q : Finset (Fin 4 → ZMod N)) (E : Finset (ZMod N × ZMod N))
    (hadd : ∀ q ∈ Q, q 0-q 1 = q 2-q 3) (hE : ∀ q ∈ Q, (q 0,q 1) ∈ E) :
    Q.card ≤ E.card*N := by
  have hc : Q.card ≤ (E ×ˢ (Finset.univ : Finset (ZMod N))).card := by
    apply Finset.card_le_card_of_injOn (fun q => ((q 0,q 1),q 2))
    · intro q hq
      exact Finset.mem_product.mpr ⟨hE q hq,Finset.mem_univ _⟩
    · intro q hq p hp he
      have h := Prod.mk.inj he
      have h01 := Prod.mk.inj h.1
      have h3 : q 3 = p 3 := by
        have hq' := hadd q hq
        have hp' := hadd p hp
        linear_combination hq'-hp'-h01.1+h01.2+h.2
      funext i
      fin_cases i
      · exact h01.1
      · exact h01.2
      · exact h.2
      · exact h3
  simpa only [Finset.card_product,Finset.card_univ,ZMod.card] using hc

theorem additive_quadruples_pair_density {N : Nat} [NeZero N]
    (Q : Finset (Fin 4 → ZMod N)) (E : Finset (ZMod N × ZMod N))
    (hadd : ∀ q ∈ Q, q 0-q 1 = q 2-q 3) (hE : ∀ q ∈ Q, (q 0,q 1) ∈ E)
    {delta : Real} (hQ : delta*(N : Real)^3 ≤ Q.card) :
    delta*(N : Real)^2 ≤ E.card := by
  have hc : (Q.card : Real) ≤ (E.card : Real)*N := by
    exact_mod_cast additive_quadruples_pair_card_le Q E hadd hE
  have hn : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  apply le_of_mul_le_mul_right (a := (N : Real)) _ hn
  calc delta*(N : Real)^2*N = delta*(N : Real)^3 := by ring
    _ ≤ (Q.card : Real) := hQ
    _ ≤ _ := hc

end LeanProofs.GowersSzemeredi
