import GowersSzemeredi.Proofs16HigherArrangementPairMap

/-! Fixing both endpoints of any pair leaves at most nine free
coordinates. This converts retained arrangement density to pair density. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def higherArrangementEndpointPair {N : Nat} (p : HigherArrangementParameter N) (j : Fin 8) :
    ZMod N × ZMod N :=
  (higherArrangementEndpoints p (higherArrangementPairLeft j),
    higherArrangementEndpoints p (higherArrangementPairRight j))

theorem higher_arrangements_pair_card_le {N : Nat} [NeZero N]
    (Q : Finset (HigherArrangementParameter N)) (E : Finset (ZMod N × ZMod N)) (j : Fin 8)
    (hE : ∀ p ∈ Q, higherArrangementEndpointPair p j ∈ E) :
    Q.card ≤ E.card*N^9 := by
  let s := higherArrangementCoordinateSymmetry N (higherArrangementPairLeft j)
  let enc (p : HigherArrangementParameter N) := (higherArrangementEndpointPair p j,(s.parameters p).1.2)
  have hc : Q.card ≤ (E ×ˢ (Finset.univ : Finset (Fin 9 → ZMod N))).card := by
    apply Finset.card_le_card_of_injOn enc
    · intro p hp
      exact Finset.mem_product.mpr ⟨hE p hp,Finset.mem_univ _⟩
    · intro p hp q hq he
      have he' : higherArrangementEndpointPair p j = higherArrangementEndpointPair q j ∧
          (s.parameters p).1.2 = (s.parameters q).1.2 := by
        simpa only [enc,Prod.mk.injEq] using he
      have hleft := congrArg Prod.fst he'.1
      have hright := congrArg Prod.snd he'.1
      have hv : (s.parameters p).2+(s.parameters p).1.1 =
          (s.parameters q).2+(s.parameters q).1.1 := by
        change higherArrangementEndpoints (s.parameters p) 0 = higherArrangementEndpoints (s.parameters q) 0
        rw [s.endpoints,s.endpoints]
        simpa only [s,higherArrangementCoordinateSymmetry_zero,higherArrangementEndpointPair] using hleft
      have hb : (s.parameters p).2 = (s.parameters q).2 := by
        change higherArrangementEndpoints (s.parameters p) 1 = higherArrangementEndpoints (s.parameters q) 1
        rw [s.endpoints,s.endpoints]
        simpa only [s,higherArrangementCoordinateSymmetry_pair_right,higherArrangementEndpointPair] using hright
      apply s.parameters.injective
      refine Prod.ext (Prod.ext ?_ he'.2) hb
      linear_combination hv-hb
  simpa only [Finset.card_product,Finset.card_univ,Fintype.card_fun,Fintype.card_fin,ZMod.card] using hc

theorem higher_arrangements_pair_density {N : Nat} [NeZero N]
    (Q : Finset (HigherArrangementParameter N)) (E : Finset (ZMod N × ZMod N)) (j : Fin 8)
    (hE : ∀ p ∈ Q, higherArrangementEndpointPair p j ∈ E)
    {delta : Real} (hQ : delta*(N : Real)^11 ≤ Q.card) : delta*(N : Real)^2 ≤ E.card := by
  have hc : (Q.card : Real) ≤ (E.card : Real)*(N : Real)^9 := by
    exact_mod_cast higher_arrangements_pair_card_le Q E j hE
  have hn : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  apply le_of_mul_le_mul_right (a := (N : Real)^9) _ (by positivity)
  calc delta*(N : Real)^2*(N : Real)^9 = delta*(N : Real)^11 := by ring
    _ ≤ (Q.card : Real) := hQ
    _ ≤ _ := hc

end LeanProofs.GowersSzemeredi
