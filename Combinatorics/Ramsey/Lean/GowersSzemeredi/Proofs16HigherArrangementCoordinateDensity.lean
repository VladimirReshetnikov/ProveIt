import GowersSzemeredi.Proofs16HigherArrangementCoordinateRetention

/-! Every endpoint projection of the eleven-parameter arrangement has
fibres of size at most N^10. Dense retained families therefore give
dense coordinate sets uniformly across all sixteen positions. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem higher_arrangements_coordinate_card_le {N : Nat} [NeZero N]
    (Q : Finset (HigherArrangementParameter N)) (E : Finset (ZMod N)) (i : Fin 16)
    (hE : ∀ p ∈ Q, higherArrangementEndpoints p i ∈ E) :
    Q.card ≤ E.card*N^10 := by
  let s := higherArrangementCoordinateSymmetry N i
  let enc (p : HigherArrangementParameter N) := (higherArrangementEndpoints p i,(s.parameters p).1)
  have hc : Q.card ≤ (E ×ˢ (Finset.univ : Finset (HigherArrangementIndex N))).card := by
    apply Finset.card_le_card_of_injOn enc
    · intro p hp
      exact Finset.mem_product.mpr ⟨hE p hp,Finset.mem_univ _⟩
    · intro p hp q hq he
      have he' : higherArrangementEndpoints p i = higherArrangementEndpoints q i ∧
          (s.parameters p).1 = (s.parameters q).1 := by
        simpa only [enc,Prod.mk.injEq] using he
      have hv : (s.parameters p).2+(s.parameters p).1.1 =
          (s.parameters q).2+(s.parameters q).1.1 := by
        change higherArrangementEndpoints (s.parameters p) 0 = higherArrangementEndpoints (s.parameters q) 0
        rw [s.endpoints,s.endpoints]
        simpa only [s,higherArrangementCoordinateSymmetry_zero] using he'.1
      apply s.parameters.injective
      apply Prod.ext he'.2
      have ha := congrArg Prod.fst he'.2
      linear_combination hv-ha
  calc Q.card ≤ _ := hc
    _ = E.card*N^10 := by
      simp only [Finset.card_product,Finset.card_univ,HigherArrangementIndex,Fintype.card_prod,
        Fintype.card_fun,Fintype.card_fin,ZMod.card]
      ring

theorem higher_arrangements_coordinate_density {N : Nat} [NeZero N]
    (Q : Finset (HigherArrangementParameter N)) (E : Finset (ZMod N)) (i : Fin 16)
    (hE : ∀ p ∈ Q, higherArrangementEndpoints p i ∈ E)
    {delta : Real} (hQ : delta*(N : Real)^11 ≤ Q.card) : delta*N ≤ (E.card : Real) := by
  have hc : (Q.card : Real) ≤ (E.card : Real)*(N : Real)^10 := by
    exact_mod_cast higher_arrangements_coordinate_card_le Q E i hE
  have hn : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  apply le_of_mul_le_mul_right (a := (N : Real)^10) _ (by positivity)
  calc delta*N*(N : Real)^10 = delta*(N : Real)^11 := by ring
    _ ≤ (Q.card : Real) := hQ
    _ ≤ _ := hc

end LeanProofs.GowersSzemeredi
