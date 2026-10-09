import GowersSzemeredi.Proofs16CoherentAnchorSelection

/-! A matched left/right anchor quadruple fixes three of the eleven
arrangement parameters. Each quadruple therefore has at most `N^8`
preimages, uniformly over its four possible positions. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def higherArrangementAnchorQuadruple {N : Nat} (p : HigherArrangementParameter N)
    (j : Fin 4) : Fin 4 → ZMod N :=
  ![(higherArrangementEndpointPair p (Fin.castAdd 4 j)).1,
    (higherArrangementEndpointPair p (Fin.castAdd 4 j)).2,
    (higherArrangementEndpointPair p (Fin.natAdd 4 j)).1,
    (higherArrangementEndpointPair p (Fin.natAdd 4 j)).2]

theorem higherArrangementAnchorQuadruple_additive {N : Nat}
    (p : HigherArrangementParameter N) (j : Fin 4) :
    higherArrangementAnchorQuadruple p j 0-higherArrangementAnchorQuadruple p j 1 =
      higherArrangementAnchorQuadruple p j 2-higherArrangementAnchorQuadruple p j 3 := by
  exact higherArrangementPairDifference_sides p j

theorem higherArrangementAnchorQuadruple_symmetry {N : Nat}
    (p : HigherArrangementParameter N) (j : Fin 4) :
    higherArrangementAnchorQuadruple
      ((higherArrangementCoordinateSymmetry N (higherArrangementPairLeft (Fin.castAdd 4 j))).parameters p) 0 =
      higherArrangementAnchorQuadruple p j := by
  let s := higherArrangementCoordinateSymmetry N (higherArrangementPairLeft (Fin.castAdd 4 j))
  change higherArrangementAnchorQuadruple (s.parameters p) 0 = _
  funext i
  fin_cases i <;> dsimp only [higherArrangementAnchorQuadruple,higherArrangementEndpointPair]
  all_goals rw [s.endpoints]
  all_goals fin_cases j <;> rfl

def higherArrangementFirstQuadrupleFree {N : Nat} (p : HigherArrangementParameter N) :
    Fin 8 → ZMod N := ![p.1.2 0,p.1.2 1,p.1.2 2,p.1.2 3,p.1.2 4,p.1.2 6,p.1.2 7,p.1.2 8]

theorem higherArrangementFirstQuadrupleEncoding_injective {N : Nat} :
    Function.Injective (fun p : HigherArrangementParameter N =>
      (higherArrangementAnchorQuadruple p 0,higherArrangementFirstQuadrupleFree p)) := by
  intro p q h
  have hQ := congrArg Prod.fst h
  have hz := congrArg Prod.snd h
  have hu := congrFun hQ 1
  have ha := congrFun hQ 0
  have h5 := congrFun hQ 3
  dsimp [higherArrangementAnchorQuadruple,higherArrangementEndpointPair,
    higherArrangementPairLeft,higherArrangementPairRight,higherArrangementEndpoints] at hu ha h5
  refine Prod.ext (Prod.ext ?_ ?_) hu
  · linear_combination ha-hu
  · funext i
    fin_cases i
    all_goals first | exact h5 | exact congrFun hz 0 | exact congrFun hz 1 |
      exact congrFun hz 2 | exact congrFun hz 3 | exact congrFun hz 4 |
      exact congrFun hz 5 | exact congrFun hz 6 | exact congrFun hz 7

theorem higher_arrangements_anchor_quadruple_card_le {N : Nat} [NeZero N]
    (H : Finset (HigherArrangementParameter N)) (E : Finset (Fin 4 → ZMod N)) (j : Fin 4)
    (hE : ∀ p ∈ H, higherArrangementAnchorQuadruple p j ∈ E) :
    H.card ≤ E.card*N^8 := by
  let s := higherArrangementCoordinateSymmetry N (higherArrangementPairLeft (Fin.castAdd 4 j))
  let enc (p : HigherArrangementParameter N) :=
    (higherArrangementAnchorQuadruple p j,higherArrangementFirstQuadrupleFree (s.parameters p))
  have hc : H.card ≤ (E ×ˢ (Finset.univ : Finset (Fin 8 → ZMod N))).card := by
    apply Finset.card_le_card_of_injOn enc
    · intro p hp
      exact Finset.mem_product.mpr ⟨hE p hp,Finset.mem_univ _⟩
    · intro p hp q hq he
      apply s.parameters.injective
      apply higherArrangementFirstQuadrupleEncoding_injective
      simpa only [higherArrangementAnchorQuadruple_symmetry,enc,s] using he
  simpa only [Finset.card_product,Finset.card_univ,Fintype.card_fun,Fintype.card_fin,ZMod.card] using hc

end LeanProofs.GowersSzemeredi
