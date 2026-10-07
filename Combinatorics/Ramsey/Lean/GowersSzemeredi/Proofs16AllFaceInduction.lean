import GowersSzemeredi.Proofs16CoordinateDirections

/-! Restrict simultaneously on every positive-dimensional proper coordinate
face, paying at most one deletion budget per subset of ambient coordinates. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

abbrev ProperCoordinateDirection (d : Nat) :=
  {s : Finset (Fin d) // 0 < s.card ∧ s.card < d}

theorem properCoordinateDirection_card_le (d : Nat) :
    Fintype.card (ProperCoordinateDirection d) ≤ 2 ^ d := by
  calc
    Fintype.card (ProperCoordinateDirection d) ≤ Fintype.card (Finset (Fin d)) :=
      Fintype.card_subtype_le _
    _ = 2 ^ d := by simp

theorem restrict_all_positive_proper_faces (d : Nat)
    (hth : ∀ l, 0 < l → l < d → Theorem162At l) (gamma theta : Real)
    (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1) :
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
      ∀ (B : Finset (Point N d)) (phi : Point N d → ZMod N),
        HasProductProperty B phi gamma →
        ∃ B' : Finset (Point N d), B' ⊆ B ∧
          (B.card : Real) - (2 : Real) ^ d * theta * (N : Real) ^ d ≤ B'.card ∧
          ∀ (l : Nat), 0 < l → l < d → ∀ F : CoordinateFace N d l,
            MultiplyLinearFunction gamma (gamma ^ (-(2 : Int)) * multipleS theta gamma l)
              (F.domain B') (F.pullback phi) := by
  classical
  obtain ⟨N0, hN0⟩ := restrict_finite_parallel_directions
    (I := ProperCoordinateDirection d) d (fun s => s.val.card) (fun s => s.valᶜ.card)
    (fun s => coordinateDirectionSplit s.val)
    (fun s => hth s.val.card s.property.1 s.property.2) gamma theta hg hg1 ht ht1
  refine ⟨N0, ?_⟩
  intro N _ _ hN B phi hprod
  obtain ⟨B', hsub, hcard, hfaces⟩ := hN0 N hN B phi hprod
  refine ⟨B', hsub, ?_, ?_⟩
  · have hcost : (Fintype.card (ProperCoordinateDirection d) : Real) * theta * (N : Real) ^ d ≤
        (2 : Real) ^ d * theta * (N : Real) ^ d := by
      gcongr
      exact_mod_cast properCoordinateDirection_card_le d
    linarith
  · intro l hl hld F
    let s : ProperCoordinateDirection d := ⟨F.direction, by simpa using And.intro hl hld⟩
    obtain ⟨e, z, hmap⟩ := F.parallel_reparametrization
    have hh := F.multiplyLinear_of_reparametrization
      (splitCoordinateFace (coordinateDirectionSplit F.direction) z) e hmap (hfaces s z)
    simpa only [s, CoordinateFace.direction_card] using hh

end LeanProofs.GowersSzemeredi
