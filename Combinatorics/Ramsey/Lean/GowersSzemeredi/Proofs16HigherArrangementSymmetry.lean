import GowersSzemeredi.Proofs16HigherArrangementModel

/-! Reindexing symmetries preserve both the sixteen-endpoint equation
and the cardinality of a family of its eleven-parameter solutions. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

structure HigherArrangementSymmetry (N : Nat) where
  parameters : Equiv.Perm (HigherArrangementParameter N)
  coordinates : Equiv.Perm (Fin 16)
  endpoints : ∀ p j, higherArrangementEndpoints (parameters p) j =
    higherArrangementEndpoints p (coordinates j)
  equation : ∀ f p, HigherArrangementEquation f p →
    HigherArrangementEquation (fun j => f (coordinates j)) (parameters p)

namespace HigherArrangementSymmetry

def refl (N : Nat) : HigherArrangementSymmetry N where
  parameters := Equiv.refl _
  coordinates := Equiv.refl _
  endpoints := fun _ _ => rfl
  equation := fun _ _ h => h

/-- Parameter maps compose in the reverse order from coordinate pullbacks. -/
def trans {N : Nat} (s t : HigherArrangementSymmetry N) : HigherArrangementSymmetry N where
  parameters := s.parameters.trans t.parameters
  coordinates := t.coordinates.trans s.coordinates
  endpoints := fun p j => (t.endpoints (s.parameters p) j).trans (s.endpoints p (t.coordinates j))
  equation := fun f p h => t.equation (fun j => f (s.coordinates j)) (s.parameters p) (s.equation f p h)

def ofInvolutions {N : Nat} (r : HigherArrangementParameter N → HigherArrangementParameter N)
    (c : Fin 16 → Fin 16) (hr : Function.Involutive r) (hc : Function.Involutive c)
    (he : ∀ p j, higherArrangementEndpoints (r p) j = higherArrangementEndpoints p (c j))
    (hv : ∀ v : Fin 16 → ZMod N,
      (v 0-v 1)+(v 2-v 3)+(v 4-v 5)+(v 6-v 7) =
        (v 8-v 9)+(v 10-v 11)+(v 12-v 13)+(v 14-v 15) →
      (v (c 0)-v (c 1))+(v (c 2)-v (c 3))+(v (c 4)-v (c 5))+(v (c 6)-v (c 7)) =
        (v (c 8)-v (c 9))+(v (c 10)-v (c 11))+(v (c 12)-v (c 13))+(v (c 14)-v (c 15))) :
    HigherArrangementSymmetry N where
  parameters := ⟨r,r,hr,hr⟩
  coordinates := ⟨c,c,hc,hc⟩
  endpoints := he
  equation := by
    intro f p h
    dsimp [HigherArrangementEquation] at h ⊢
    simp_rw [he]
    exact hv (fun j => f j (higherArrangementEndpoints p j)) h

end HigherArrangementSymmetry
end LeanProofs.GowersSzemeredi
