import GowersSzemeredi.Proofs16SinglePieceSpectrum
import GowersSzemeredi.Proofs16EmbeddedLift
import GowersSzemeredi.Proofs16Translations
import GowersSzemeredi.Proofs16SingletonPartition
import GowersSzemeredi.Proofs16LiftAllScales

/-! Basic facts about local piece providers (Notes L.1): the density `liftLastC`
after one unused coordinate, the injectivity of the points-to-pairs map
(`initLast_injective`), `LocalPieceFor.congr`, and finite sums of multilinear
maps (`IsMultilinear.finset_sum`).

The calculus of providers (transport, translation, reindexing and the
unused-coordinate lift `LocalPieceFor.lift_last`) is in
`Proofs16PieceCalculusSide`, outside the final route. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- The density after one unused coordinate. -/
def liftLastC (c : Real → Real) (theta : Real) : Real :=
  theta / 2 * c (theta / 2)

/-- The points-to-pairs map is injective. -/
theorem initLast_injective {N d : Nat} :
    Function.Injective fun z : Point N (d + 1) => (section16Init z, section16Last z) := by
  intro z z' h
  simp only [Prod.mk.injEq] at h
  have hz : z = Fin.snoc (section16Init z) (section16Last z) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [section16Last]
    · simp [section16Init]
  have hz' : z' = Fin.snoc (section16Init z') (section16Last z') := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [section16Last]
    · simp [section16Init]
  rw [hz, hz', h.1, h.2]

/-- Providers respect equal domains and agreeing functions. -/
theorem LocalPieceFor.congr {N d : Nat} [NeZero N] {c : Real → Real} {w : Real → Nat → Nat}
    {Dom Dom' : Finset (Point N d)} {g g' : Point N d → ZMod N}
    (h : LocalPieceFor c w Dom g) (hDom : Dom' = Dom) (hg : ∀ x, g' x = g x) :
    LocalPieceFor c w Dom' g' := by
  subst hDom
  have hfun : g' = g := funext hg
  subst hfun
  exact h

/-- Finite sums of multilinear maps are multilinear. -/
theorem IsMultilinear.finset_sum {N n : Nat} {ι : Type*} (s : Finset ι)
    (f : ι → Point N n → ZMod N) (hf : ∀ i ∈ s, IsMultilinear (f i)) :
    IsMultilinear (fun x => ∑ i ∈ s, f i x) := by
  induction s using Finset.induction_on with
  | empty => simpa using (isMultilinear_constant (N := N) (k := n) 0)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

end LeanProofs.GowersSzemeredi
