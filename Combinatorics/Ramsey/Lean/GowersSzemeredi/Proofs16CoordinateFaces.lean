import GowersSzemeredi.Section16

/-! Coordinate-face transport for the inductive dichotomy in Lemma 16.4.
The product property depends only on the partial function and is inherited
by every coordinate cross-section. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

theorem CoordinateFace.map_injective {N d l : Nat} (F : CoordinateFace N d l) :
    Function.Injective F.map := by
  intro x y hxy
  funext i
  have h := congrFun hxy (F.free i)
  simpa only [F.map_free] using h

theorem CoordinateFace.map_replaceCoordinate {N d l : Nat} (F : CoordinateFace N d l)
    (x : Point N l) (j : Fin l) (a : ZMod N) :
    F.map (replaceCoordinate x j a) = replaceCoordinate (F.map x) (F.free j) a := by
  classical
  funext i
  by_cases hi : ∃ t, F.free t = i
  · obtain ⟨t, rfl⟩ := hi
    simp [replaceCoordinate, Function.update_apply, F.map_free, F.free.injective.eq_iff]
  · have hout : ∀ t, F.free t ≠ i := by simpa using hi
    rw [F.map_fixed _ i hout]
    rw [replaceCoordinate, Function.update_of_ne (hout j).symm, F.map_fixed _ i hout]

@[simp] theorem CoordinateFace.mem_domain {N d l : Nat} [NeZero N]
    (F : CoordinateFace N d l) (B : Finset (Point N d)) (x : Point N l) :
    x ∈ F.domain B ↔ F.map x ∈ B := by
  classical
  simp [CoordinateFace.domain]

theorem CoordinateFace.domain_mono {N d l : Nat} [NeZero N]
    (F : CoordinateFace N d l) {B C : Finset (Point N d)} (hBC : B ⊆ C) :
    F.domain B ⊆ F.domain C := by
  intro x hx
  exact (F.mem_domain C x).mpr (hBC ((F.mem_domain B x).mp hx))

theorem weightedSimultaneousAdditiveEnergy_congr_on {N p : Nat} [NeZero N]
    (E : Finset (ZMod N)) (theta : ZMod N → Real)
    (psi chi : Fin p → ZMod N → ZMod N)
    (h : ∀ i x, x ∈ E → psi i x = chi i x) :
    weightedSimultaneousAdditiveEnergy E theta psi =
      weightedSimultaneousAdditiveEnergy E theta chi := by
  classical
  unfold weightedSimultaneousAdditiveEnergy
  apply Finset.sum_congr rfl
  intro q _
  by_cases hq : ∀ t, q t ∈ E
  · have heq (i : Fin p) : (fun t => psi i (q t)) = (fun t => chi i (q t)) :=
      funext fun t => h i (q t) (hq t)
    simp only [hq]
    simp_rw [heq]
  · simp [hq]

theorem HasProductProperty.mono {N k : Nat} [NeZero N]
    {B C : Finset (Point N k)} {phi : Point N k → ZMod N} {gamma : Real}
    (h : HasProductProperty B phi gamma) (hCB : C ⊆ B) : HasProductProperty C phi gamma := by
  intro p j y E theta htheta hE
  exact h p j y E theta htheta (fun i x hx => hCB (hE i x hx))

theorem HasProductProperty.congr_on {N k : Nat} [NeZero N]
    {B : Finset (Point N k)} {phi psi : Point N k → ZMod N} {gamma : Real}
    (h : HasProductProperty B phi gamma) (heq : ∀ x, x ∈ B → phi x = psi x) :
    HasProductProperty B psi gamma := by
  intro p j y E theta htheta hE
  have hh := h p j y E theta htheta hE
  rw [weightedSimultaneousAdditiveEnergy_congr_on E theta
    (fun i => coordinateRestriction phi (y i) j)
    (fun i => coordinateRestriction psi (y i) j)
    (fun i x hx => heq _ (hE i x hx))] at hh
  exact hh

theorem HasProductProperty.coordinateFace {N d l : Nat} [NeZero N]
    {B : Finset (Point N d)} {phi : Point N d → ZMod N} {gamma : Real}
    (h : HasProductProperty B phi gamma) (F : CoordinateFace N d l) :
    HasProductProperty (F.domain B) (F.pullback phi) gamma := by
  intro p j y E theta htheta hE
  have hh := h p (F.free j) (fun i => F.map (y i)) E theta htheta (by
    intro i x hx
    rw [← F.map_replaceCoordinate]
    exact (F.mem_domain B _).mp (hE i x hx))
  have hfun : (fun i : Fin p => coordinateRestriction (F.pullback phi) (y i) j) =
      (fun i : Fin p => coordinateRestriction phi (F.map (y i)) (F.free j)) := by
    funext i x
    change phi (F.map (replaceCoordinate (y i) j x)) = _
    rw [F.map_replaceCoordinate]
    rfl
  rw [hfun]
  exact hh

theorem partialGraph_relationProductProperty {N k : Nat} [NeZero N]
    {B : Finset (Point N k)} {phi : Point N k → ZMod N} {gamma : Real}
    (h : HasProductProperty B phi gamma) : RelationProductProperty gamma (partialGraph B phi) := by
  classical
  intro C psi hgraph
  have hdata (x : Point N k) (hx : x ∈ C) : x ∈ B ∧ phi x = psi x := by
    obtain ⟨y, hy, heq⟩ := Finset.mem_image.mp (hgraph x hx)
    have hyx := congrArg Prod.fst heq
    dsimp at hyx
    subst y
    exact ⟨hy, congrArg Prod.snd heq⟩
  exact (h.mono (fun x hx => (hdata x hx).1)).congr_on (fun x hx => (hdata x hx).2)

end LeanProofs.GowersSzemeredi
