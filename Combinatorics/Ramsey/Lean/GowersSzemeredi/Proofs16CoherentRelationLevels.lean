import GowersSzemeredi.Proofs16CoherentBridgeSystem
import GowersSzemeredi.Proofs16ColumnRelationSystem

/-! Constant-radius relation levels for coherent frequency families.
The first level uses the original radius; all three symmetries persist. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def coherentRelationRadius (sigma : Real) (i : Nat) : Real := sigma/(6 : Real)^(i-1)

theorem coherentRelationRadius_antitone {sigma : Real} (hs : 0 ≤ sigma) {i j : Nat} (hij : i ≤ j) :
    coherentRelationRadius sigma j ≤ coherentRelationRadius sigma i := by
  exact div_le_div_of_nonneg_left hs (by positivity)
    (pow_le_pow_right₀ (by norm_num) (Nat.sub_le_sub_right hij 1))

def CoherentRelationLevel {N ell : Nat} [NeZero N] (X B : Finset (ZMod N))
    (theta : Fin ell → ZMod N → ZMod N) (F : ZMod N → ZMod N → ZMod N)
    (sigma : Real) (i : Nat) (p q : ZMod N × ZMod N) : Prop :=
  ColumnPairRelated X (fun u => B ∪ Finset.univ.image (fun j => theta j u)) F (coherentRelationRadius sigma i) p q

theorem CoherentRelationLevel.mono {N ell : Nat} [NeZero N]
    {X B : Finset (ZMod N)} {theta : Fin ell → ZMod N → ZMod N}
    {F : ZMod N → ZMod N → ZMod N} {sigma : Real} {i j : Nat} {p q : ZMod N × ZMod N}
    (h : CoherentRelationLevel X B theta F sigma i p q) (hs : 0 ≤ sigma) (hij : i ≤ j) :
    CoherentRelationLevel X B theta F sigma j p q :=
  ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.mono_radius (coherentRelationRadius_antitone hs hij)⟩

theorem CoherentRelationLevel.symm {N ell : Nat} [NeZero N]
    {X B : Finset (ZMod N)} {theta : Fin ell → ZMod N → ZMod N}
    {F : ZMod N → ZMod N → ZMod N} {sigma : Real} {i : Nat} {p q : ZMod N × ZMod N}
    (h : CoherentRelationLevel X B theta F sigma i p q) :
    CoherentRelationLevel X B theta F sigma i q p := ColumnPairRelated.symm h

theorem CoherentRelationLevel.swap {N ell : Nat} [NeZero N]
    {X B : Finset (ZMod N)} {theta : Fin ell → ZMod N → ZMod N}
    {F : ZMod N → ZMod N → ZMod N} {sigma : Real} {i : Nat} {p q : ZMod N × ZMod N}
    (h : CoherentRelationLevel X B theta F sigma i p q) :
    CoherentRelationLevel X B theta F sigma i p.swap q.swap := ColumnPairRelated.swap h

theorem CoherentRelationLevel.cross {N ell : Nat} [NeZero N]
    {X B : Finset (ZMod N)} {theta : Fin ell → ZMod N → ZMod N}
    {F : ZMod N → ZMod N → ZMod N} {sigma : Real} {i : Nat} {p q : ZMod N × ZMod N}
    (h : CoherentRelationLevel X B theta F sigma i p q) :
    CoherentRelationLevel X B theta F sigma i (p.1,q.1) (p.2,q.2) := ColumnPairRelated.cross h

/-- Mixed positive levels compose after their indices are added. -/
theorem CoherentBridgeSystem.mixed_levels {N ell depth i j : Nat} [NeZero N]
    {X B : Finset (ZMod N)} {theta : Fin ell → ZMod N → ZMod N}
    {F : ZMod N → ZMod N → ZMod N} {sigma eta : Real}
    (h : CoherentBridgeSystem B X theta F sigma eta depth) (hs : 0 ≤ sigma)
    (hi : 0 < i) (hj : 0 < j) (hdepth : max (i-1) (j-1) ≤ depth)
    (Z : Finset (ZMod N)) (x y a : ZMod N)
    (hZ : Z ⊆ X) (hmass : eta*N ≤ (Z.card : Real))
    (hx : x ∈ X) (hxa : x+a ∈ X) (hy : y ∈ X) (hya : y+a ∈ X)
    (hza : ∀ z ∈ Z, z+a ∈ X)
    (hbridge : ∀ z ∈ Z,
      CoherentRelationLevel X B theta F sigma i (x+a,x) (z+a,z) ∧
      CoherentRelationLevel X B theta F sigma j (z+a,z) (y+a,y)) :
    CoherentRelationLevel X B theta F sigma (i+j) (x+a,x) (y+a,y) := by
  let m := max (i-1) (j-1)
  have hrad (k : Nat) (hk : k-1 ≤ m) : sigma/(6 : Real)^m ≤ coherentRelationRadius sigma k :=
    div_le_div_of_nonneg_left hs (by positivity) (pow_le_pow_right₀ (by norm_num) hk)
  have hcomp := h m hdepth Z x y a hZ hmass hx hxa hy hya hza (fun z hz =>
    ⟨(hbridge z hz).1.2.2.2.mono_radius (hrad i (le_max_left _ _)),
      (hbridge z hz).2.2.2.2.mono_radius (hrad j (le_max_right _ _))⟩)
  refine ⟨⟨hxa,hx⟩,⟨hya,hy⟩,by simp, hcomp.mono_radius ?_⟩
  rw [div_div,← pow_succ]
  exact div_le_div_of_nonneg_left hs (by positivity)
    (pow_le_pow_right₀ (by norm_num) (by dsimp only [m]; omega))

end LeanProofs.GowersSzemeredi
