import GowersSzemeredi.Proofs16ExplicitGraphCutoff
import GowersSzemeredi.Proofs16TupleDensityLower

/-! One sparse-relation certificate controls every admissible pair of
vertical radii, including equal radii and further shrunk profiles. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def DenseBohrGraphProfiles {N ell : Nat} [NeZero N]
    (B C : Finset (ZMod N)) (theta : Fin ell → ZMod N → ZMod N)
    (H m : Nat) (epsilon : Real) : Prop :=
  ∀ nu eta : Real, 0 < nu → nu ≤ eta → eta < 1/4 → 1 ≤ nu*H →
    ∃ delta : Real, (1/(H : Real)^m)/2 ≤ delta ∧ delta ≤ 1 ∧
      boxSum (fun (z : ↥(bohr B eta)) (u : ↥C) =>
        (if (z : ZMod N) ∈ bohr (Finset.univ.image fun i => theta i u) nu
          then (1 : Real) else 0)-delta) ≤
      epsilon^4*((bohr B eta).card : Real)^2*(C.card : Real)^2

theorem denseBohrGraphProfiles_of_sparse_relations {N ell H : Nat}
    [NeZero N] [NeZero H] [Fact N.Prime]
    (B D C : Finset (ZMod N)) (hC : C ⊆ D) (hCne : C.Nonempty)
    (theta : Fin ell → ZMod N → ZMod N) (hzero : ∀ i, theta i 0 = 0)
    (m : Nat) (hm : B.card+2*ell ≤ m) {epsilon : Real} (he : 0 < epsilon)
    (heMax : epsilon ≤ (1/(H : Real)^m)/2)
    (hN : 1/relationProfileSmoothing (epsilon^4) H m ≤ N)
    (hbad : ((boundedBadRelationPairs (fun i : ↥B => (i : ZMod N)) D theta C
      (relationProfileCutoff (epsilon^4) H m)).card : Real) ≤ (epsilon^4/6)*(C.card : Real)^2) :
    DenseBohrGraphProfiles B C theta H m epsilon := by
  have hH : (1 : Real) ≤ H := by exact_mod_cast NeZero.pos H
  have hbeta : 1/(H : Real)^m ≤ 1 := (div_le_one (by positivity)).mpr (one_le_pow₀ hH)
  have heOne : epsilon ≤ 1 := by linarith
  intro nu eta hn hne heq hnuH
  have heta : 0 < eta := hn.trans_le hne
  have hetaH : 1 ≤ eta*(H : Real) := hnuH.trans (mul_le_mul_of_nonneg_right hne (Nat.cast_nonneg H))
  obtain ⟨delta,hd0,hd1,hbox⟩ := tuple_bohr_quasirandom_explicit (Q := H)
    (fun i : ↥B => (i : ZMod N)) D C hC hCne theta hzero m heta.le hn.le heq
    (hne.trans_lt heq) (pow_pos he _) (by simpa using pow_le_pow_left₀ he.le heOne 4)
    hN hetaH (by simpa only [Fintype.card_coe,Fintype.card_fin] using hm) hbad
  have himage : Finset.univ.image (fun i : ↥B => (i : ZMod N)) = B := by ext z; simp
  rw [boxSum_finset_congr (congrArg (fun T => bohr T eta) himage)
    (fun z (u : ↥C) =>
      (if z ∈ bohr (Finset.univ.image fun i => theta i u) nu then (1 : Real) else 0)-delta)] at hbox
  rw [himage] at hbox
  have hd := tuple_bohr_density_lower (Q := H) B C hCne theta m heta.le hne hnuH
    (by simp only [Fintype.card_fin]; omega) he.le hbox
  exact ⟨delta,by linarith,hd1,hbox⟩

end LeanProofs.GowersSzemeredi
