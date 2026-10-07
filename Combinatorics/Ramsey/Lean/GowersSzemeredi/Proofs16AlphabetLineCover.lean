import GowersSzemeredi.Proofs16GlobalGraphCover

/-! A finite alphabet gives a constant-line cover on the identity partition.
This elementary certificate does not imply a small multilinear graph cover. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem finiteAlphabet_section16LineCover {N k : Nat} [NeZero N]
    (P : Box N (k + 1)) (hP : P.IsProper)
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N)
    (S : Finset (ZMod N)) (hphi : ∀ z ∈ B, phi z ∈ S)
    {sigma l : Real} (hsigma : 0 ≤ sigma) (hl : l ≤ P.width) :
    Section16LineCover P B phi sigma l S.card := by
  classical
  let e : Fin S.card ≃ {c // c ∈ S} := S.equivFin.symm
  refine ⟨P.carrier, 1, fun _ => P, fun _ => boxInit P,
    fun _ => P.axis (Fin.last k), fun _ _ i _ => (e i).val,
    Finset.Subset.rfl, ?_, ?_, fun _ => hP, fun _ => boxInit_last_product P,
    fun _ => hl, ?_, ?_⟩
  · have hnonneg : (0 : Real) ≤ P.carrier.card := by positivity
    nlinarith
  · constructor
    · intro x
      simp
    · intro i j hij
      exact ((bne_iff_ne.mp hij) (Subsingleton.elim i j)).elim
  · intro u h i
    exact ⟨0, (e i).val, by intros; simp⟩
  · intro u h x hh hxB hxE hxP
    refine ⟨e.symm ⟨phi (appendCoordinate h x), hphi _ hxB⟩, ?_⟩
    simp only [Equiv.apply_symm_apply]

end LeanProofs.GowersSzemeredi
