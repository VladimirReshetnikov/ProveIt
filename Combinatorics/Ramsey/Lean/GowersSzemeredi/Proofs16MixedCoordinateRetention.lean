import GowersSzemeredi.Proofs16MixedConfigurationRetention

/-! Symmetries of the difference equation allow the retention argument
at any of the four coordinates. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def mixedCoordinatePermutation (i : Fin 4) : Equiv.Perm (Fin 4) :=
  match i.val with
  | 0 => Equiv.refl _
  | 1 => ⟨![1,0,3,2],![1,0,3,2],by intro j; fin_cases j <;> rfl,by intro j; fin_cases j <;> rfl⟩
  | 2 => ⟨![2,3,0,1],![2,3,0,1],by intro j; fin_cases j <;> rfl,by intro j; fin_cases j <;> rfl⟩
  | _ => ⟨![3,2,1,0],![3,2,1,0],by intro j; fin_cases j <;> rfl,by intro j; fin_cases j <;> rfl⟩

theorem mixedCoordinatePermutation_zero (i : Fin 4) : mixedCoordinatePermutation i 0 = i := by
  fin_cases i <;> rfl

theorem mixed_relation_reindex {N : Nat} (q : Fin 4 → ZMod N)
    (h : q 0-q 1 = q 2-q 3) (i : Fin 4) :
    q (mixedCoordinatePermutation i 0)-q (mixedCoordinatePermutation i 1) =
      q (mixedCoordinatePermutation i 2)-q (mixedCoordinatePermutation i 3) := by
  fin_cases i
  · exact h
  · change q 1-q 0 = q 3-q 2
    linear_combination -h
  · exact h.symm
  · change q 3-q 2 = q 1-q 0
    linear_combination h

/-- A dense mixed family retains many configurations after extracting
an order-eight Freiman piece at any chosen coordinate. -/
theorem mixed_configurations_retain_coordinate {N : Nat} [NeZero N] [Fact N.Prime]
    (f : Fin 4 → ZMod N → ZMod N) (Q : Finset (Fin 4 → ZMod N))
    (hQ : Q ⊆ mixedColumnQuadruples Finset.univ f)
    {delta : Real} (hdelta : 0 < delta) (hcount : delta*(N : Real)^3 ≤ Q.card) (i : Fin 4) :
    ∃ (E : Finset (ZMod N)) (R : Finset (Fin 4 → ZMod N)),
      E ⊆ Q.image (fun q => q i) ∧ R ⊆ Q ∧
      (∀ q ∈ R, q i ∈ E) ∧ FreimanHom 8 E (f i) ∧
      (2 : Real)^(-(1882 : Real))*((delta/2)^4)^1164*N ≤ E.card ∧
      mixedConfigurationRetention delta*(N : Real)^3 ≤ R.card := by
  let e := mixedCoordinatePermutation i
  let reindex (a : Equiv.Perm (Fin 4)) (q : Fin 4 → ZMod N) := fun j => q (a j)
  have hinj (a : Equiv.Perm (Fin 4)) : Function.Injective (reindex a) := by
    intro q r h
    funext j
    have h' := congrFun h (a.symm j)
    simpa only [reindex,Equiv.apply_symm_apply] using h'
  let Q' := Q.image (reindex e)
  let g := fun j => f (e j)
  have hQ' : Q' ⊆ mixedColumnQuadruples Finset.univ g := by
    intro q hq
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨_,_,hd,hv⟩ := Finset.mem_filter.mp (hQ ha)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,Finset.mem_univ _,
      mixed_relation_reindex a hd i,mixed_relation_reindex (fun j => f j (a j)) hv i⟩
  have hcount' : delta*(N : Real)^3 ≤ Q'.card := by
    simpa only [Q',Finset.card_image_of_injective _ (hinj e)] using hcount
  obtain ⟨E,R',hEQ',hRQ',hcoord,hF,hE,hR⟩ :=
    mixed_configurations_retain_freiman_piece g Q' hQ' hdelta hcount'
  let R := R'.image (reindex e.symm)
  have hRcard : R.card = R'.card := Finset.card_image_of_injective _ (hinj e.symm)
  have hrefl (q : Fin 4 → ZMod N) : reindex e.symm (reindex e q) = q := by
    funext j
    exact congrArg q (e.apply_symm_apply j)
  have hRsub : R ⊆ Q := by
    intro q hq
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨b,hb,hba⟩ := Finset.mem_image.mp (hRQ' ha)
    rw [← hba,hrefl]
    exact hb
  have hEsub : E ⊆ Q.image (fun q => q i) := by
    intro x hx
    obtain ⟨a,ha,hax⟩ := Finset.mem_image.mp (hEQ' hx)
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp ha
    exact Finset.mem_image.mpr ⟨b,hb,by simpa only [reindex,e,mixedCoordinatePermutation_zero] using hax⟩
  refine ⟨E,R,hEsub,hRsub,?_,?_,hE,?_⟩
  · intro q hq
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hq
    have he0 : e.symm i = 0 := e.symm_apply_eq.mpr (mixedCoordinatePermutation_zero i).symm
    simpa only [reindex,he0] using hcoord a ha
  · simpa only [g,e,mixedCoordinatePermutation_zero] using hF
  · simpa only [hRcard] using hR

end LeanProofs.GowersSzemeredi
