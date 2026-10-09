import GowersSzemeredi.Proofs16CommonSliceShift
import GowersSzemeredi.Proofs16PrimeColumnIdentities

/-! Recenter dense column slices at one common source row. The original
row values supply the affine offsets without losing either Freiman identity. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem column_bihomomorphism_add_row {N : Nat} [NeZero N]
    (A : Finset (ZMod N × ZMod N)) (phi : ZMod N × ZMod N → ZMod N)
    (P V : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (s : Real) (t : ZMod N)
    (hVP : V ⊆ P) (hrow : ∀ x ∈ V, (x,t) ∈ A)
    (hphi : IsEBihomomorphism A phi {0})
    (hL : IsEBihomomorphism (columnBohrDomain P T s) (fun p => L p.1 p.2) {0}) :
    IsEBihomomorphism (columnBohrDomain V T s)
      (fun p => L p.1 p.2+phi (p.1,t)) {0} := by
  have hsub : columnBohrDomain V T s ⊆ columnBohrDomain P T s := by
    intro p hp
    obtain ⟨_,hx,hy⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hVP hx,hy⟩
  constructor
  · intro a b c d y heq ha hb hc hd
    have hl := Set.mem_singleton_iff.mp (hL.1 a b c d y heq (hsub ha) (hsub hb) (hsub hc) (hsub hd))
    have hr := Set.mem_singleton_iff.mp (hphi.1 a b c d t heq
      (hrow a (Finset.mem_filter.mp ha).2.1) (hrow b (Finset.mem_filter.mp hb).2.1)
      (hrow c (Finset.mem_filter.mp hc).2.1) (hrow d (Finset.mem_filter.mp hd).2.1))
    apply Set.mem_singleton_iff.mpr
    dsimp at hl ⊢
    linear_combination hl+hr
  · intro x a b c d heq ha hb hc hd
    have hl := Set.mem_singleton_iff.mp (hL.2 x a b c d heq (hsub ha) (hsub hb) (hsub hc) (hsub hd))
    apply Set.mem_singleton_iff.mpr
    dsimp at hl ⊢
    linear_combination hl

/-- Dense pairwise agreement slices yield an actual agreement set after
one vertical shift, with density `delta*lambda^2`. -/
theorem column_slices_shifted_agreement {N : Nat} [NeZero N]
    (A : Finset (ZMod N × ZMod N)) (phi : ZMod N × ZMod N → ZMod N)
    (P : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (D : ZMod N → Finset (ZMod N))
    {s r delta lambda : Real} (hd : 0 ≤ delta) (hl : 0 ≤ lambda)
    (hP : delta*N ≤ (P.card : Real))
    (hD : ∀ x ∈ P, lambda*N ≤ ((D x).card : Real))
    (hDA : ∀ x ∈ P, ∀ a ∈ D x, (x,a) ∈ A)
    (hagree : ∀ x ∈ P, ∀ a ∈ D x, ∀ b ∈ D x,
      a-b ∈ bohr (T x) s ∧ L x (a-b) = phi (x,a)-phi (x,b))
    (hphi : IsEBihomomorphism A phi {0})
    (hL : IsEBihomomorphism (columnBohrDomain P T r) (fun p => L p.1 p.2) {0}) :
    ∃ (t : ZMod N) (V : Finset (ZMod N)) (G : Finset (ZMod N × ZMod N)),
      V ⊆ P ∧ (∀ x ∈ V, (x,t) ∈ A) ∧ G ⊆ columnBohrDomain V T s ∧
      delta*lambda^2*(N : Real)^2 ≤ G.card ∧
      IsEBihomomorphism (columnBohrDomain V T r) (fun p => L p.1 p.2+phi (p.1,t)) {0} ∧
      ∀ p ∈ G, (p.1,p.2+t) ∈ A ∧ L p.1 p.2+phi (p.1,t) = phi (p.1,p.2+t) := by
  obtain ⟨t,F,hF,hmem⟩ := exists_common_slice_shift P D hd hl hP hD
  let V := P.filter (fun x => (x,t) ∈ A)
  let G := F.image (fun p => (p.1,p.2-t))
  have hVP : V ⊆ P := Finset.filter_subset _ _
  have hrow : ∀ x ∈ V, (x,t) ∈ A := fun x hx => (Finset.mem_filter.mp hx).2
  have hGcard : G.card = F.card := by
    apply Finset.card_image_of_injective
    intro p q he
    have hp := Prod.mk.inj he
    exact Prod.ext hp.1 (by linear_combination hp.2)
  refine ⟨t,V,G,hVP,hrow,?_,by simpa only [hGcard] using hF,
    column_bihomomorphism_add_row A phi P V T L r t hVP hrow hphi hL,?_⟩
  · intro p hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hx,ha,ht⟩ := hmem q hq
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      Finset.mem_filter.mpr ⟨hx,hDA q.1 hx t ht⟩,(hagree q.1 hx q.2 ha t ht).1⟩
  · intro p hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hx,ha,ht⟩ := hmem q hq
    simp only [sub_add_cancel]
    refine ⟨hDA q.1 hx q.2 ha,?_⟩
    rw [(hagree q.1 hx q.2 ha t ht).2]
    exact sub_add_cancel _ _

end LeanProofs.GowersSzemeredi
