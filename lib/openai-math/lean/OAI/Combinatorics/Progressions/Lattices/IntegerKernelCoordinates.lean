import OAI.Combinatorics.Progressions.Estimates.LinearQuotientCoverAverage

namespace OAI

section

namespace Erdos3

def nsmulKernelCongr {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (e : G ≃+ H) (d : ℕ) :
    (nsmulAddMonoidHom (α := G) d).ker ≃+
      (nsmulAddMonoidHom (α := H) d).ker where
  toFun x := ⟨e x.val, by
    change d • e x.val = 0
    rw [← map_nsmul, show d • x.val = 0 from x.property, map_zero]⟩
  invFun y := ⟨e.symm y.val, by
    change d • e.symm y.val = 0
    rw [← map_nsmul, show d • y.val = 0 from y.property, map_zero]⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.val)
  right_inv y := Subtype.ext (e.apply_symm_apply y.val)
  map_add' x y := Subtype.ext (e.map_add x.val y.val)

theorem nsmulKernelCongr_val {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (e : G ≃+ H) (d : ℕ) (x : (nsmulAddMonoidHom (α := G) d).ker) :
    (nsmulKernelCongr e d x).val = e x.val := rfl

def nsmulKernelPiEquiv {I : Type*} (G : I → Type*) [∀ i, AddCommGroup (G i)]
    (d : ℕ) : (nsmulAddMonoidHom (α := ∀ i, G i) d).ker ≃+
      ∀ i, (nsmulAddMonoidHom (α := G i) d).ker where
  toFun x i := ⟨x.val i, congrFun x.property i⟩
  invFun y := ⟨fun i => (y i).val, funext fun i => (y i).property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

theorem nsmulKernelPiEquiv_val {I : Type*} (G : I → Type*) [∀ i, AddCommGroup (G i)]
    (d : ℕ) (x : (nsmulAddMonoidHom (α := ∀ i, G i) d).ker) (i : I) :
    (nsmulKernelPiEquiv G d x i).val = x.val i := rfl

end Erdos3

end

end OAI
