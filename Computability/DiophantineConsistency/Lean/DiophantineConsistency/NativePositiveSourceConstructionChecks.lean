import DiophantineConsistency.NativePositiveSourceConstruction

namespace DiophantineConsistency.NativePositiveSourceConstructionChecks

open NativePositiveSourceConstruction NativeOuterSeedConstruction

set_option Elab.async false

-- The exact ordinary multiplier product follows from the exponent, including
-- the endpoint R=u. The order premise cannot simply be dropped.
example : (2^(7-3) : ℕ)*2^3=2^7 :=
  forced_product_of_exponent (by decide) rfl
example (u : ℕ) : (2^(u-u) : ℕ)*2^u=2^u :=
  forced_product_of_exponent (by omega) rfl
example : (2^(3-7) : ℕ)*2^7 ≠ 2^3 := by decide

-- Every actual independent coordinate is in its literal parent slot.
example {p : Fin 4 → ℤ} {u R : ℕ} (d : Data p u R) (s : Seed u R)
    (f i T y : ℤ) :
    parent d s f i T y 0=d.J ∧ parent d s f i T y 1=d.F ∧
    parent d s f i T y 2=d.alpha ∧ parent d s f i T y 3=d.z ∧
    parent d s f i T y 4=f ∧ parent d s f i T y 5=s.h ∧
    parent d s f i T y 6=i ∧ parent d s f i T y 7=T ∧
    parent d s f i T y 8=s.s ∧ parent d s f i T y 9=d.w ∧
    parent d s f i T y 10=s.tau ∧ parent d s f i T y 11=s.eta ∧
    parent d s f i T y 12=s.zeta ∧ parent d s f i T y 13=y ∧
    parent d s f i T y 14=s.gamma := by simp [parent]

-- The negative freshly constructed ordinate is changed only by sign.
example (y : ℤ) (hy : y<0) : 0 < -y ∧ -y=|y| ∧ (-y)^2=y^2 := by
  exact ⟨by omega,(abs_of_neg hy).symm,neg_sq y⟩

-- No first/main/private norm or source zero is supplied to the construction.
-- The same scalar inputs and once-shifted four ports are retained.
example {p : Fin 4 → ℤ} {u R : ℕ} (d : Data p u R) (s : Seed u R)
    (hR : R%4=3) :
    ∃ v : Fin 15 → ℤ, (∀ j,0<v j) ∧ Carrier66.Canonical p v ∧
      Carrier66.value p v=0 ∧ (Carrier66.core p v).rank=R := by
  obtain ⟨c⟩ := exists_construction d s hR
  exact ⟨c.v,c.positive,c.canonical,Carrier66.canonical_zero p c.v c.canonical,c.rank⟩

-- The actual literal 31-variable source, not a replacement residual system.
example {p : Fin 4 → ℤ} {u R : ℕ} (hb : 0<p 0)
    (d : Data p u R) (s : Seed u R) (hR : R%4=3) :
    ∃ x : Fin 31 → ℕ, (∀ j,0<x j) ∧
      (∀ j,SplitCertificate59.sourceRows p (fun k => (x k : ℤ)) j=0) := by
  obtain ⟨x,hx,hs,_⟩ := exists_positive_source hb d s hR
  exact ⟨x,hx,hs⟩

-- The actual fourteen-variable polynomial keeps all five scalar coordinates.
example {p : Fin 4 → ℤ} {u R : ℕ} (hb : 0<p 0)
    (d : Data p u R) (s : Seed u R) (hR : R%4=3) :
    ∃ v : Fin 14 → ℤ, (∀ j,0<v j) ∧
      MvPolynomial.eval v (Carrier65.polynomial p)=0 ∧
      v 0=d.J ∧ v 1=d.F ∧ v 2=d.alpha ∧ v 3=d.z ∧ v 8=d.w :=
  exists_positive_polynomial_zero hb d s hR

-- Population-only entry point constructs BOTH the outer and private seeds.
example {p : Fin 4 → ℤ} {u R : ℕ} (hb : 0<p 0) (d : Data p u R)
    (hu : 0<u) (hp : Jones1982.σ 2 R=3*u+2) (hR : R%4=3) :
    ∃ v : Fin 14 → ℤ, (∀ j,0<v j) ∧
      MvPolynomial.eval v (Carrier65.polynomial p)=0 := by
  obtain ⟨v,hv,hzero,_⟩ := population_positive_polynomial_zero hb d hu hp hR
  exact ⟨v,hv,hzero⟩

#print axioms forced_product_of_exponent
#print axioms parent_pos
#print axioms parent_blocks
#print axioms exists_construction
#print axioms exists_positive_source
#print axioms exists_positive_polynomial_zero
#print axioms population_constructs
#print axioms population_positive_polynomial_zero

end DiophantineConsistency.NativePositiveSourceConstructionChecks
