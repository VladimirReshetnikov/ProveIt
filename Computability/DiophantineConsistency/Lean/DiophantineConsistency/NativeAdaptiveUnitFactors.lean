import DiophantineConsistency.NativePellBootstrap

/-! Integer unit extraction for the four literal adaptive carrier factors.
All parameters are arbitrary signed integers. The discriminant and q-cubic
multiplier exclude negative units by finite modulo4 computations. No Pell
classification, source restoration, current ports or HA theorem is assumed. -/
set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.NativeAdaptiveUnitFactors

def firstFactor (q Z N : ℤ) : ℤ := 1+Z^2-(q^3*(q-1))^2*N
def mainFactor (U a c D : ℤ) : ℤ := 1+D^2-U^2*(1+(a^2+4*a+3)*c^2)
def strongFactor (a f I : ℤ) : ℤ := 1+I^2-(a^2+4*a+3)*(f^2-1)
def auxFactor (a f V y : ℤ) : ℤ :=
  (a^2+4*a+3)*(f^2-1)*V^2+(1-(a^2+4*a+3)*(f^2-1))*y^2

theorem first_ne_neg_one (q Z N : ℤ) : firstFactor q Z N ≠ -1 := by
  intro h
  have hm := congrArg (fun z : ℤ => (z : ZMod 4)) h
  unfold firstFactor at hm
  push_cast at hm
  have bad : ∀ q Z N : ZMod 4, 1+Z^2-(q^3*(q-1))^2*N ≠ -1 := by decide
  exact bad _ _ _ hm

theorem main_ne_neg_one (U a c D : ℤ) : mainFactor U a c D ≠ -1 := by
  intro h
  have hm := congrArg (fun z : ℤ => (z : ZMod 4)) h
  unfold mainFactor at hm
  push_cast at hm
  have bad : ∀ U a c D : ZMod 4, 1+D^2-U^2*(1+(a^2+4*a+3)*c^2) ≠ -1 := by decide
  exact bad _ _ _ _ hm

theorem strong_ne_neg_one (a f I : ℤ) : strongFactor a f I ≠ -1 := by
  intro h
  have hm := congrArg (fun z : ℤ => (z : ZMod 4)) h
  unfold strongFactor at hm
  push_cast at hm
  have bad : ∀ a f I : ZMod 4, 1+I^2-(a^2+4*a+3)*(f^2-1) ≠ -1 := by decide
  exact bad _ _ _ hm

theorem aux_ne_neg_one (a f V y : ℤ) : auxFactor a f V y ≠ -1 := by
  intro h
  have hm := congrArg (fun z : ℤ => (z : ZMod 4)) h
  unfold auxFactor at hm
  push_cast at hm
  have bad : ∀ a f V y : ZMod 4,
      (a^2+4*a+3)*(f^2-1)*V^2+(1-(a^2+4*a+3)*(f^2-1))*y^2 ≠ -1 := by decide
  exact bad _ _ _ _ hm

private theorem first_unit {x y : ℤ} (h : x*y=1) (hx : x≠-1) : x=1 :=
  (Int.eq_one_or_neg_one_of_mul_eq_one h).resolve_right hx

/-- Every literal factor is1; a signed product cannot conceal negative units. -/
theorem product_one_iff (q Z N U a c D f I V y : ℤ) :
    firstFactor q Z N*mainFactor U a c D*auxFactor a f V y*strongFactor a f I=1 ↔
      firstFactor q Z N=1 ∧ mainFactor U a c D=1 ∧
        auxFactor a f V y=1 ∧ strongFactor a f I=1 := by
  constructor
  · intro h
    have h1 : firstFactor q Z N=1 := first_unit
      (by simpa only [mul_assoc] using h) (first_ne_neg_one q Z N)
    rw [h1,one_mul] at h
    have h2 : mainFactor U a c D=1 := first_unit
      (by simpa only [mul_assoc] using h) (main_ne_neg_one U a c D)
    rw [h2,one_mul] at h
    have h3 : auxFactor a f V y=1 := first_unit h (aux_ne_neg_one a f V y)
    rw [h3,one_mul] at h
    exact ⟨h1,h2,h3,h⟩
  · rintro ⟨h1,h2,h3,h4⟩
    rw [h1,h2,h3,h4]
    norm_num

end DiophantineConsistency.NativeAdaptiveUnitFactors
