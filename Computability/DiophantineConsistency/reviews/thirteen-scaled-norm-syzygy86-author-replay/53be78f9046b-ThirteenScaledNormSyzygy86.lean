import DiophantineConsistency.ThirteenSecondFirstNormCorrections

/-! A scaled first/main-norm syzygy with the same entire positive zero set.
The separate integer-leaf audit pays178 operations and proves degree86.
No polynomial equality to the parent, signed-domain extension, internal
consistency proof, or operation/degree minimality is asserted. -/
set_option Elab.async false
namespace DiophantineConsistency.ThirteenScaledNormSyzygy86
open ThirteenCarrierSoundness
variable {A B : Type*} [CommRing A] [CommRing B]

def scale (p : Fin 4 → A) (v : Fin 13 → A) : A := (data p v).k-4*v 12

def syzygy (p : Fin 4 → A) (v : Fin 13 → A) : A :=
  let d := data p v
  8*v 12*(d.P-1)+(d.k*d.Y)*(d.Q-1)

def coefficient (p : Fin 4 → A) (v : Fin 13 → A) : A :=
  let d := data p v
  let K := d.k*d.Y
  let Gc := p 1*d.C-v 1
  let g := d.k*v 6*d.q^2
  let u := d.X*d.rank
  let z := v 5*K
  let e := u-z
  let h := G p v-d.q*Gc
  let L1 := d.C*e*(2*d.X*z+d.f^2*(3*u-z)) +
    2*d.f^2*(v 5)^2*d.C*d.X*(K*d.X*v 9+g^2)-4*d.f^2*Gc*z^2
  let L2 := d.C*K*d.X*u +
    h*(-2*z*e+d.f^2*(d.rank*(4*z-3*u)-2*v 5*z*d.X*v 9)) +
    d.f^2*v 5*z*g*(2*Gc-d.C)
  16*(d.f^2*v 5)^2*d.C*(L1+2*L2)

def syzygyCoefficient (p : Fin 4 → A) (v : Fin 13 → A) : A :=
  let d := data p v
  let Gc := p 1*d.C-v 1
  let z := v 5*(d.k*d.Y)
  8*b p v*d.f^2*(d.f^2*v 5)^2*z^2*Gc*(b p v*Gc+d.C)

def auxiliary (p : Fin 4 → A) (v : Fin 13 → A) : A :=
  scale p v*(ThirteenGroupedSquares96.auxiliary p v -
    (ThirteenSecondFirstNormCorrections.coefficient88 p v+coefficient p v)*((data p v).P-1)) -
    syzygyCoefficient p v*syzygy p v

def value (p : Fin 4 → A) (v : Fin 13 → A) : A :=
  let d := data p v
  (d.P*d.Q-1)^2+(Carrier65.strong d-1)^2+(auxiliary p v-scale p v)^2

/-- The scale is recovered from the main unit alone, independently of any
first/auxiliary/strong unit or native interpretation. -/
theorem main_unit_scale_pos (X Y k eta gamma : ℤ)
    (hX : 2 ≤ X) (hY : 2 ≤ Y) (he : 0 < eta) (hek : eta < k) (hg : 0 < gamma)
    (hQ : (X+((X+1)*Y)*(k*Y+eta)+gamma*(4*((X+1)*Y)+3))^2 -
      (((X+1)*Y)^2+(4*((X+1)*Y)+3))*(k*Y+eta)^2 = 1) :
    0 < k-4*gamma := by
  let a := (X+1)*Y
  let c := k*Y+eta
  let H := 4*a+3
  have ha : 0 < a := by dsimp [a]; positivity
  have hk : 0 < k := lt_trans he hek
  have hc : 0 < c := by dsimp [c]; positivity
  have hH : 0 < H := by dsimp [H]; positivity
  by_contra hn
  have hk4 : k ≤ 4*gamma := by omega
  have hgeom : 2*(Y+1) ≤ a := by
    dsimp [a]
    nlinarith [mul_nonneg (show 0 ≤ X-2 by omega) (show 0 ≤ Y by omega)]
  have hc1 : c < k*(Y+1) := by dsimp [c]; nlinarith only [hek]
  have hc2 : k*(Y+1) ≤ 4*gamma*(Y+1) :=
    mul_le_mul_of_nonneg_right hk4 (by omega)
  have hc3 : 4*gamma*(Y+1) ≤ 2*gamma*a := by
    nlinarith only [mul_nonneg (show 0 ≤ gamma by omega) (sub_nonneg.mpr hgeom)]
  have hca : c < 2*gamma*a := lt_of_lt_of_le (lt_of_lt_of_le hc1 hc2) hc3
  have hb : 2 ≤ X+gamma*H := by nlinarith [mul_pos hg hH]
  have ht : 0 < H*c*(2*a*gamma-c) :=
    mul_pos (mul_pos hH hc) (by nlinarith only [hca])
  have hm : 0 < 2*a*c*X := by positivity
  have hnrm : (X+gamma*H)^2+2*a*c*X+H*c*(2*a*gamma-c)=1 := by
    calc
      _ = (X+a*c+gamma*H)^2-(a^2+H)*c^2 := by ring
      _ = 1 := hQ
  nlinarith only [hb,ht,hm,hnrm]

theorem scale_pos_of_main (p : Fin 4 → ℤ) (v : Fin 13 → ℤ)
    (hb : 0 < p 0) (hv : ∀ j, 0 < v j) (hQ : (data p v).Q=1) :
    0 < scale p v := by
  let d := data p v
  have hp := parent_pos p v hb hv (z := 1) (y := 1) (by norm_num) (by norm_num)
  have hq : 2 ≤ d.q := Carrier65.q_ge_two p (parent p v 1 1) hb hp
  have hq3 : (8 : ℤ) ≤ d.q^3 := by
    have hh := pow_le_pow_left₀ (show (0 : ℤ) ≤ 2 by norm_num) hq (n := 3)
    norm_num at hh
    exact hh
  have hx : 2 ≤ d.X := by
    change 2 ≤ v 7*d.q
    have hw : 1 ≤ v 7 := by have := hv 7; omega
    nlinarith [mul_nonneg (sub_nonneg.mpr hw) (show 0 ≤ d.q by omega)]
  have hy : 2 ≤ d.Y := by
    change 2 ≤ v 6*d.q^3
    have hs : 1 ≤ v 6 := by have := hv 6; omega
    nlinarith [mul_nonneg (sub_nonneg.mpr hs) (show 0 ≤ d.q^3 by omega)]
  have hek : v 9 < d.k := by
    change v 9 < v 9+v 10
    have := hv 10
    omega
  have ha : d.a=(d.X+1)*d.Y := by
    change d.X*d.Y+d.Y=(d.X+1)*d.Y
    ring
  change (d.X+d.a*(d.k*d.Y+v 9)+v 12*(4*d.a+3))^2 -
    (d.a^2+(4*d.a+3))*(d.k*d.Y+v 9)^2=1 at hQ
  rw [ha] at hQ
  exact main_unit_scale_pos d.X d.Y d.k (v 9) (v 12) hx hy (hv 9) hek (hv 12) hQ

/-- Three squared integer residuals vanish separately; no sign of the
corrected auxiliary or its scale is assumed. -/
theorem residuals_zero_iff (P Q Z U A : ℤ) :
    (P*Q-1)^2+(Z-1)^2+(U-A)^2=0 ↔ P*Q=1 ∧ Z=1 ∧ U=A := by
  constructor
  · intro h
    have hp : (P*Q-1)^2=0 := by nlinarith [sq_nonneg (Z-1),sq_nonneg (U-A)]
    have hz : (Z-1)^2=0 := by nlinarith [sq_nonneg (P*Q-1),sq_nonneg (U-A)]
    have hu : (U-A)^2=0 := by nlinarith [sq_nonneg (P*Q-1),sq_nonneg (Z-1)]
    exact ⟨by nlinarith [sq_eq_zero_iff.mp hp],by nlinarith [sq_eq_zero_iff.mp hz],
      sub_eq_zero.mp (sq_eq_zero_iff.mp hu)⟩
  · rintro ⟨hp,hz,hu⟩; simp [hp,hz,hu]

private theorem units (P Q : ℤ) (hP : P ≠ -1) (_hQ : Q ≠ -1) (h : P*Q=1) :
    P=1 ∧ Q=1 := by
  have hp := (Int.isUnit_iff.mp (IsUnit.of_mul_eq_one_right Q (by simpa only [mul_comm] using h))).resolve_right hP
  exact ⟨hp,by simpa only [hp,one_mul] using h⟩

/-- Both maps are the identity on every positive assignment. Norm units are
recovered before the scale is cancelled. The parent's conditional auxiliary
negative-unit exclusion is inherited only after its strong norm equals1. -/
theorem positive_zero_iff75 (p : Fin 4 → ℤ) (v : Fin 13 → ℤ)
    (hb : 0 < p 0) (hv : ∀ j, 0 < v j) :
    value p v=0 ↔ ThirteenUnitSphere96.value p v=0 := by
  rw [ThirteenUnitSphere96.positive_zero_iff_residuals p v hb hv]
  rw [value,residuals_zero_iff]
  have hp : (data p v).P ≠ -1 := ThirteenCorrectedStrong.first_ne_neg_one p v hb hv
  have hq := ThirteenUnitSphere96.main_ne_neg_one p v
  constructor
  · rintro ⟨hpq,hz,hu⟩
    obtain ⟨hP,hQ⟩ := units _ _ hp hq hpq
    have ha : scale p v ≠ 0 := ne_of_gt (scale_pos_of_main p v hb hv hQ)
    have haux : auxiliary p v=scale p v*ThirteenGroupedSquares96.auxiliary p v := by
      simp [auxiliary,syzygy,hP,hQ]
    rw [haux] at hu
    have hU : ThirteenGroupedSquares96.auxiliary p v=1 :=
      mul_left_cancel₀ ha (by simpa only [mul_one] using hu)
    exact ⟨hpq,hU,hz⟩
  · rintro ⟨hpq,hU,hz⟩
    obtain ⟨hP,hQ⟩ := units _ _ hp hq hpq
    exact ⟨hpq,hz,by simp [auxiliary,syzygy,hP,hQ,hU]⟩

theorem positive_zero_iff88 (p : Fin 4 → ℤ) (v : Fin 13 → ℤ)
    (hb : 0 < p 0) (hv : ∀ j, 0 < v j) :
    value p v=0 ↔ ThirteenSecondFirstNormCorrections.value true p v=0 :=
  (positive_zero_iff75 p v hb hv).trans
    (ThirteenSecondFirstNormCorrections.positive_zero_iff75 true p v hb hv).symm

theorem value_map (φ : A →+* B) (p : Fin 4 → A) (v : Fin 13 → A) :
    φ (value p v)=value (fun j => φ (p j)) (fun j => φ (v j)) := by
  simp [value,auxiliary,scale,syzygy,coefficient,syzygyCoefficient,
    ThirteenSecondFirstNormCorrections.coefficient88,ThirteenGroupedSquares96.auxiliary,
    ThirteenLVCarrier.y,ThirteenLVCarrier.L,G,data,Carrier65.core,parent,b,Carrier65.strong,
    map_add,map_sub,map_mul,map_pow,map_ofNat]

noncomputable def polynomial (p : Fin 4 → ℤ) : MvPolynomial (Fin 13) ℤ :=
  value (fun j => MvPolynomial.C (p j)) MvPolynomial.X

theorem eval_polynomial (p : Fin 4 → ℤ) (v : Fin 13 → ℤ) :
    MvPolynomial.eval v (polynomial p)=value p v := by
  simpa only [polynomial,MvPolynomial.eval_C,MvPolynomial.eval_X] using
    value_map (MvPolynomial.eval v) (fun j => MvPolynomial.C (p j)) MvPolynomial.X

theorem exists_positive_zero_iff88 (p : Fin 4 → ℤ) (hb : 0 < p 0) :
    CurrentCarrierArithmetic2011.PositiveZero (polynomial p) ↔
      CurrentCarrierArithmetic2011.PositiveZero (ThirteenSecondFirstNormCorrections.polynomial true p) := by
  constructor <;> rintro ⟨v,hv,hz⟩
  · rw [eval_polynomial] at hz
    refine ⟨v,hv,?_⟩
    rw [ThirteenSecondFirstNormCorrections.eval_polynomial]
    exact (positive_zero_iff88 p v hb hv).mp hz
  · rw [ThirteenSecondFirstNormCorrections.eval_polynomial] at hz
    refine ⟨v,hv,?_⟩
    rw [eval_polynomial]
    exact (positive_zero_iff88 p v hb hv).mpr hz

noncomputable def currentPolynomial : MvPolynomial (Fin 13) ℤ :=
  polynomial CurrentWindowCarry2011.ports

/-- Actual current ports and actual ConZFC, as an external Lean theorem.
No internal HA/PA/ZFC proof is asserted. -/
theorem no_current_positive_zero_iff_conZFC :
    (¬ CurrentCarrierArithmetic2011.PositiveZero currentPolynomial) ↔
      DiophantineConsistency.ConZFC := by
  have hb : (0 : ℤ) < CurrentWindowCarry2011.ports 0 := by
    change (0 : ℤ) < CurrentMasks2011.beta
    exact_mod_cast CurrentMasks2011.beta_pos
  exact (not_congr (exists_positive_zero_iff88 _ hb)).trans
    (ThirteenSecondFirstNormCorrections.no_current_positive_zero_iff_conZFC true)
end DiophantineConsistency.ThirteenScaledNormSyzygy86
