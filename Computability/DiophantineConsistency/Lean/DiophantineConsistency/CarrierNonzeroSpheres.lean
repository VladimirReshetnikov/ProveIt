import DiophantineConsistency.NearSquareNormZero
import DiophantineConsistency.CarrierScaledAuxiliary118

set_option autoImplicit false
set_option Elab.async false

/-! Two same-positive-zero-set equations for the actual fourteen-coordinate
carrier. The independent positive y coordinate is essential. The separate
finite schedules establish the 71/80 and 72/68 operation/degree metrics. -/
namespace DiophantineConsistency.CarrierNonzeroSpheres
open Carrier65

variable {A B : Type*} [CommRing A] [CommRing B]

def auxiliary (d : Core A) : A := d.delta*(d.f^2-1)*(d.V^2-d.y^2)+d.y^2

def value71 (p : Fin 4 → A) (v : Fin 14 → A) : A :=
  let d := core p v
  (d.P*d.Q)^2 + (auxiliary d*d.W-1)^2 + (strong d)^2 - 2

def value72 (p : Fin 4 → A) (v : Fin 14 → A) : A :=
  let d := core p v
  d.P^2 + (auxiliary d)^2 + (strong d)^2 + (d.Q*d.W-1)^2 - 3

private theorem c_pos (p : Fin 4 → ℤ) (v : Fin 14 → ℤ)
    (hb : 0 < p 0) (hv : ∀ j, 0 < v j) : 0 < (core p v).c := by
  have hY := (scales_pos p v hb hv).2.1
  change 0 < (v 10+v 11)*(core p v).Y+v 10
  exact add_pos (mul_pos (add_pos (hv 10) (hv 11)) hY) (hv 10)

/-- Unconditional on any zero equation, even when the signed tau is negative. -/
theorem first_ne_zero (p : Fin 4 → ℤ) (v : Fin 14 → ℤ)
    (hb : 0 < p 0) (hv : ∀ j, 0 < v j) : (core p v).P ≠ 0 := by
  let d := core p v
  let m := d.E*d.Y
  have hm : 2 ≤ m := firstParameter_ge_two p v hb hv
  have hk : 0 < d.k := add_pos (hv 10) (hv 11)
  have hi : 4*d.P=(2*d.tau)^2-((2*m+1)^2-1)*d.k^2 := by
    dsimp only [d, m]
    rw [first_shape]
    ring
  intro hz
  exact NearSquareNormZero.norm_ne_zero (2*m+1) (2*d.tau) d.k
    (by omega) (ne_of_gt hk) (by rw [← hi, hz]; ring)

theorem main_ne_zero (p : Fin 4 → ℤ) (v : Fin 14 → ℤ)
    (hb : 0 < p 0) (hv : ∀ j, 0 < v j) : (core p v).Q ≠ 0 := by
  have ha := (scales_pos p v hb hv).2.2.2
  change (core p v).D^2-(core p v).delta*(core p v).c^2 ≠ 0
  rw [delta_shape]
  exact NearSquareNormZero.norm_ne_zero _ _ _ (by omega) (ne_of_gt (c_pos p v hb hv))

theorem strong_ne_zero (p : Fin 4 → ℤ) (v : Fin 14 → ℤ)
    (hb : 0 < p 0) (hv : ∀ j, 0 < v j) : strong (core p v) ≠ 0 := by
  have ha := (scales_pos p v hb hv).2.2.2
  have hc := c_pos p v hb hv
  unfold strong
  rw [delta_shape]
  exact NearSquareNormZero.norm_ne_zero _ _ _ (by omega)
    (ne_of_gt (mul_pos (hv 5) (sq_pos_of_pos hc)))

/-- This uses the independent coordinate y>0, not a signed carrier ordinate.
No assertion that the auxiliary factor always avoids -1 is made. -/
theorem auxiliary_ne_zero (p : Fin 4 → ℤ) (v : Fin 14 → ℤ)
    (hb : 0 < p 0) (hv : ∀ j, 0 < v j) : auxiliary (core p v) ≠ 0 := by
  let d := core p v
  have hf : 0 < d.f := hv 4
  have hy : 0 < d.y := hv 12
  have hd : 0 < d.delta := delta_pos p v hb hv
  by_cases hf1 : d.f=1
  · change d.delta*(d.f^2-1)*(d.V^2-d.y^2)+d.y^2 ≠ 0
    simpa only [hf1, one_pow, sub_self, mul_zero, zero_mul, zero_add] using
      ne_of_gt (sq_pos_of_pos hy)
  · have hf2 : 2 ≤ d.f := by omega
    let theta := d.delta*(d.f^2-1)
    have ht : 2 ≤ theta := by
      have hs : 3 ≤ d.f^2-1 := by nlinarith
      have hmul := mul_le_mul_of_nonneg_right (show (1 : ℤ) ≤ d.delta by omega)
        (show 0 ≤ d.f^2-1 by omega)
      dsimp [theta]
      nlinarith
    have hi : 4*theta*auxiliary d =
        (2*theta*d.V)^2-((2*theta-1)^2-1)*d.y^2 := by
      dsimp only [auxiliary, theta]
      ring
    intro hz
    exact NearSquareNormZero.norm_ne_zero (2*theta-1) (2*theta*d.V) d.y
      (by omega) (ne_of_gt hy) (by rw [← hi, hz]; ring)

private theorem negative_unit_exclusions (p : Fin 4 → ℤ) (v : Fin 14 → ℤ)
    (hb : 0 < p 0) (hv : ∀ j, 0 < v j) :
    (core p v).P ≠ -1 ∧ (core p v).Q ≠ -1 ∧ strong (core p v) ≠ -1 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [first_shape]
    exact ConsecutivePell.norm_ne_neg_one _ _ _ (firstParameter_ge_two p v hb hv)
  · change (core p v).D^2-(core p v).delta*(core p v).c^2 ≠ -1
    rw [delta_shape]
    exact ShortEquation.strong_ne_neg_one _ _ _
  · unfold strong
    rw [delta_shape]
    exact ShortEquation.strong_ne_neg_one _ _ _

theorem auxiliary_of_strong_one (p : Fin 4 → ℤ) (v : Fin 14 → ℤ)
    (hs : strong (core p v)=1) : auxiliary (core p v)=(core p v).U := by
  let d := core p v
  have hf : d.f^2-1=d.delta*(d.i*d.c^2)^2 := by
    change d.f^2-d.delta*(d.i*d.c^2)^2=1 at hs
    linarith only [hs]
  have hcoef : d.delta*(d.f^2-1)=d.S^2 := by
    rw [hf]
    change d.delta*(d.delta*(d.i*d.c^2)^2)=(d.i*d.delta*d.c^2)^2
    ring
  change d.delta*(d.f^2-1)*(d.V^2-d.y^2)+d.y^2 = d.S^2*(d.V^2-d.y^2)+d.y^2
  rw [hcoef]

theorem auxiliary_ne_neg_one_of_strong_one (p : Fin 4 → ℤ) (v : Fin 14 → ℤ)
    (hs : strong (core p v)=1) : auxiliary (core p v) ≠ -1 := by
  rw [auxiliary_of_strong_one p v hs]
  exact ShortSystem.square_aux_ne_neg_one (core p v).S (core p v).V (core p v).y

private theorem square_ge_one (x : ℤ) (hx : x ≠ 0) : 1 ≤ x^2 := by
  have h := sq_pos_of_ne_zero hx
  omega

private theorem unit_factors (x y : ℤ) (h : x*y=1) (hx : x ≠ -1) : x=1 ∧ y=1 := by
  have h1 := (Int.eq_one_or_neg_one_of_mul_eq_one h).resolve_right hx
  exact ⟨h1, by simpa only [h1, one_mul] using h⟩

private theorem product_ne_neg_one (x y : ℤ) (hx : x ≠ -1) (hy : y ≠ -1) : x*y ≠ -1 := by
  intro h
  have hu : IsUnit x := IsUnit.of_mul_eq_one_right (-y) (by nlinarith only [h])
  have h1 := (Int.isUnit_iff.mp hu).resolve_right hx
  exact hy (by simpa only [h1, one_mul] using h)

def Norms (p : Fin 4 → ℤ) (v : Fin 14 → ℤ) : Prop :=
  (core p v).P=1 ∧ (core p v).Q=1 ∧ auxiliary (core p v)=1 ∧
    strong (core p v)=1 ∧ (core p v).W=1

theorem value71_zero_iff_norms (p : Fin 4 → ℤ) (v : Fin 14 → ℤ)
    (hb : 0 < p 0) (hv : ∀ j, 0 < v j) : value71 p v=0 ↔ Norms p v := by
  constructor
  · intro hz
    let d := core p v
    have hp : 1 ≤ (d.P*d.Q)^2 := square_ge_one _
      (mul_ne_zero (first_ne_zero p v hb hv) (main_ne_zero p v hb hv))
    have hs : 1 ≤ (strong d)^2 := square_ge_one _ (strong_ne_zero p v hb hv)
    have hr := sq_nonneg (auxiliary d*d.W-1)
    change (d.P*d.Q)^2+(auxiliary d*d.W-1)^2+(strong d)^2-2=0 at hz
    have hps : (d.P*d.Q)^2=1 := by nlinarith only [hz,hp,hs,hr]
    have hss : (strong d)^2=1 := by nlinarith only [hz,hp,hs,hr]
    have hrs : (auxiliary d*d.W-1)^2=0 := by nlinarith only [hz,hp,hs,hr]
    have huw : auxiliary d*d.W=1 := sub_eq_zero.mp (sq_eq_zero_iff.mp hrs)
    obtain ⟨hnP,hnQ,hnZ⟩ := negative_unit_exclusions p v hb hv
    have hpq := (sq_eq_one_iff.mp hps).resolve_right (product_ne_neg_one _ _ hnP hnQ)
    have hz1 := (sq_eq_one_iff.mp hss).resolve_right hnZ
    obtain ⟨hP,hQ⟩ := unit_factors _ _ hpq hnP
    obtain ⟨hU,hW⟩ := unit_factors _ _ huw (auxiliary_ne_neg_one_of_strong_one p v hz1)
    exact ⟨hP,hQ,hU,hz1,hW⟩
  · rintro ⟨hP,hQ,hU,hZ,hW⟩
    simp only [value71,hP,hQ,hU,hZ,hW]
    norm_num

theorem value72_zero_iff_norms (p : Fin 4 → ℤ) (v : Fin 14 → ℤ)
    (hb : 0 < p 0) (hv : ∀ j, 0 < v j) : value72 p v=0 ↔ Norms p v := by
  constructor
  · intro hz
    let d := core p v
    have hp : 1 ≤ d.P^2 := square_ge_one _ (first_ne_zero p v hb hv)
    have hu : 1 ≤ (auxiliary d)^2 := square_ge_one _ (auxiliary_ne_zero p v hb hv)
    have hs : 1 ≤ (strong d)^2 := square_ge_one _ (strong_ne_zero p v hb hv)
    have hr := sq_nonneg (d.Q*d.W-1)
    change d.P^2+(auxiliary d)^2+(strong d)^2+(d.Q*d.W-1)^2-3=0 at hz
    have hps : d.P^2=1 := by nlinarith only [hz,hp,hu,hs,hr]
    have hus : (auxiliary d)^2=1 := by nlinarith only [hz,hp,hu,hs,hr]
    have hss : (strong d)^2=1 := by nlinarith only [hz,hp,hu,hs,hr]
    have hrs : (d.Q*d.W-1)^2=0 := by nlinarith only [hz,hp,hu,hs,hr]
    have hqw : d.Q*d.W=1 := sub_eq_zero.mp (sq_eq_zero_iff.mp hrs)
    obtain ⟨hnP,hnQ,hnZ⟩ := negative_unit_exclusions p v hb hv
    have hP := (sq_eq_one_iff.mp hps).resolve_right hnP
    have hZ := (sq_eq_one_iff.mp hss).resolve_right hnZ
    have hU := (sq_eq_one_iff.mp hus).resolve_right (auxiliary_ne_neg_one_of_strong_one p v hZ)
    obtain ⟨hQ,hW⟩ := unit_factors _ _ hqw hnQ
    exact ⟨hP,hQ,hU,hZ,hW⟩
  · rintro ⟨hP,hQ,hU,hZ,hW⟩
    simp only [value72,hP,hQ,hU,hZ,hW]
    norm_num

theorem norms_iff_original (p : Fin 4 → ℤ) (v : Fin 14 → ℤ)
    (hb : 0 < p 0) (hv : ∀ j, 0 < v j) : Norms p v ↔ Carrier65.value p v=0 := by
  rw [Carrier65.value_zero_iff_norms p v hb hv]
  constructor
  · rintro ⟨hP,hQ,hU,hZ,hW⟩
    exact ⟨hP,hQ,by rw [← auxiliary_of_strong_one p v hZ]; exact hU,hZ,hW⟩
  · rintro ⟨hP,hQ,hU,hZ,hW⟩
    exact ⟨hP,hQ,by rw [auxiliary_of_strong_one p v hZ]; exact hU,hZ,hW⟩

theorem positive_zero71_iff_original (p : Fin 4 → ℤ) (v : Fin 14 → ℤ)
    (hb : 0 < p 0) (hv : ∀ j, 0 < v j) : value71 p v=0 ↔ Carrier65.value p v=0 :=
  (value71_zero_iff_norms p v hb hv).trans (norms_iff_original p v hb hv)

theorem positive_zero72_iff_original (p : Fin 4 → ℤ) (v : Fin 14 → ℤ)
    (hb : 0 < p 0) (hv : ∀ j, 0 < v j) : value72 p v=0 ↔ Carrier65.value p v=0 :=
  (value72_zero_iff_norms p v hb hv).trans (norms_iff_original p v hb hv)

theorem value71_map (φ : A →+* B) (p : Fin 4 → A) (v : Fin 14 → A) :
    φ (value71 p v)=value71 (fun j => φ (p j)) (fun j => φ (v j)) := by
  simp only [value71,auxiliary,strong,core,map_add,map_sub,map_mul,map_pow,map_one,map_ofNat]

theorem value72_map (φ : A →+* B) (p : Fin 4 → A) (v : Fin 14 → A) :
    φ (value72 p v)=value72 (fun j => φ (p j)) (fun j => φ (v j)) := by
  simp only [value72,auxiliary,strong,core,map_add,map_sub,map_mul,map_pow,map_one,map_ofNat]

noncomputable def polynomial71 (p : Fin 4 → ℤ) : MvPolynomial (Fin 14) ℤ :=
  value71 (fun j => MvPolynomial.C (p j)) MvPolynomial.X

noncomputable def polynomial72 (p : Fin 4 → ℤ) : MvPolynomial (Fin 14) ℤ :=
  value72 (fun j => MvPolynomial.C (p j)) MvPolynomial.X

theorem eval_polynomial71 (p : Fin 4 → ℤ) (v : Fin 14 → ℤ) :
    MvPolynomial.eval v (polynomial71 p)=value71 p v := by
  simpa only [polynomial71,MvPolynomial.eval_C,MvPolynomial.eval_X] using
    value71_map (MvPolynomial.eval v) (fun j => MvPolynomial.C (p j)) MvPolynomial.X

theorem eval_polynomial72 (p : Fin 4 → ℤ) (v : Fin 14 → ℤ) :
    MvPolynomial.eval v (polynomial72 p)=value72 p v := by
  simpa only [polynomial72,MvPolynomial.eval_C,MvPolynomial.eval_X] using
    value72_map (MvPolynomial.eval v) (fun j => MvPolynomial.C (p j)) MvPolynomial.X

noncomputable def currentPolynomial71 : MvPolynomial (Fin 14) ℤ :=
  polynomial71 CurrentWindowCarry2011.ports
noncomputable def currentPolynomial72 : MvPolynomial (Fin 14) ℤ :=
  polynomial72 CurrentWindowCarry2011.ports

theorem current_positive_zero71_iff :
    CurrentCarrierArithmetic2011.PositiveZero currentPolynomial71 ↔
      CurrentCarrierArithmetic2011.PositiveZero CurrentPolynomialWindow2011.polynomial := by
  have hb : (0 : ℤ) < CurrentWindowCarry2011.ports 0 := by
    change (0 : ℤ) < CurrentMasks2011.beta
    exact_mod_cast CurrentMasks2011.beta_pos
  constructor <;> rintro ⟨v,hv,hz⟩ <;> refine ⟨v,hv,?_⟩
  · change MvPolynomial.eval v (polynomial71 CurrentWindowCarry2011.ports)=0 at hz
    change MvPolynomial.eval v (Carrier65.polynomial CurrentWindowCarry2011.ports)=0
    rw [eval_polynomial71] at hz
    rw [Carrier65.eval_polynomial]
    exact (positive_zero71_iff_original _ v hb hv).mp hz
  · change MvPolynomial.eval v (Carrier65.polynomial CurrentWindowCarry2011.ports)=0 at hz
    change MvPolynomial.eval v (polynomial71 CurrentWindowCarry2011.ports)=0
    rw [Carrier65.eval_polynomial] at hz
    rw [eval_polynomial71]
    exact (positive_zero71_iff_original _ v hb hv).mpr hz

theorem current_positive_zero72_iff :
    CurrentCarrierArithmetic2011.PositiveZero currentPolynomial72 ↔
      CurrentCarrierArithmetic2011.PositiveZero CurrentPolynomialWindow2011.polynomial := by
  have hb : (0 : ℤ) < CurrentWindowCarry2011.ports 0 := by
    change (0 : ℤ) < CurrentMasks2011.beta
    exact_mod_cast CurrentMasks2011.beta_pos
  constructor <;> rintro ⟨v,hv,hz⟩ <;> refine ⟨v,hv,?_⟩
  · change MvPolynomial.eval v (polynomial72 CurrentWindowCarry2011.ports)=0 at hz
    change MvPolynomial.eval v (Carrier65.polynomial CurrentWindowCarry2011.ports)=0
    rw [eval_polynomial72] at hz
    rw [Carrier65.eval_polynomial]
    exact (positive_zero72_iff_original _ v hb hv).mp hz
  · change MvPolynomial.eval v (Carrier65.polynomial CurrentWindowCarry2011.ports)=0 at hz
    change MvPolynomial.eval v (polynomial72 CurrentWindowCarry2011.ports)=0
    rw [Carrier65.eval_polynomial] at hz
    rw [eval_polynomial72]
    exact (positive_zero72_iff_original _ v hb hv).mpr hz

/-- External exact-current-port equivalences, not internal HA/ZFC derivations. -/
theorem no_current_positive_zero71_iff_conZFC :
    (¬ CurrentCarrierArithmetic2011.PositiveZero currentPolynomial71) ↔ DiophantineConsistency.ConZFC :=
  (not_congr current_positive_zero71_iff).trans CurrentPositiveZero2011.no_positive_zero_iff_conZFC

theorem no_current_positive_zero72_iff_conZFC :
    (¬ CurrentCarrierArithmetic2011.PositiveZero currentPolynomial72) ↔ DiophantineConsistency.ConZFC :=
  (not_congr current_positive_zero72_iff).trans CurrentPositiveZero2011.no_positive_zero_iff_conZFC

end DiophantineConsistency.CarrierNonzeroSpheres
