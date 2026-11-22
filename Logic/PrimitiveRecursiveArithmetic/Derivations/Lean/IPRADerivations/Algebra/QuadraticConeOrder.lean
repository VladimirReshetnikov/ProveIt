import IPRADerivations.Algebra.QuadraticSignCertificates

/-!
# Actual quadratic cone closure and uniqueness of sign certificates

The source positive quadratic stage is used only at positive numerical d.
Actual coordinate-value equality is kept distinct from raw code equality.
The actual cone product gap is a sum of nonnegative source slacks, and
actual pair-ring identities rule out conflicting multiplier certificates.
No global sign/order law is an input.
-/

set_option autoImplicit false
set_option linter.unnecessarySeqFocus false

namespace LeanProofs.IPRA.Algebra.QuadraticConeOrder

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open QuadraticSignCertificates (first second equal cone add negative multiply zeroCode oneCode
  product multiplier sign classification tag certificate actual_certificate)
open QuadraticSignCertificates (first_value second_value multiply_first multiply_second negative_first negative_second
  zero_first_value zero_second_value)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

theorem first_nonnegative (x : PTm n) (h : Γ ⊢[PRAAx] cone x) : Nonneg Γ (ZT.toZ Γ (first x)) := nn_zle0 (.andE₁ h)
theorem second_nonnegative (x : PTm n) (h : Γ ⊢[PRAAx] cone x) : Nonneg Γ (ZT.toZ Γ (second x)) := nn_zle0 (.andE₁ (.andE₂ h))
theorem equal_first {x y : PTm n} (h : Γ ⊢[PRAAx] equal x y) : ZT.toZ Γ (first x) = ZT.toZ Γ (first y) := ZT.toZ_eq (.andE₁ h)
theorem equal_second {x y : PTm n} (h : Γ ⊢[PRAAx] equal x y) : ZT.toZ Γ (second x) = ZT.toZ Γ (second y) := ZT.toZ_eq (.andE₂ h)
theorem equal_of_values {x y : PTm n} (ha : ZT.toZ Γ (first x) = ZT.toZ Γ (first y))
    (hb : ZT.toZ Γ (second x) = ZT.toZ Γ (second y)) : Γ ⊢[PRAAx] equal x y := .andI (ZT.derive ha) (ZT.derive hb)
theorem equal_refl (x : PTm n) : Γ ⊢[PRAAx] equal x x := equal_of_values rfl rfl
theorem equal_symm {x y : PTm n} (h : Γ ⊢[PRAAx] equal x y) : Γ ⊢[PRAAx] equal y x := equal_of_values (equal_first h).symm (equal_second h).symm
theorem equal_trans {x y z : PTm n} (h : Γ ⊢[PRAAx] equal x y) (k : Γ ⊢[PRAAx] equal y z) : Γ ⊢[PRAAx] equal x z :=
  equal_of_values ((equal_first h).trans (equal_first k)) ((equal_second h).trans (equal_second k))
theorem add_first (x y : PTm n) : ZT.toZ Γ (first (add x y)) = ZT.toZ Γ (first x)+ZT.toZ Γ (first y) := by rw [add,first_value,ZT.toZ_add]
theorem add_second (x y : PTm n) : ZT.toZ Γ (second (add x y)) = ZT.toZ Γ (second x)+ZT.toZ Γ (second y) := by rw [add,second_value,ZT.toZ_add]

theorem cone_of_nonnegative (x : PTm n) (ha : Nonneg Γ (ZT.toZ Γ (first x)))
    (hb : Nonneg Γ (ZT.toZ Γ (second x)))
    (hs : Nonneg Γ (ZT.toZ Γ (first x)+ZT.toZ Γ (second x)-1)) : Γ ⊢[PRAAx] cone x :=
  .andI (QuadraticSignCertificates.nonnegative_of_value _ ha)
    (.andI (QuadraticSignCertificates.nonnegative_of_value _ hb)
      (zle_of_comb _ (by rw [ZT.toZ_add,ZT.toZ_ofNat]; ipra_simps; ring) hs))

theorem cone_add (x y : PTm n) (hx : Γ ⊢[PRAAx] cone x) (hy : Γ ⊢[PRAAx] cone y) : Γ ⊢[PRAAx] cone (add x y) := by
  have ha := first_nonnegative x hx
  have hb := second_nonnegative x hx
  have hc := first_nonnegative y hy
  have he := second_nonnegative y hy
  have gap : Nonneg Γ ((ZT.toZ Γ (first x)+ZT.toZ Γ (second x)-1)+(ZT.toZ Γ (first y)+ZT.toZ Γ (second y))) := by
    simpa only [zsl_def,ZT.toZ_add,ZT.toZ_ofNat,Q.mk_one,map_one] using nn_add (nn_zsl (.andE₂ (.andE₂ hx))) (nn_add hc he)
  apply cone_of_nonnegative
  · rw [add_first]; exact nn_add ha hc
  · rw [add_second]; exact nn_add hb he
  · have identity : ZT.toZ Γ (first (add x y))+ZT.toZ Γ (second (add x y))-1 =
        (ZT.toZ Γ (first x)+ZT.toZ Γ (second x)-1)+(ZT.toZ Γ (first y)+ZT.toZ Γ (second y)) := by
      rw [add_first,add_second]
      ring
    rw [identity]
    exact gap

theorem cone_multiply (d x y : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (hx : Γ ⊢[PRAAx] cone x) (hy : Γ ⊢[PRAAx] cone y) : Γ ⊢[PRAAx] cone (multiply d x y) := by
  have ha := first_nonnegative x hx
  have hb := second_nonnegative x hx
  have hc := first_nonnegative y hy
  have he := second_nonnegative y hy
  have gap := nn_add
    (nn_add (nn_mul (nn_zsl (.andE₂ (.andE₂ hx))) (nn_add hc he)) (nn_zsl (.andE₂ (.andE₂ hy))))
    (nn_mul (nn_sl hd) (nn_mul hb he))
  apply cone_of_nonnegative
  · rw [multiply_first]; exact nn_add (nn_mul ha hc) (nn_mul (nn_term d) (nn_mul hb he))
  · rw [multiply_second]; exact nn_add (nn_mul ha he) (nn_mul hb hc)
  · have identity : ZT.toZ Γ (first (multiply d x y))+ZT.toZ Γ (second (multiply d x y))-1 =
        (ZT.toZ Γ (first x+second x)-1)*(ZT.toZ Γ (first y)+ZT.toZ Γ (second y))+
          (ZT.toZ Γ (first y+second y)-1)+(𝔞(d)-1)*(ZT.toZ Γ (second x)*ZT.toZ Γ (second y)) := by
      rw [multiply_first,multiply_second,ZT.toZ_add,ZT.toZ_add]
      ring
    rw [identity]
    simpa only [zsl_def,ZT.toZ_ofNat,Q.mk_one,map_one,sl_def] using gap

theorem multiply_congr {d x x' y y' : PTm n} (hx : Γ ⊢[PRAAx] equal x x')
    (hy : Γ ⊢[PRAAx] equal y y') : Γ ⊢[PRAAx] equal (multiply d x y) (multiply d x' y') := by
  apply equal_of_values
  · rw [multiply_first,multiply_first,equal_first hx,equal_second hx,equal_first hy,equal_second hy]
  · rw [multiply_second,multiply_second,equal_first hx,equal_second hx,equal_first hy,equal_second hy]
theorem add_congr {x x' y y' : PTm n} (hx : Γ ⊢[PRAAx] equal x x')
    (hy : Γ ⊢[PRAAx] equal y y') : Γ ⊢[PRAAx] equal (add x y) (add x' y') := by
  apply equal_of_values
  · rw [add_first,add_first,equal_first hx,equal_first hy]
  · rw [add_second,add_second,equal_second hx,equal_second hy]
theorem negative_congr {x y : PTm n} (h : Γ ⊢[PRAAx] equal x y) : Γ ⊢[PRAAx] equal (negative x) (negative y) := by
  apply equal_of_values
  · rw [negative_first,negative_first,equal_first h]
  · rw [negative_second,negative_second,equal_second h]
theorem negative_negative (x : PTm n) : Γ ⊢[PRAAx] equal (negative (negative x)) x := by
  apply equal_of_values
  · rw [negative_first,negative_first,_root_.neg_neg]
  · rw [negative_second,negative_second,_root_.neg_neg]
theorem multiply_zero_right (d x : PTm n) : Γ ⊢[PRAAx] equal (multiply d x zeroCode) zeroCode := by
  apply equal_of_values
  · rw [multiply_first,zero_first_value,zero_second_value]; ring
  · rw [multiply_second,zero_first_value,zero_second_value]; ring
theorem nested_commute (d u v x : PTm n) : Γ ⊢[PRAAx]
    equal (multiply d v (multiply d u x)) (multiply d u (multiply d v x)) := by
  apply equal_of_values
  · simp only [multiply_first,multiply_second]; ring
  · simp only [multiply_first,multiply_second]; ring
theorem negative_product_right (d x y : PTm n) : Γ ⊢[PRAAx]
    equal (multiply d x (negative y)) (negative (multiply d x y)) := by
  apply equal_of_values
  · rw [multiply_first,negative_first,negative_first,negative_second,multiply_first]; ring
  · rw [multiply_second,negative_second,negative_first,negative_second,multiply_second]; ring
theorem add_negative_self (x : PTm n) : Γ ⊢[PRAAx] equal (add x (negative x)) zeroCode := by
  apply equal_of_values
  · rw [add_first,negative_first,zero_first_value]; ring
  · rw [add_second,negative_second,zero_second_value]; ring

theorem positive_zero_conflict (d x u v : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (_hu : Γ ⊢[PRAAx] cone u) (hv : Γ ⊢[PRAAx] cone v)
    (hPos : Γ ⊢[PRAAx] cone (multiply d u x))
    (hZero : Γ ⊢[PRAAx] equal (multiply d v x) zeroCode) : Γ ⊢[PRAAx] Fm.bot := by
  have pos := cone_multiply d v (multiply d u x) hd hv hPos
  have eq := equal_trans (nested_commute d u v x)
    (equal_trans (multiply_congr (equal_refl u) hZero) (multiply_zero_right d u))
  exact .impE (QuadraticSignCertificates.cone_not_zero _ pos) eq

theorem positive_negative_conflict (d x u v : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (hu : Γ ⊢[PRAAx] cone u) (hv : Γ ⊢[PRAAx] cone v)
    (hPos : Γ ⊢[PRAAx] cone (multiply d u x))
    (hNeg : Γ ⊢[PRAAx] cone (negative (multiply d v x))) : Γ ⊢[PRAAx] Fm.bot := by
  have a := cone_multiply d v (multiply d u x) hd hv hPos
  have b := cone_multiply d u (negative (multiply d v x)) hd hu hNeg
  have eq := equal_trans (Γ := Γ) (add_congr (nested_commute d u v x) (negative_product_right d u (multiply d v x)))
    (add_negative_self (multiply d u (multiply d v x)))
  exact .impE (QuadraticSignCertificates.cone_not_zero _ (cone_add _ _ a b)) eq


theorem negative_zero (x : PTm n) (h : Γ ⊢[PRAAx] equal x zeroCode) : Γ ⊢[PRAAx] equal (negative x) zeroCode := by
  apply equal_of_values
  · rw [negative_first,equal_first h,zero_first_value]; ring
  · rw [negative_second,equal_second h,zero_second_value]; ring

theorem negative_zero_conflict (d x u v : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (_hu : Γ ⊢[PRAAx] cone u) (hv : Γ ⊢[PRAAx] cone v)
    (hNeg : Γ ⊢[PRAAx] cone (negative (multiply d u x)))
    (hZero : Γ ⊢[PRAAx] equal (multiply d v x) zeroCode) : Γ ⊢[PRAAx] Fm.bot := by
  have pos := cone_multiply d v (negative (multiply d u x)) hd hv hNeg
  have eq := equal_trans (Γ := Γ) (negative_product_right d v (multiply d u x))
    (equal_trans (negative_congr (nested_commute d u v x))
      (negative_zero _ (equal_trans (multiply_congr (equal_refl u) hZero) (multiply_zero_right d u))))
  exact .impE (QuadraticSignCertificates.cone_not_zero _ pos) eq

theorem sign_unique_positive (d x u : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (hu : Γ ⊢[PRAAx] cone u) (hPos : Γ ⊢[PRAAx] cone (multiply d u x)) : Γ ⊢[PRAAx] sign d x ≐ one := by
  have actual := actual_certificate (Γ := Γ) d x
  have hw := Prf.andE₁ actual
  refine .orE (.andE₂ actual) (.andE₁ Prf.hyp0) ?_
  refine .orE Prf.hyp0 ?_ ?_
  · exact .botE _ (positive_negative_conflict d x u (multiplier x) hd.wk.wk hu.wk.wk hw.wk.wk hPos.wk.wk (.andE₂ Prf.hyp0))
  · exact .botE _ (positive_zero_conflict d x u (multiplier x) hd.wk.wk hu.wk.wk hw.wk.wk hPos.wk.wk (.andE₂ Prf.hyp0))

theorem sign_unique_negative (d x u : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (hu : Γ ⊢[PRAAx] cone u) (hNeg : Γ ⊢[PRAAx] cone (negative (multiply d u x))) : Γ ⊢[PRAAx] sign d x ≐ two := by
  have actual := actual_certificate (Γ := Γ) d x
  have hw := Prf.andE₁ actual
  refine .orE (.andE₂ actual) ?_ ?_
  · exact .botE _ (positive_negative_conflict d x (multiplier x) u hd.wk hw.wk hu.wk (.andE₂ Prf.hyp0) hNeg.wk)
  · refine .orE Prf.hyp0 (.andE₁ Prf.hyp0) ?_
    exact .botE _ (negative_zero_conflict d x u (multiplier x) hd.wk.wk hu.wk.wk hw.wk.wk hNeg.wk.wk (.andE₂ Prf.hyp0))

theorem sign_unique_zero (d x u : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (hu : Γ ⊢[PRAAx] cone u) (hZero : Γ ⊢[PRAAx] equal (multiply d u x) zeroCode) : Γ ⊢[PRAAx] sign d x ≐ zero := by
  have actual := actual_certificate (Γ := Γ) d x
  have hw := Prf.andE₁ actual
  refine .orE (.andE₂ actual) ?_ ?_
  · exact .botE _ (positive_zero_conflict d x (multiplier x) u hd.wk hw.wk hu.wk (.andE₂ Prf.hyp0) hZero.wk)
  · refine .orE Prf.hyp0 ?_ (.andE₁ Prf.hyp0)
    exact .botE _ (negative_zero_conflict d x (multiplier x) u hd.wk.wk hw.wk.wk hu.wk.wk (.andE₂ Prf.hyp0) hZero.wk.wk)


theorem cone_congr {x y : PTm n} (h : Γ ⊢[PRAAx] equal x y) (hx : Γ ⊢[PRAAx] cone x) : Γ ⊢[PRAAx] cone y := by
  apply cone_of_nonnegative
  · rw [← equal_first h]; exact first_nonnegative x hx
  · rw [← equal_second h]; exact second_nonnegative x hx
  · rw [← equal_first h,← equal_second h]
    simpa only [zsl_def,ZT.toZ_add,ZT.toZ_ofNat,Q.mk_one,map_one] using nn_zsl (.andE₂ (.andE₂ hx))

theorem sign_congr (d x y : PTm n) (hd : Γ ⊢[PRAAx] le one d) (h : Γ ⊢[PRAAx] equal x y) : Γ ⊢[PRAAx] sign d x ≐ sign d y := by
  have actual := actual_certificate (Γ := Γ) d x
  have hw := Prf.andE₁ actual
  have rel := multiply_congr (d := d) (equal_refl (multiplier x)) h
  refine .orE (.andE₂ actual) ?_ ?_
  · exact (Prf.andE₁ Prf.hyp0).eqTrans
      (sign_unique_positive d y (multiplier x) hd.wk hw.wk (cone_congr rel.wk (.andE₂ Prf.hyp0))).eqSymm
  · refine .orE Prf.hyp0 ?_ ?_
    · exact (Prf.andE₁ Prf.hyp0).eqTrans
        (sign_unique_negative d y (multiplier x) hd.wk.wk hw.wk.wk
          (cone_congr (negative_congr rel.wk.wk) (.andE₂ Prf.hyp0))).eqSymm
    · exact (Prf.andE₁ Prf.hyp0).eqTrans
        (sign_unique_zero d y (multiplier x) hd.wk.wk hw.wk.wk
          (equal_trans (equal_symm rel.wk.wk) (.andE₂ Prf.hyp0))).eqSymm

theorem returned_sign_positive (d x u : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (hu : Γ ⊢[PRAAx] cone u) (hPos : Γ ⊢[PRAAx] cone (multiply d u x)) : Γ ⊢[PRAAx]
    fstT (sndT (QuadraticSignCertificates.run d x)) ≐ one :=
  (QuadraticSignCertificates.returned_sign d x).eqTrans (sign_unique_positive d x u hd hu hPos)
theorem returned_sign_negative (d x u : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (hu : Γ ⊢[PRAAx] cone u) (hNeg : Γ ⊢[PRAAx] cone (negative (multiply d u x))) : Γ ⊢[PRAAx]
    fstT (sndT (QuadraticSignCertificates.run d x)) ≐ two :=
  (QuadraticSignCertificates.returned_sign d x).eqTrans (sign_unique_negative d x u hd hu hNeg)
theorem returned_sign_zero (d x u : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (hu : Γ ⊢[PRAAx] cone u) (hZero : Γ ⊢[PRAAx] equal (multiply d u x) zeroCode) : Γ ⊢[PRAAx]
    fstT (sndT (QuadraticSignCertificates.run d x)) ≐ zero :=
  (QuadraticSignCertificates.returned_sign d x).eqTrans (sign_unique_zero d x u hd hu hZero)

theorem actual_quadratic_cone_addition_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (cone (var 0) ⟶ cone (var 1) ⟶ cone (add (var 0) (var 1))) := closeUniv 2 (.impI (.impI (cone_add _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_quadratic_cone_product_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 0) ⟶ cone (var 1) ⟶ cone (var 2) ⟶ cone (multiply (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (.impI (.impI (cone_multiply _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))
theorem actual_positive_sign_unique_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 0) ⟶ cone (var 2) ⟶ cone (multiply (var 0) (var 2) (var 1)) ⟶ sign (var 0) (var 1) ≐ one) :=
  closeUniv 3 (.impI (.impI (.impI (sign_unique_positive _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))
theorem actual_negative_sign_unique_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 0) ⟶ cone (var 2) ⟶ cone (negative (multiply (var 0) (var 2) (var 1))) ⟶ sign (var 0) (var 1) ≐ two) :=
  closeUniv 3 (.impI (.impI (.impI (sign_unique_negative _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))
theorem actual_zero_sign_unique_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 0) ⟶ cone (var 2) ⟶ equal (multiply (var 0) (var 2) (var 1)) zeroCode ⟶ sign (var 0) (var 1) ≐ zero) :=
  closeUniv 3 (.impI (.impI (.impI (sign_unique_zero _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))
theorem actual_quadratic_sign_value_congruence_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 0) ⟶ equal (var 1) (var 2) ⟶ sign (var 0) (var 1) ≐ sign (var 0) (var 2)) :=
  closeUniv 3 (.impI (.impI (sign_congr _ _ _ Prf.hyp1 Prf.hyp0)))
theorem returned_positive_sign_unique_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 0) ⟶ cone (var 2) ⟶ cone (multiply (var 0) (var 2) (var 1)) ⟶
      fstT (sndT (QuadraticSignCertificates.run (var 0) (var 1))) ≐ one) :=
  closeUniv 3 (.impI (.impI (.impI (returned_sign_positive _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))
theorem returned_negative_sign_unique_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 0) ⟶ cone (var 2) ⟶ cone (negative (multiply (var 0) (var 2) (var 1))) ⟶
      fstT (sndT (QuadraticSignCertificates.run (var 0) (var 1))) ≐ two) :=
  closeUniv 3 (.impI (.impI (.impI (returned_sign_negative _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))
theorem returned_zero_sign_unique_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 0) ⟶ cone (var 2) ⟶ equal (multiply (var 0) (var 2) (var 1)) zeroCode ⟶
      fstT (sndT (QuadraticSignCertificates.run (var 0) (var 1))) ≐ zero) :=
  closeUniv 3 (.impI (.impI (.impI (returned_sign_zero _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Algebra.QuadraticConeOrder
