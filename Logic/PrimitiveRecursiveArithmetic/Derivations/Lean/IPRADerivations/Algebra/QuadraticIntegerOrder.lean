import IPRADerivations.Algebra.QuadraticConeOrder

/-!
# The actual sign-zero ideal in one positive integer quadratic stage

Signs and multiplier certificates are the SAME actual finite programs.
Positive and zero closure use computed products of the original cone
multipliers. Equality of the resulting radical values is sign-zero of
the difference, distinct from coefficient-value or raw code equality.
Only the integer ground stage and positive numerical radicand are used.
-/

set_option autoImplicit false
set_option linter.unnecessarySeqFocus false

namespace LeanProofs.IPRA.Algebra.QuadraticIntegerOrder

open_ipra
open QuadraticSignCertificates (first second equal cone add negative multiply zeroCode oneCode
  product multiplier sign certificate actual_certificate)
open QuadraticSignCertificates (multiply_first multiply_second negative_first negative_second
  zero_first_value zero_second_value first_value second_value)
open QuadraticConeOrder (equal_of_values equal_refl equal_symm equal_trans equal_first equal_second
  multiply_congr add_congr negative_congr cone_congr cone_add cone_multiply add_first add_second
  multiply_zero_right nested_commute negative_product_right add_negative_self negative_zero negative_negative
  sign_unique_positive sign_unique_negative sign_unique_zero sign_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def positive (d x : PTm n) : Fm PTm n := sign d x ≐ one
def isZero (d x : PTm n) : Fm PTm n := sign d x ≐ zero
def isNegative (d x : PTm n) : Fm PTm n := sign d x ≐ two
def difference (x y : PTm n) : PTm n := add x (negative y)
def equivalent (d x y : PTm n) : Fm PTm n := isZero d (difference x y)
ipra_subst positive
ipra_subst isZero
ipra_subst isNegative
ipra_subst difference
ipra_subst equivalent

theorem one_zero_absurd (φ : Fm PTm n) (h : Γ ⊢[PRAAx] (one : PTm n) ≐ zero) : Γ ⊢[PRAAx] φ := succ_ne_zero' φ h
theorem two_zero_absurd (φ : Fm PTm n) (h : Γ ⊢[PRAAx] (two : PTm n) ≐ zero) : Γ ⊢[PRAAx] φ := succ_ne_zero' φ h
theorem one_two_absurd (φ : Fm PTm n) (h : Γ ⊢[PRAAx] (one : PTm n) ≐ two) : Γ ⊢[PRAAx] φ :=
  succ_ne_zero' φ ((pred_succ zero).eqSymm.eqTrans ((congrPred h).eqTrans (pred_succ one))).eqSymm

theorem positive_certificate (d x : PTm n) (h : Γ ⊢[PRAAx] positive d x) : Γ ⊢[PRAAx] cone (product d x) := by
  refine .orE (.andE₂ (actual_certificate d x)) (.andE₂ Prf.hyp0) ?_
  refine .orE Prf.hyp0 ?_ ?_
  · exact one_two_absurd _ (h.wk.wk.eqSymm.eqTrans (.andE₁ Prf.hyp0))
  · exact one_zero_absurd _ (h.wk.wk.eqSymm.eqTrans (.andE₁ Prf.hyp0))
theorem negative_certificate (d x : PTm n) (h : Γ ⊢[PRAAx] isNegative d x) : Γ ⊢[PRAAx] cone (negative (product d x)) := by
  refine .orE (.andE₂ (actual_certificate d x)) ?_ ?_
  · exact one_two_absurd _ ((Prf.andE₁ Prf.hyp0).eqSymm.eqTrans h.wk)
  · refine .orE Prf.hyp0 (.andE₂ Prf.hyp0) ?_
    exact two_zero_absurd _ (h.wk.wk.eqSymm.eqTrans (.andE₁ Prf.hyp0))
theorem zero_certificate (d x : PTm n) (h : Γ ⊢[PRAAx] isZero d x) : Γ ⊢[PRAAx] equal (product d x) zeroCode := by
  refine .orE (.andE₂ (actual_certificate d x)) ?_ ?_
  · exact one_zero_absurd _ ((Prf.andE₁ Prf.hyp0).eqSymm.eqTrans h.wk)
  · refine .orE Prf.hyp0 ?_ (.andE₂ Prf.hyp0)
    exact two_zero_absurd _ ((Prf.andE₁ Prf.hyp0).eqSymm.eqTrans h.wk.wk)

theorem one_first_value : ZT.toZ Γ (first (oneCode : PTm n)) = 1 := by
  change ZT.toZ Γ (first (QuadraticSignCertificates.encode (ZT.ofNat one) (ZT.ofNat zero))) = 1
  rw [first_value,ZT.toZ_ofNat]
  ipra_simps
  ring
theorem one_second_value : ZT.toZ Γ (second (oneCode : PTm n)) = 0 := by
  change ZT.toZ Γ (second (QuadraticSignCertificates.encode (ZT.ofNat one) (ZT.ofNat zero))) = 0
  rw [second_value,ZT.toZ_ofNat]
  ipra_simps
theorem cone_one : Γ ⊢[PRAAx] cone (oneCode : PTm n) :=
  QuadraticSignCertificates.cone_natural one zero (le_congr (.eqRefl _) (add_zero _).eqSymm (le_refl _))
theorem multiply_one_left (d x : PTm n) : Γ ⊢[PRAAx] equal (multiply d oneCode x) x := by
  apply equal_of_values
  · rw [multiply_first,one_first_value,one_second_value]; ring
  · rw [multiply_second,one_first_value,one_second_value]; ring
theorem add_zero_right (x : PTm n) : Γ ⊢[PRAAx] equal (add x zeroCode) x := by
  apply equal_of_values
  · rw [add_first,zero_first_value]; ring
  · rw [add_second,zero_second_value]; ring

theorem positive_value_congr (d x y : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (he : Γ ⊢[PRAAx] equal x y) (h : Γ ⊢[PRAAx] positive d x) : Γ ⊢[PRAAx] positive d y :=
  (sign_congr d x y hd he).eqSymm.eqTrans h
theorem zero_value_congr (d x y : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (he : Γ ⊢[PRAAx] equal x y) (h : Γ ⊢[PRAAx] isZero d x) : Γ ⊢[PRAAx] isZero d y :=
  (sign_congr d x y hd he).eqSymm.eqTrans h

theorem cone_positive (d x : PTm n) (hd : Γ ⊢[PRAAx] le one d) (h : Γ ⊢[PRAAx] cone x) : Γ ⊢[PRAAx] positive d x :=
  sign_unique_positive d x oneCode hd cone_one (cone_congr (equal_symm (multiply_one_left d x)) h)
theorem zero_isZero (d : PTm n) (hd : Γ ⊢[PRAAx] le one d) : Γ ⊢[PRAAx] isZero d zeroCode :=
  sign_unique_zero d zeroCode oneCode hd cone_one (multiply_zero_right d oneCode)

theorem add_multiplier_identity (d u v x y : PTm n) : Γ ⊢[PRAAx]
    equal (multiply d (multiply d u v) (add x y))
      (add (multiply d v (multiply d u x)) (multiply d u (multiply d v y))) := by
  apply equal_of_values <;> simp only [multiply_first,multiply_second,add_first,add_second] <;> ring
theorem product_multiplier_identity (d u v x y : PTm n) : Γ ⊢[PRAAx]
    equal (multiply d (multiply d u v) (multiply d x y)) (multiply d (multiply d u x) (multiply d v y)) := by
  apply equal_of_values <;> simp only [multiply_first,multiply_second] <;> ring
theorem zero_multiplier_identity (d u x y : PTm n) : Γ ⊢[PRAAx]
    equal (multiply d u (multiply d x y)) (multiply d y (multiply d u x)) := by
  apply equal_of_values <;> simp only [multiply_first,multiply_second] <;> ring

theorem positive_add (d x y : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (hx : Γ ⊢[PRAAx] positive d x) (hy : Γ ⊢[PRAAx] positive d y) : Γ ⊢[PRAAx] positive d (add x y) := by
  have hu := QuadraticSignCertificates.multiplier_cone (Γ := Γ) x
  have hv := QuadraticSignCertificates.multiplier_cone (Γ := Γ) y
  have a := cone_multiply d (multiplier y) (product d x) hd hv (positive_certificate d x hx)
  have b := cone_multiply d (multiplier x) (product d y) hd hu (positive_certificate d y hy)
  exact sign_unique_positive d (add x y) (multiply d (multiplier x) (multiplier y)) hd
    (cone_multiply _ _ _ hd hu hv)
    (cone_congr (equal_symm (add_multiplier_identity _ _ _ _ _)) (cone_add _ _ a b))
theorem positive_multiply (d x y : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (hx : Γ ⊢[PRAAx] positive d x) (hy : Γ ⊢[PRAAx] positive d y) : Γ ⊢[PRAAx] positive d (multiply d x y) :=
  sign_unique_positive d (multiply d x y) (multiply d (multiplier x) (multiplier y)) hd
    (cone_multiply _ _ _ hd (QuadraticSignCertificates.multiplier_cone x) (QuadraticSignCertificates.multiplier_cone y))
    (cone_congr (equal_symm (product_multiplier_identity _ _ _ _ _))
      (cone_multiply _ _ _ hd (positive_certificate d x hx) (positive_certificate d y hy)))

theorem zero_multiply (d x y : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (hx : Γ ⊢[PRAAx] isZero d x) : Γ ⊢[PRAAx] isZero d (multiply d x y) :=
  sign_unique_zero d (multiply d x y) (multiplier x) hd (QuadraticSignCertificates.multiplier_cone x)
    (equal_trans (zero_multiplier_identity _ _ _ _)
      (equal_trans (multiply_congr (equal_refl y) (zero_certificate d x hx)) (multiply_zero_right d y)))
theorem zero_negative (d x : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (hx : Γ ⊢[PRAAx] isZero d x) : Γ ⊢[PRAAx] isZero d (negative x) :=
  sign_unique_zero d (negative x) (multiplier x) hd (QuadraticSignCertificates.multiplier_cone x)
    (equal_trans (negative_product_right _ _ _) (negative_zero _ (zero_certificate d x hx)))
theorem zero_add (d x y : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (hx : Γ ⊢[PRAAx] isZero d x) (hy : Γ ⊢[PRAAx] isZero d y) : Γ ⊢[PRAAx] isZero d (add x y) := by
  have hu := QuadraticSignCertificates.multiplier_cone (Γ := Γ) x
  have hv := QuadraticSignCertificates.multiplier_cone (Γ := Γ) y
  have a := equal_trans (multiply_congr (equal_refl (multiplier y)) (zero_certificate d x hx)) (multiply_zero_right d (multiplier y))
  have b := equal_trans (multiply_congr (equal_refl (multiplier x)) (zero_certificate d y hy)) (multiply_zero_right d (multiplier x))
  exact sign_unique_zero d (add x y) (multiply d (multiplier x) (multiplier y)) hd (cone_multiply _ _ _ hd hu hv)
    (equal_trans (add_multiplier_identity _ _ _ _ _) (equal_trans (add_congr a b) (add_zero_right zeroCode)))
theorem positive_add_zero (d x y : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (hx : Γ ⊢[PRAAx] positive d x) (hy : Γ ⊢[PRAAx] isZero d y) : Γ ⊢[PRAAx] positive d (add x y) := by
  have hu := QuadraticSignCertificates.multiplier_cone (Γ := Γ) x
  have hv := QuadraticSignCertificates.multiplier_cone (Γ := Γ) y
  have a := cone_multiply d (multiplier y) (product d x) hd hv (positive_certificate d x hx)
  have b := equal_trans (multiply_congr (equal_refl (multiplier x)) (zero_certificate d y hy)) (multiply_zero_right d (multiplier x))
  have rel := equal_trans (Γ := Γ) (add_congr (equal_refl (multiply d (multiplier y) (product d x))) b)
    (add_zero_right (multiply d (multiplier y) (product d x)))
  exact sign_unique_positive d (add x y) (multiply d (multiplier x) (multiplier y)) hd (cone_multiply _ _ _ hd hu hv)
    (cone_congr (equal_symm (equal_trans (add_multiplier_identity _ _ _ _ _) rel)) a)


theorem negative_difference (x y : PTm n) : Γ ⊢[PRAAx] equal (negative (difference x y)) (difference y x) := by
  apply equal_of_values <;> simp only [difference,add_first,add_second,negative_first,negative_second] <;> ring
theorem difference_chain (x y z : PTm n) : Γ ⊢[PRAAx] equal (add (difference x y) (difference y z)) (difference x z) := by
  apply equal_of_values <;> simp only [difference,add_first,add_second,negative_first,negative_second] <;> ring
theorem difference_add (x y z w : PTm n) : Γ ⊢[PRAAx]
    equal (add (difference x y) (difference z w)) (difference (add x z) (add y w)) := by
  apply equal_of_values <;> simp only [difference,add_first,add_second,negative_first,negative_second] <;> ring
theorem difference_product (d x y z w : PTm n) : Γ ⊢[PRAAx]
    equal (add (multiply d (difference x y) z) (multiply d (difference z w) y))
      (difference (multiply d x z) (multiply d y w)) := by
  apply equal_of_values <;> simp only [difference,multiply_first,multiply_second,add_first,add_second,negative_first,negative_second] <;> ring
theorem difference_negative (x y : PTm n) : Γ ⊢[PRAAx]
    equal (negative (difference x y)) (difference (negative x) (negative y)) := by
  apply equal_of_values <;> simp only [difference,add_first,add_second,negative_first,negative_second] <;> ring

theorem equivalent_refl (d x : PTm n) (hd : Γ ⊢[PRAAx] le one d) : Γ ⊢[PRAAx] equivalent d x x :=
  zero_value_congr d zeroCode (difference x x) hd (equal_symm (add_negative_self x)) (zero_isZero d hd)
theorem equivalent_symm (d x y : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (h : Γ ⊢[PRAAx] equivalent d x y) : Γ ⊢[PRAAx] equivalent d y x :=
  zero_value_congr _ _ _ hd (negative_difference x y) (zero_negative d (difference x y) hd h)
theorem equivalent_trans (d x y z : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (hxy : Γ ⊢[PRAAx] equivalent d x y) (hyz : Γ ⊢[PRAAx] equivalent d y z) : Γ ⊢[PRAAx] equivalent d x z :=
  zero_value_congr _ _ _ hd (difference_chain x y z) (zero_add _ _ _ hd hxy hyz)
theorem equivalent_add (d x y z w : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (hxy : Γ ⊢[PRAAx] equivalent d x y) (hzw : Γ ⊢[PRAAx] equivalent d z w) : Γ ⊢[PRAAx]
    equivalent d (add x z) (add y w) :=
  zero_value_congr _ _ _ hd (difference_add x y z w) (zero_add _ _ _ hd hxy hzw)
theorem equivalent_multiply (d x y z w : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (hxy : Γ ⊢[PRAAx] equivalent d x y) (hzw : Γ ⊢[PRAAx] equivalent d z w) : Γ ⊢[PRAAx]
    equivalent d (multiply d x z) (multiply d y w) :=
  zero_value_congr _ _ _ hd (difference_product d x y z w)
    (zero_add _ _ _ hd (zero_multiply _ _ _ hd hxy) (zero_multiply _ _ _ hd hzw))
theorem equivalent_negative (d x y : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (h : Γ ⊢[PRAAx] equivalent d x y) : Γ ⊢[PRAAx] equivalent d (negative x) (negative y) :=
  zero_value_congr _ _ _ hd (difference_negative x y) (zero_negative _ _ hd h)

theorem recover_difference (x y : PTm n) : Γ ⊢[PRAAx] equal (add x (difference y x)) y := by
  apply equal_of_values <;> simp only [difference,add_first,add_second,negative_first,negative_second] <;> ring
theorem positive_equivalent_congr (d x y : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (he : Γ ⊢[PRAAx] equivalent d x y) (h : Γ ⊢[PRAAx] positive d x) : Γ ⊢[PRAAx] positive d y :=
  positive_value_congr _ _ _ hd (recover_difference x y)
    (positive_add_zero _ _ _ hd h (equivalent_symm d x y hd he))
theorem zero_equivalent_congr (d x y : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (he : Γ ⊢[PRAAx] equivalent d x y) (h : Γ ⊢[PRAAx] isZero d x) : Γ ⊢[PRAAx] isZero d y :=
  zero_value_congr _ _ _ hd (recover_difference x y)
    (zero_add _ _ _ hd h (equivalent_symm d x y hd he))

theorem negative_positive (d x : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (h : Γ ⊢[PRAAx] isNegative d x) : Γ ⊢[PRAAx] positive d (negative x) :=
  sign_unique_positive d (negative x) (multiplier x) hd (QuadraticSignCertificates.multiplier_cone x)
    (cone_congr (equal_symm (negative_product_right _ _ _)) (negative_certificate d x h))
theorem positive_negative (d x : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (h : Γ ⊢[PRAAx] positive d x) : Γ ⊢[PRAAx] isNegative d (negative x) :=
  sign_unique_negative d (negative x) (multiplier x) hd (QuadraticSignCertificates.multiplier_cone x)
    (cone_congr (equal_symm (equal_trans (negative_congr (negative_product_right _ _ _))
      (negative_negative (multiply d (multiplier x) x)))) (positive_certificate d x h))

def less (d x y : PTm n) : Fm PTm n := positive d (difference y x)
ipra_subst less

theorem less_irrefl (d x : PTm n) (hd : Γ ⊢[PRAAx] le one d) : Γ ⊢[PRAAx] neg (less d x x) := by
  refine .impI ?_
  exact one_zero_absurd _ (Prf.hyp0.eqSymm.eqTrans (equivalent_refl d x hd.wk))
theorem less_trans (d x y z : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (hxy : Γ ⊢[PRAAx] less d x y) (hyz : Γ ⊢[PRAAx] less d y z) : Γ ⊢[PRAAx] less d x z :=
  positive_value_congr _ _ _ hd (difference_chain z y x)
    (positive_add _ _ _ hd hyz hxy)
theorem translation_difference (x y z : PTm n) : Γ ⊢[PRAAx]
    equal (difference y x) (difference (add y z) (add x z)) := by
  apply equal_of_values <;> simp only [difference,add_first,add_second,negative_first,negative_second] <;> ring
theorem less_translate (d x y z : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (h : Γ ⊢[PRAAx] less d x y) : Γ ⊢[PRAAx] less d (add x z) (add y z) :=
  positive_value_congr _ _ _ hd (translation_difference x y z) h

theorem sign_trichotomy (d x : PTm n) : Γ ⊢[PRAAx] positive d x ⋎ (isNegative d x ⋎ isZero d x) := by
  refine .orE (.andE₂ (actual_certificate d x)) (.orI₁ (.andE₁ Prf.hyp0)) ?_
  exact .orE Prf.hyp0 (.orI₂ (.orI₁ (.andE₁ Prf.hyp0))) (.orI₂ (.orI₂ (.andE₁ Prf.hyp0)))
theorem ordered_trichotomy (d x y : PTm n) (hd : Γ ⊢[PRAAx] le one d) : Γ ⊢[PRAAx]
    less d x y ⋎ (less d y x ⋎ equivalent d x y) := by
  refine .orE (sign_trichotomy d (difference y x)) (.orI₁ Prf.hyp0) ?_
  refine .orE Prf.hyp0 ?_ ?_
  · exact .orI₂ (.orI₁ (positive_value_congr _ _ _ hd.wk.wk (negative_difference y x) (negative_positive _ _ hd.wk.wk Prf.hyp0)))
  · exact .orI₂ (.orI₂ (equivalent_symm d y x hd.wk.wk Prf.hyp0))


theorem less_congr (d x x' y y' : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (hx : Γ ⊢[PRAAx] equivalent d x x') (hy : Γ ⊢[PRAAx] equivalent d y y')
    (h : Γ ⊢[PRAAx] less d x y) : Γ ⊢[PRAAx] less d x' y' :=
  positive_equivalent_congr _ _ _ hd (equivalent_add d y y' (negative x) (negative x') hd hy (equivalent_negative d x x' hd hx)) h

theorem positive_zero_absurd (d x : PTm n) (hp : Γ ⊢[PRAAx] positive d x)
    (hz : Γ ⊢[PRAAx] isZero d x) : Γ ⊢[PRAAx] Fm.bot := one_zero_absurd _ (hp.eqSymm.eqTrans hz)
theorem negative_product_left (d x y : PTm n) : Γ ⊢[PRAAx]
    equal (multiply d (negative x) y) (negative (multiply d x y)) := by
  apply equal_of_values <;> simp only [multiply_first,multiply_second,negative_first,negative_second] <;> ring

theorem zero_product_positive_left (d x y : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (hx : Γ ⊢[PRAAx] positive d x) (hxy : Γ ⊢[PRAAx] isZero d (multiply d x y)) : Γ ⊢[PRAAx] isZero d y := by
  refine .orE (sign_trichotomy d y) ?_ ?_
  · exact .botE _ (positive_zero_absurd _ _ (positive_multiply _ _ _ hd.wk hx.wk Prf.hyp0) hxy.wk)
  · refine .orE Prf.hyp0 ?_ Prf.hyp0
    exact .botE _ (positive_zero_absurd _ _
      (positive_multiply _ _ _ hd.wk.wk hx.wk.wk (negative_positive _ _ hd.wk.wk Prf.hyp0))
      (zero_value_congr _ _ _ hd.wk.wk (equal_symm (negative_product_right _ _ _)) (zero_negative _ _ hd.wk.wk hxy.wk.wk)))

theorem zero_product_reflect (d x y : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (hxy : Γ ⊢[PRAAx] isZero d (multiply d x y)) : Γ ⊢[PRAAx] isZero d x ⋎ isZero d y := by
  refine .orE (sign_trichotomy d x) ?_ ?_
  · exact .orI₂ (zero_product_positive_left _ _ _ hd.wk Prf.hyp0 hxy.wk)
  · refine .orE Prf.hyp0 ?_ (.orI₁ Prf.hyp0)
    exact .orI₂ (zero_product_positive_left d (negative x) y hd.wk.wk (negative_positive _ _ hd.wk.wk Prf.hyp0)
      (zero_value_congr _ _ _ hd.wk.wk (equal_symm (negative_product_left _ _ _)) (zero_negative _ _ hd.wk.wk hxy.wk.wk)))

theorem coefficient_equal_equivalent (d x y : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (h : Γ ⊢[PRAAx] equal x y) : Γ ⊢[PRAAx] equivalent d x y :=
  zero_value_congr _ _ _ hd (equal_symm (equal_trans (add_congr h (equal_refl (negative y))) (add_negative_self y))) (zero_isZero d hd)

def root : PTm n := QuadraticSignCertificates.naturalPair zero one
def natural (a : PTm n) : PTm n := QuadraticSignCertificates.naturalPair a zero
ipra_subst root [one]
ipra_subst natural
theorem root_cone : Γ ⊢[PRAAx] cone (root : PTm n) :=
  QuadraticSignCertificates.cone_natural zero one (le_congr (.eqRefl _) (LeanProofs.IPRA.zero_add _).eqSymm (le_refl _))
theorem root_positive (d : PTm n) (hd : Γ ⊢[PRAAx] le one d) : Γ ⊢[PRAAx] positive d root := cone_positive d root hd root_cone
theorem root_square_coefficients (d : PTm n) : Γ ⊢[PRAAx] equal (multiply d root root) (natural d) := by
  apply equal_of_values <;> simp only [root,natural,QuadraticSignCertificates.naturalPair,multiply_first,multiply_second,first_value,second_value,ZT.toZ_ofNat] <;> ipra_simps <;> ring
theorem root_square (d : PTm n) (hd : Γ ⊢[PRAAx] le one d) : Γ ⊢[PRAAx] equivalent d (multiply d root root) (natural d) :=
  coefficient_equal_equivalent d _ _ hd (root_square_coefficients d)

theorem actual_positive_quadratic_addition_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 0) ⟶ positive (var 0) (var 1) ⟶ positive (var 0) (var 2) ⟶ positive (var 0) (add (var 1) (var 2))) :=
  closeUniv 3 (.impI (.impI (.impI (positive_add _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))
theorem actual_positive_quadratic_product_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 0) ⟶ positive (var 0) (var 1) ⟶ positive (var 0) (var 2) ⟶ positive (var 0) (multiply (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (.impI (.impI (positive_multiply _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))
theorem actual_zero_quadratic_ideal_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 0) ⟶ isZero (var 0) (var 1) ⟶
      (isZero (var 0) (negative (var 1)) ⋏ (isZero (var 0) (multiply (var 0) (var 1) (var 2)) ⋏
        (isZero (var 0) (var 2) ⟶ isZero (var 0) (add (var 1) (var 2)))))) :=
  closeUniv 3 (.impI (.impI (.andI (zero_negative _ _ Prf.hyp1 Prf.hyp0)
    (.andI (zero_multiply _ _ _ Prf.hyp1 Prf.hyp0) (.impI (zero_add _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))))
theorem actual_quadratic_equality_equivalence_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 0) ⟶ (equivalent (var 0) (var 1) (var 1) ⋏
      ((equivalent (var 0) (var 1) (var 2) ⟶ equivalent (var 0) (var 2) (var 1)) ⋏
        (equivalent (var 0) (var 1) (var 2) ⟶ equivalent (var 0) (var 2) (var 3) ⟶ equivalent (var 0) (var 1) (var 3))))) :=
  closeUniv 4 (.impI (.andI (equivalent_refl _ _ Prf.hyp0)
    (.andI (.impI (equivalent_symm _ _ _ Prf.hyp1 Prf.hyp0))
      (.impI (.impI (equivalent_trans _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))))
theorem actual_quadratic_equality_operations_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 0) ⟶ equivalent (var 0) (var 1) (var 2) ⟶ equivalent (var 0) (var 3) (var 4) ⟶
      (equivalent (var 0) (add (var 1) (var 3)) (add (var 2) (var 4)) ⋏
        (equivalent (var 0) (multiply (var 0) (var 1) (var 3)) (multiply (var 0) (var 2) (var 4)) ⋏
          equivalent (var 0) (negative (var 1)) (negative (var 2))))) :=
  closeUniv 5 (.impI (.impI (.impI (.andI (equivalent_add _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)
    (.andI (equivalent_multiply _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0) (equivalent_negative _ _ _ Prf.hyp0.wk.wk Prf.hyp1))))))
theorem actual_quadratic_order_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 0) ⟶ (neg (less (var 0) (var 1) (var 1)) ⋏
      ((less (var 0) (var 1) (var 2) ⟶ less (var 0) (var 2) (var 3) ⟶ less (var 0) (var 1) (var 3)) ⋏
        (less (var 0) (var 1) (var 2) ⋎ (less (var 0) (var 2) (var 1) ⋎ equivalent (var 0) (var 1) (var 2)))))) :=
  closeUniv 4 (.impI (.andI (less_irrefl _ _ Prf.hyp0)
    (.andI (.impI (.impI (less_trans _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))) (ordered_trichotomy _ _ _ Prf.hyp0))))
theorem actual_quadratic_order_translation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 0) ⟶ less (var 0) (var 1) (var 2) ⟶ less (var 0) (add (var 1) (var 3)) (add (var 2) (var 3))) :=
  closeUniv 4 (.impI (.impI (less_translate _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_quadratic_order_congruence_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 0) ⟶ equivalent (var 0) (var 1) (var 2) ⟶ equivalent (var 0) (var 3) (var 4) ⟶
      less (var 0) (var 1) (var 3) ⟶ less (var 0) (var 2) (var 4)) :=
  closeUniv 5 (.impI (.impI (.impI (.impI (less_congr _ _ _ _ _ Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))
theorem actual_quadratic_zero_product_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 0) ⟶ isZero (var 0) (multiply (var 0) (var 1) (var 2)) ⟶ (isZero (var 0) (var 1) ⋎ isZero (var 0) (var 2))) :=
  closeUniv 3 (.impI (.impI (zero_product_reflect _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_positive_quadratic_root_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (le one (var 0) ⟶ (positive (var 0) root ⋏ equivalent (var 0) (multiply (var 0) root root) (natural (var 0)))) :=
  closeUniv 1 (.impI (.andI (root_positive _ Prf.hyp0) (root_square _ Prf.hyp0)))

end LeanProofs.IPRA.Algebra.QuadraticIntegerOrder
