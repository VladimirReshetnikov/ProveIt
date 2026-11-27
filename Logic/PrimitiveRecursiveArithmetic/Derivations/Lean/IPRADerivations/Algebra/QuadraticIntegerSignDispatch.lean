import IPRADerivations.Algebra.QuadraticTowerSignRecipe
import IPRADerivations.Algebra.QuadraticIntegerEmbedding

/-!
# The source three-query dispatch at an actual integer quadratic stage

Source `isoperimetric_ipra.tex` section2.3. Native integer coefficients,
the actual norm and the existing cone-certified sign are used directly.
This local stage theorem is distinct from correctness of the numerical
tower scheduler over an arbitrary valid lower ordered domain.
-/

set_option autoImplicit false
set_option linter.unnecessarySeqFocus false

namespace LeanProofs.IPRA.Algebra.QuadraticIntegerSignDispatch

open_ipra
open QuadraticSignCertificates
open QuadraticConeOrder (equal_of_values equal_first equal_second)
open QuadraticIntegerEmbedding (integer integer_sign integer_equal integer_positive integer_isNegative integer_isZero integer_tag_classification)
open QuadraticTowerSignRecipe (dispatch tagProduct)
open LeanProofs.IPRA.Foundations.GuardedTotalization (sel sel_one sel_zero)
open LeanProofs.IPRA.Foundations.BoundedReflection

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

theorem tag_value_congr (a b : ZT n) (h : Γ ⊢[PRAAx] ZT.eq a b) : Γ ⊢[PRAAx] tag a ≐ tag b :=
  (integer_sign one a (le_refl one)).eqSymm.eqTrans
    ((QuadraticConeOrder.sign_congr one (integer a) (integer b) (le_refl one) (integer_equal a b h)).eqTrans
      (integer_sign one b (le_refl one)))
theorem tag_of_positive (a : ZT n) (h : Γ ⊢[PRAAx] zle (ZT.ofNat one) a) : Γ ⊢[PRAAx] tag a ≐ one :=
  (integer_sign one a (le_refl one)).eqSymm.eqTrans (integer_positive one a (le_refl one) h)
theorem tag_of_negative (a : ZT n) (h : Γ ⊢[PRAAx] zle (ZT.ofNat one) (-a)) : Γ ⊢[PRAAx] tag a ≐ two :=
  (integer_sign one a (le_refl one)).eqSymm.eqTrans (integer_isNegative one a (le_refl one) h)
theorem tag_of_zero (a : ZT n) (h : Γ ⊢[PRAAx] ZT.eq a (ZT.ofNat zero)) : Γ ⊢[PRAAx] tag a ≐ zero :=
  (integer_sign one a (le_refl one)).eqSymm.eqTrans (integer_isZero one a (le_refl one) h)

theorem strict_nonnegative (a : ZT n) (h : Γ ⊢[PRAAx] zle (ZT.ofNat one) a) : Γ ⊢[PRAAx] zle (ZT.ofNat zero) a := by
  have hn : Nonneg Γ (ZT.toZ Γ a-1) := by simpa only [zsl_def,ZT.toZ_ofNat,Q.mk_one,map_one] using nn_zsl h
  exact nonnegative_of_value a (by convert nn_add nn_one hn using 1 <;> ring)
theorem negative_nonpositive (a : ZT n) (h : Γ ⊢[PRAAx] zle (ZT.ofNat one) (-a)) : Γ ⊢[PRAAx] zle a (ZT.ofNat zero) := by
  have hn := nn_zle0 (strict_nonnegative (-a) h)
  exact zle_of_comb _ (by simp only [ZT.toZ_neg,ZT.toZ_ofNat,Q.mk_zero,map_zero]; ring) hn
theorem strict_negative (a : ZT n) (h : Γ ⊢[PRAAx] zle (ZT.ofNat one) a) : Γ ⊢[PRAAx] neg (ZT.eq a (ZT.ofNat zero)) := by
  refine .impI ?_
  let Δ := ZT.eq a (ZT.ofNat zero) :: Γ
  have hs : Δ ⊢[PRAAx] zle (ZT.ofNat one) a := h.wk
  have hz : Δ ⊢[PRAAx] ZT.eq a (ZT.ofNat zero) := Prf.hyp0
  have hn := nn_zsl hs
  have bad : Nonneg Δ (-1) := by
    have ev : zsl hs = -1 := by rw [zsl_def,ZT.toZ_eq hz,ZT.toZ_ofNat,ZT.toZ_ofNat]; ipra_simps; ring
    simpa only [ev] using hn
  exact false_of_comb (-1) rfl bad _

theorem multiply_code_congr {d e x u y v : PTm n} (hd : Γ ⊢[PRAAx] d ≐ e)
    (hx : Γ ⊢[PRAAx] x ≐ u) (hy : Γ ⊢[PRAAx] y ≐ v) : Γ ⊢[PRAAx]
    multiply d x y ≐ multiply e u v := by
  ipra_congr (multiply (var 0) (var 1) (var 2) : PTm 3) with [hd, hx, hy]

theorem positive_mass_first (x : PTm n) (ha : Γ ⊢[PRAAx] zle (ZT.ofNat one) (first x)) : Γ ⊢[PRAAx] le one (mass x) := by
  have h : Nonneg Γ (ZT.toZ Γ (first x)-1) := by simpa only [zsl_def,ZT.toZ_ofNat,Q.mk_one,map_one] using nn_zsl ha
  apply le_of_nonneg
  simp only [mass,Q.mk_add,map_add,Q.mk_one,map_one]
  rw [magnitude_nonnegative _ (strict_nonnegative _ ha)]
  convert nn_add h (nn_term (magnitude (second x))) using 1 <;> ring
theorem negative_mass_first (x : PTm n) (ha : Γ ⊢[PRAAx] zle (ZT.ofNat one) (-first x)) : Γ ⊢[PRAAx] le one (mass x) := by
  have h : Nonneg Γ (-ZT.toZ Γ (first x)-1) := by simpa only [zsl_def,ZT.toZ_neg,ZT.toZ_ofNat,Q.mk_one,map_one] using nn_zsl ha
  apply le_of_nonneg
  simp only [mass,Q.mk_add,map_add,Q.mk_one,map_one]
  rw [magnitude_nonpositive _ (negative_nonpositive _ ha)]
  convert nn_add h (nn_term (magnitude (second x))) using 1 <;> ring

theorem positive_opposite_sign (d x : PTm n)
    (ha : Γ ⊢[PRAAx] zle (ZT.ofNat one) (first x))
    (hb : Γ ⊢[PRAAx] zle (ZT.ofNat one) (-second x)) : Γ ⊢[PRAAx]
    sign d x ≐ tag (norm d x) := by
  have code := multiply_code_congr (.eqRefl d) (multiplier_nonzero x (positive_mass_first x ha)) (.eqRefl x)
  have productEq := positive_opposite_conjugation d x (strict_nonnegative _ ha) (negative_nonpositive _ hb)
  apply tag_value_congr
  apply ZT.derive
  change ZT.toZ Γ (first (product d x)+second (product d x)) = ZT.toZ Γ (norm d x)
  simp only [ZT.toZ_add,product]
  rw [first_code_value code,second_code_value code,equal_first productEq,equal_second productEq,
    first_value,second_value,ZT.toZ_ofNat]
  ipra_simps
  ring
theorem negative_opposite_sign (d x : PTm n)
    (ha : Γ ⊢[PRAAx] zle (ZT.ofNat one) (-first x))
    (hb : Γ ⊢[PRAAx] zle (ZT.ofNat one) (second x)) : Γ ⊢[PRAAx]
    sign d x ≐ tag (-norm d x) := by
  have code := multiply_code_congr (.eqRefl d) (multiplier_nonzero x (negative_mass_first x ha)) (.eqRefl x)
  have productEq := negative_opposite_conjugation d x (negative_nonpositive _ ha) (strict_nonnegative _ hb)
  apply tag_value_congr
  apply ZT.derive
  change ZT.toZ Γ (first (product d x)+second (product d x)) = ZT.toZ Γ (-norm d x)
  simp only [ZT.toZ_add,product]
  rw [first_code_value code,second_code_value code,equal_first productEq,equal_second productEq,
    first_value,second_value,ZT.toZ_ofNat]
  ipra_simps
  ring

theorem zero_second_sign (d x : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (hb : Γ ⊢[PRAAx] ZT.eq (second x) (ZT.ofNat zero)) : Γ ⊢[PRAAx] sign d x ≐ tag (first x) := by
  have same : Γ ⊢[PRAAx] equal x (integer (first x)) := equal_of_values
    (QuadraticIntegerEmbedding.integer_first _).symm
    (by rw [ZT.toZ_eq hb,QuadraticIntegerEmbedding.integer_second,ZT.toZ_ofNat]; ipra_simps)
  exact (QuadraticConeOrder.sign_congr d x _ hd same).eqTrans (integer_sign d (first x) hd)

theorem positive_coefficients_sign (d x : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (ha : Γ ⊢[PRAAx] zle (ZT.ofNat zero) (first x)) (hb : Γ ⊢[PRAAx] zle (ZT.ofNat zero) (second x))
    (hs : Γ ⊢[PRAAx] zle (ZT.ofNat one) (first x+second x)) : Γ ⊢[PRAAx] sign d x ≐ one :=
  QuadraticIntegerOrder.cone_positive d x hd (.andI ha (.andI hb hs))
theorem negative_coefficients_sign (d x : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (ha : Γ ⊢[PRAAx] zle (first x) (ZT.ofNat zero)) (hb : Γ ⊢[PRAAx] zle (second x) (ZT.ofNat zero))
    (hs : Γ ⊢[PRAAx] zle (ZT.ofNat one) (-(first x+second x))) : Γ ⊢[PRAAx] sign d x ≐ two := by
  have negCone : Γ ⊢[PRAAx] cone (negative x) :=
    .andI (nonnegative_of_value _ (by
      rw [negative_first]
      simpa only [zsl_def,ZT.toZ_ofNat,Q.mk_zero,map_zero,_root_.zero_sub] using nn_zsl ha))
      (.andI (nonnegative_of_value _ (by
        rw [negative_second]
        simpa only [zsl_def,ZT.toZ_ofNat,Q.mk_zero,map_zero,_root_.zero_sub] using nn_zsl hb))
        (zle_of_comb (zsl hs) (by simp only [zsl_def,ZT.toZ_add,ZT.toZ_neg,negative_first,negative_second,ZT.toZ_ofNat]; ring) (nn_zsl hs)))
  exact QuadraticConeOrder.sign_unique_negative d x oneCode hd QuadraticIntegerOrder.cone_one
    (QuadraticConeOrder.cone_congr (QuadraticConeOrder.equal_symm (QuadraticConeOrder.negative_congr (QuadraticIntegerOrder.multiply_one_left d x))) negCone)

theorem nonzero_one : Γ ⊢[PRAAx] neg ((one : PTm n) ≐ zero) := .impI (succ_ne_zero' _ Prf.hyp0)
theorem nonzero_two : Γ ⊢[PRAAx] neg ((two : PTm n) ≐ zero) := .impI (succ_ne_zero' _ Prf.hyp0)
theorem different_one_two : Γ ⊢[PRAAx] neg ((one : PTm n) ≐ two) := .impI (QuadraticIntegerOrder.one_two_absurd _ Prf.hyp0)
theorem different_two_one : Γ ⊢[PRAAx] neg ((two : PTm n) ≐ one) := Order.ne_symm different_one_two

theorem tag_product_one_one : Γ ⊢[PRAAx] tagProduct (one : PTm n) one ≐ one :=
  (sel_zero (eqb_of_ne nonzero_one)).eqTrans ((sel_zero (eqb_of_ne nonzero_one)).eqTrans (sel_one (eqb_of_eq (.eqRefl _))))
theorem tag_product_one_two : Γ ⊢[PRAAx] tagProduct (one : PTm n) two ≐ two :=
  (sel_zero (eqb_of_ne nonzero_one)).eqTrans ((sel_zero (eqb_of_ne nonzero_two)).eqTrans (sel_zero (eqb_of_ne different_one_two)))
theorem tag_product_two_one : Γ ⊢[PRAAx] tagProduct (two : PTm n) one ≐ two :=
  (sel_zero (eqb_of_ne nonzero_two)).eqTrans ((sel_zero (eqb_of_ne nonzero_one)).eqTrans (sel_zero (eqb_of_ne different_two_one)))
theorem tag_product_two_two : Γ ⊢[PRAAx] tagProduct (two : PTm n) two ≐ one :=
  (sel_zero (eqb_of_ne nonzero_two)).eqTrans ((sel_zero (eqb_of_ne nonzero_two)).eqTrans (sel_one (eqb_of_eq (.eqRefl _))))

theorem tag_product_unit (a : ZT n) : Γ ⊢[PRAAx] tagProduct one (tag a) ≐ tag a := by
  refine .orE (integer_tag_classification a) ?_ ?_
  · exact ((QuadraticTowerSignRecipe.tag_product_congr (.eqRefl _) (Prf.andE₁ Prf.hyp0)).eqTrans tag_product_one_one).eqTrans (Prf.andE₁ Prf.hyp0).eqSymm
  · refine .orE Prf.hyp0 ?_ ?_
    · exact ((QuadraticTowerSignRecipe.tag_product_congr (.eqRefl _) (Prf.andE₁ Prf.hyp0)).eqTrans tag_product_one_two).eqTrans (Prf.andE₁ Prf.hyp0).eqSymm
    · exact (QuadraticTowerSignRecipe.tag_product_zero_right _ _ (Prf.andE₁ Prf.hyp0)).eqTrans (Prf.andE₁ Prf.hyp0).eqSymm
theorem tag_product_unit_right (a : ZT n) : Γ ⊢[PRAAx] tagProduct (tag a) one ≐ tag a := by
  refine .orE (integer_tag_classification a) ?_ ?_
  · exact ((QuadraticTowerSignRecipe.tag_product_congr (Prf.andE₁ Prf.hyp0) (.eqRefl _)).eqTrans tag_product_one_one).eqTrans (Prf.andE₁ Prf.hyp0).eqSymm
  · refine .orE Prf.hyp0 ?_ ?_
    · exact ((QuadraticTowerSignRecipe.tag_product_congr (Prf.andE₁ Prf.hyp0) (.eqRefl _)).eqTrans tag_product_two_one).eqTrans (Prf.andE₁ Prf.hyp0).eqSymm
    · exact (QuadraticTowerSignRecipe.tag_product_zero_left _ _ (Prf.andE₁ Prf.hyp0)).eqTrans (Prf.andE₁ Prf.hyp0).eqSymm
theorem tag_product_negative (a : ZT n) : Γ ⊢[PRAAx] tagProduct two (tag a) ≐ tag (-a) := by
  refine .orE (integer_tag_classification a) ?_ ?_
  · have negPositive : (tag a ≐ one ⋏ zle (ZT.ofNat one) a) :: Γ ⊢[PRAAx] zle (ZT.ofNat one) (-(-a)) :=
      zle_of_comb _ (by simp only [zsl_def,ZT.toZ_neg,ZT.toZ_ofNat]; ring) (nn_zsl (Prf.andE₂ Prf.hyp0))
    exact ((QuadraticTowerSignRecipe.tag_product_congr (.eqRefl _) (Prf.andE₁ Prf.hyp0)).eqTrans tag_product_two_one).eqTrans
      (tag_of_negative (-a) negPositive).eqSymm
  · refine .orE Prf.hyp0 ?_ ?_
    · exact ((QuadraticTowerSignRecipe.tag_product_congr (.eqRefl _) (Prf.andE₁ Prf.hyp0)).eqTrans tag_product_two_two).eqTrans
        (tag_of_positive (-a) (Prf.andE₂ Prf.hyp0)).eqSymm
    · have za : (tag a ≐ zero ⋏ ZT.eq a (ZT.ofNat zero)) :: (tag a ≐ two ⋏ zle (ZT.ofNat one) (-a) ⋎ (tag a ≐ zero ⋏ ZT.eq a (ZT.ofNat zero))) :: Γ ⊢[PRAAx]
          ZT.eq (-a) (ZT.ofNat zero) := by
        apply ZT.derive
        rw [ZT.toZ_neg,ZT.toZ_eq (Prf.andE₂ Prf.hyp0),ZT.toZ_ofNat]
        ipra_simps
        ring
      exact (QuadraticTowerSignRecipe.tag_product_zero_right _ _ (Prf.andE₁ Prf.hyp0)).eqTrans (tag_of_zero (-a) za).eqSymm

def third (d x : PTm n) : PTm n := sel (eqb (tag (first x)) zero) (tag (ZT.ofNat d)) (tag (norm d x))
def recipe (d x : PTm n) : PTm n := dispatch (tag (first x)) (tag (second x)) (third d x)
ipra_subst third [sel]
ipra_subst recipe

theorem nonzero_from_code {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) (hb : Γ ⊢[PRAAx] neg (b ≐ zero)) : Γ ⊢[PRAAx] neg (a ≐ zero) :=
  .impI (.impE hb.wk (h.wk.eqSymm.eqTrans Prf.hyp0))
theorem different_from_codes {a b c d : PTm n} (ha : Γ ⊢[PRAAx] a ≐ c) (hb : Γ ⊢[PRAAx] b ≐ d)
    (hd : Γ ⊢[PRAAx] neg (c ≐ d)) : Γ ⊢[PRAAx] neg (a ≐ b) :=
  .impI (.impE hd.wk (ha.wk.eqSymm.eqTrans (Prf.hyp0.eqTrans hb.wk)))
theorem third_when_nonzero (d x : PTm n) (ha : Γ ⊢[PRAAx] neg (tag (first x) ≐ zero)) : Γ ⊢[PRAAx]
    third d x ≐ tag (norm d x) := sel_zero (eqb_of_ne ha)
theorem third_when_zero (d x : PTm n) (ha : Γ ⊢[PRAAx] tag (first x) ≐ zero) : Γ ⊢[PRAAx]
    third d x ≐ tag (ZT.ofNat d) := sel_one (eqb_of_eq ha)
theorem natural_tag (d : PTm n) (hd : Γ ⊢[PRAAx] le one d) : Γ ⊢[PRAAx] tag (ZT.ofNat d) ≐ one :=
  tag_of_positive _ (zle_of_comb _ (by simp only [sl_def,ZT.toZ_ofNat]) (nn_sl hd))

theorem strict_sum (a b : ZT n) (ha : Γ ⊢[PRAAx] zle (ZT.ofNat one) a)
    (hb : Γ ⊢[PRAAx] zle (ZT.ofNat zero) b) : Γ ⊢[PRAAx] zle (ZT.ofNat one) (a+b) :=
  zle_of_comb (zsl ha+zsl hb) (by simp only [zsl_def,ZT.toZ_add,ZT.toZ_ofNat]; ipra_simps; ring) (nn_add (nn_zsl ha) (nn_zsl hb))
theorem negative_strict_sum (a b : ZT n) (ha : Γ ⊢[PRAAx] zle (ZT.ofNat one) (-a))
    (hb : Γ ⊢[PRAAx] zle b (ZT.ofNat zero)) : Γ ⊢[PRAAx] zle (ZT.ofNat one) (-(a+b)) :=
  zle_of_comb (zsl ha+zsl hb) (by simp only [zsl_def,ZT.toZ_add,ZT.toZ_neg,ZT.toZ_ofNat]; ipra_simps; ring) (nn_add (nn_zsl ha) (nn_zsl hb))

theorem zero_first_sign (d x : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (ha : Γ ⊢[PRAAx] ZT.eq (first x) (ZT.ofNat zero)) : Γ ⊢[PRAAx] sign d x ≐ tag (second x) := by
  refine .orE (integer_tag_classification (second x)) ?_ ?_
  · let Δ := (tag (second x) ≐ one ⋏ zle (ZT.ofNat one) (second x)) :: Γ
    have hz : Δ ⊢[PRAAx] ZT.eq (first x) (ZT.ofNat zero) := ha.wk
    have ha0 := ZT.toZ_eq hz
    have haNonneg : (tag (second x) ≐ one ⋏ zle (ZT.ofNat one) (second x)) :: Γ ⊢[PRAAx] zle (ZT.ofNat zero) (first x) :=
      nonnegative_of_value _ (by rw [ha0,ZT.toZ_ofNat]; exact nn_zero)
    have sum : (tag (second x) ≐ one ⋏ zle (ZT.ofNat one) (second x)) :: Γ ⊢[PRAAx] zle (ZT.ofNat one) (first x+second x) :=
      zle_of_comb (zsl (Prf.andE₂ (Prf.hyp0))) (by simp only [zsl_def,ZT.toZ_add]; rw [ha0,ZT.toZ_ofNat]; ipra_simps; ring) (nn_zsl (Prf.andE₂ Prf.hyp0))
    exact (positive_coefficients_sign d x hd.wk haNonneg (strict_nonnegative _ (Prf.andE₂ Prf.hyp0)) sum).eqTrans (Prf.andE₁ Prf.hyp0).eqSymm
  · refine .orE Prf.hyp0 ?_ ?_
    · let Δ := (tag (second x) ≐ two ⋏ zle (ZT.ofNat one) (-second x)) ::
        (tag (second x) ≐ two ⋏ zle (ZT.ofNat one) (-second x) ⋎ (tag (second x) ≐ zero ⋏ ZT.eq (second x) (ZT.ofNat zero))) :: Γ
      have hz : Δ ⊢[PRAAx] ZT.eq (first x) (ZT.ofNat zero) := ha.wk.wk
      have ha0 := ZT.toZ_eq hz
      have haNonpos : (tag (second x) ≐ two ⋏ zle (ZT.ofNat one) (-second x)) :: _ ⊢[PRAAx] zle (first x) (ZT.ofNat zero) :=
        zle_of_comb 0 (by rw [ha0,ZT.toZ_ofNat]; ipra_simps; ring) nn_zero
      have sum : (tag (second x) ≐ two ⋏ zle (ZT.ofNat one) (-second x)) :: _ ⊢[PRAAx] zle (ZT.ofNat one) (-(first x+second x)) :=
        zle_of_comb (zsl (Prf.andE₂ (Prf.hyp0))) (by simp only [zsl_def,ZT.toZ_neg,ZT.toZ_add]; rw [ha0,ZT.toZ_ofNat]; ipra_simps; ring) (nn_zsl (Prf.andE₂ Prf.hyp0))
      exact (negative_coefficients_sign d x hd.wk.wk haNonpos (negative_nonpositive _ (Prf.andE₂ Prf.hyp0)) sum).eqTrans (Prf.andE₁ Prf.hyp0).eqSymm
    · exact ((zero_second_sign d x hd.wk.wk (Prf.andE₂ Prf.hyp0)).eqTrans (tag_of_zero _ ha.wk.wk)).eqTrans (Prf.andE₁ Prf.hyp0).eqSymm

theorem positive_first_recipe (d x : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (ha : Γ ⊢[PRAAx] zle (ZT.ofNat one) (first x)) : Γ ⊢[PRAAx] recipe d x ≐ sign d x := by
  refine .orE (integer_tag_classification (second x)) ?_ ?_
  · have aTag : (tag (second x) ≐ one ⋏ zle (ZT.ofNat one) (second x)) :: Γ ⊢[PRAAx] tag (first x) ≐ one := tag_of_positive _ ha.wk
    have bt : (tag (second x) ≐ one ⋏ zle (ZT.ofNat one) (second x)) :: Γ ⊢[PRAAx] tag (second x) ≐ one := Prf.andE₁ Prf.hyp0
    have disp : (tag (second x) ≐ one ⋏ zle (ZT.ofNat one) (second x)) :: Γ ⊢[PRAAx] recipe d x ≐ tag (first x) :=
      QuadraticTowerSignRecipe.dispatch_same _ _ _ (nonzero_from_code aTag nonzero_one) (nonzero_from_code bt nonzero_one) (aTag.eqTrans bt.eqSymm)
    exact (disp.eqTrans aTag).eqTrans (positive_coefficients_sign d x hd.wk (strict_nonnegative _ ha.wk)
      (strict_nonnegative _ (Prf.andE₂ Prf.hyp0)) (strict_sum _ _ ha.wk (strict_nonnegative _ (Prf.andE₂ Prf.hyp0)))).eqSymm
  · refine .orE Prf.hyp0 ?_ ?_
    · have aTag : (tag (second x) ≐ two ⋏ zle (ZT.ofNat one) (-second x)) :: (tag (second x) ≐ two ⋏ zle (ZT.ofNat one) (-second x) ⋎ (tag (second x) ≐ zero ⋏ ZT.eq (second x) (ZT.ofNat zero))) :: Γ ⊢[PRAAx] tag (first x) ≐ one := tag_of_positive _ ha.wk.wk
      have bt : (tag (second x) ≐ two ⋏ zle (ZT.ofNat one) (-second x)) :: (tag (second x) ≐ two ⋏ zle (ZT.ofNat one) (-second x) ⋎ (tag (second x) ≐ zero ⋏ ZT.eq (second x) (ZT.ofNat zero))) :: Γ ⊢[PRAAx] tag (second x) ≐ two := Prf.andE₁ Prf.hyp0
      have an := nonzero_from_code aTag nonzero_one
      have disp : (tag (second x) ≐ two ⋏ zle (ZT.ofNat one) (-second x)) :: _ ⊢[PRAAx]
          recipe d x ≐ tagProduct (tag (first x)) (third d x) :=
        QuadraticTowerSignRecipe.dispatch_opposite _ _ _ an (nonzero_from_code bt nonzero_two) (different_from_codes aTag bt different_one_two)
      exact disp.eqTrans ((QuadraticTowerSignRecipe.tag_product_congr aTag (third_when_nonzero d x an)).eqTrans
        ((tag_product_unit (norm d x)).eqTrans (positive_opposite_sign d x ha.wk.wk (Prf.andE₂ Prf.hyp0)).eqSymm))
    · have aTag : (tag (second x) ≐ zero ⋏ ZT.eq (second x) (ZT.ofNat zero)) :: (tag (second x) ≐ two ⋏ zle (ZT.ofNat one) (-second x) ⋎ (tag (second x) ≐ zero ⋏ ZT.eq (second x) (ZT.ofNat zero))) :: Γ ⊢[PRAAx] tag (first x) ≐ one := tag_of_positive _ ha.wk.wk
      have disp : (tag (second x) ≐ zero ⋏ ZT.eq (second x) (ZT.ofNat zero)) :: _ ⊢[PRAAx] recipe d x ≐ tag (first x) :=
        QuadraticTowerSignRecipe.dispatch_b_zero _ _ _ (nonzero_from_code aTag nonzero_one) (Prf.andE₁ Prf.hyp0)
      exact disp.eqTrans (zero_second_sign d x hd.wk.wk (Prf.andE₂ Prf.hyp0)).eqSymm

theorem negative_first_recipe (d x : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (ha : Γ ⊢[PRAAx] zle (ZT.ofNat one) (-first x)) : Γ ⊢[PRAAx] recipe d x ≐ sign d x := by
  refine .orE (integer_tag_classification (second x)) ?_ ?_
  · have aTag : (tag (second x) ≐ one ⋏ zle (ZT.ofNat one) (second x)) :: Γ ⊢[PRAAx] tag (first x) ≐ two := tag_of_negative _ ha.wk
    have bt : (tag (second x) ≐ one ⋏ zle (ZT.ofNat one) (second x)) :: Γ ⊢[PRAAx] tag (second x) ≐ one := Prf.andE₁ Prf.hyp0
    have an := nonzero_from_code aTag nonzero_two
    have disp : (tag (second x) ≐ one ⋏ zle (ZT.ofNat one) (second x)) :: Γ ⊢[PRAAx]
        recipe d x ≐ tagProduct (tag (first x)) (third d x) :=
      QuadraticTowerSignRecipe.dispatch_opposite _ _ _ an (nonzero_from_code bt nonzero_one) (different_from_codes aTag bt different_two_one)
    exact disp.eqTrans ((QuadraticTowerSignRecipe.tag_product_congr aTag (third_when_nonzero d x an)).eqTrans
      ((tag_product_negative (norm d x)).eqTrans (negative_opposite_sign d x ha.wk (Prf.andE₂ Prf.hyp0)).eqSymm))
  · refine .orE Prf.hyp0 ?_ ?_
    · have aTag : (tag (second x) ≐ two ⋏ zle (ZT.ofNat one) (-second x)) :: (tag (second x) ≐ two ⋏ zle (ZT.ofNat one) (-second x) ⋎ (tag (second x) ≐ zero ⋏ ZT.eq (second x) (ZT.ofNat zero))) :: Γ ⊢[PRAAx] tag (first x) ≐ two := tag_of_negative _ ha.wk.wk
      have bt : (tag (second x) ≐ two ⋏ zle (ZT.ofNat one) (-second x)) :: (tag (second x) ≐ two ⋏ zle (ZT.ofNat one) (-second x) ⋎ (tag (second x) ≐ zero ⋏ ZT.eq (second x) (ZT.ofNat zero))) :: Γ ⊢[PRAAx] tag (second x) ≐ two := Prf.andE₁ Prf.hyp0
      have disp : (tag (second x) ≐ two ⋏ zle (ZT.ofNat one) (-second x)) :: _ ⊢[PRAAx] recipe d x ≐ tag (first x) :=
        QuadraticTowerSignRecipe.dispatch_same _ _ _ (nonzero_from_code aTag nonzero_two) (nonzero_from_code bt nonzero_two) (aTag.eqTrans bt.eqSymm)
      exact (disp.eqTrans aTag).eqTrans (negative_coefficients_sign d x hd.wk.wk (negative_nonpositive _ ha.wk.wk)
        (negative_nonpositive _ (Prf.andE₂ Prf.hyp0)) (negative_strict_sum _ _ ha.wk.wk (negative_nonpositive _ (Prf.andE₂ Prf.hyp0)))).eqSymm
    · have aTag : (tag (second x) ≐ zero ⋏ ZT.eq (second x) (ZT.ofNat zero)) :: (tag (second x) ≐ two ⋏ zle (ZT.ofNat one) (-second x) ⋎ (tag (second x) ≐ zero ⋏ ZT.eq (second x) (ZT.ofNat zero))) :: Γ ⊢[PRAAx] tag (first x) ≐ two := tag_of_negative _ ha.wk.wk
      have disp : (tag (second x) ≐ zero ⋏ ZT.eq (second x) (ZT.ofNat zero)) :: _ ⊢[PRAAx] recipe d x ≐ tag (first x) :=
        QuadraticTowerSignRecipe.dispatch_b_zero _ _ _ (nonzero_from_code aTag nonzero_two) (Prf.andE₁ Prf.hyp0)
      exact disp.eqTrans (zero_second_sign d x hd.wk.wk (Prf.andE₂ Prf.hyp0)).eqSymm

theorem zero_first_recipe (d x : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (ha : Γ ⊢[PRAAx] ZT.eq (first x) (ZT.ofNat zero)) : Γ ⊢[PRAAx] recipe d x ≐ sign d x :=
  (QuadraticTowerSignRecipe.dispatch_a_zero _ _ _ (tag_of_zero _ ha)).eqTrans
    ((QuadraticTowerSignRecipe.tag_product_congr (.eqRefl _) ((third_when_zero d x (tag_of_zero _ ha)).eqTrans (natural_tag d hd))).eqTrans
      ((tag_product_unit_right (second x)).eqTrans (zero_first_sign d x hd ha).eqSymm))

theorem positive_radicand_dispatch (d x : PTm n) (hd : Γ ⊢[PRAAx] le one d) : Γ ⊢[PRAAx] recipe d x ≐ sign d x := by
  refine .orE (integer_tag_classification (first x)) (positive_first_recipe d x hd.wk (Prf.andE₂ Prf.hyp0)) ?_
  exact .orE Prf.hyp0 (negative_first_recipe d x hd.wk.wk (Prf.andE₂ Prf.hyp0))
    (zero_first_recipe d x hd.wk.wk (Prf.andE₂ Prf.hyp0))

theorem dispatch_third_congr (s t u v : PTm n) (hu : Γ ⊢[PRAAx] u ≐ v) : Γ ⊢[PRAAx]
    dispatch s t u ≐ dispatch s t v := by
  ipra_congr (dispatch (var 0) (var 1) (var 2) : PTm 3) with [.eqRefl s, .eqRefl t, hu]

theorem dispatch_nonzero_unit (a : ZT n) (t : PTm n) (ha : Γ ⊢[PRAAx] neg (tag a ≐ zero)) : Γ ⊢[PRAAx]
    dispatch (tag a) t one ≐ tag a := by
  have middle : Γ ⊢[PRAAx]
      sel (eqb t zero) (tag a) (sel (eqb (tag a) t) (tag a) (tagProduct (tag a) one)) ≐ tag a := by
    refine .orE (eqb_cases t zero) ?_ ?_
    · refine (sel_zero Prf.hyp0).eqTrans ?_
      refine .orE (eqb_cases (tag a) t) ?_ ?_
      · exact (sel_zero Prf.hyp0).eqTrans (tag_product_unit_right a)
      · exact sel_one Prf.hyp0
    · exact sel_one Prf.hyp0
  exact (sel_zero (eqb_of_ne ha)).eqTrans middle

theorem positive_square (a : ZT n) (ha : Γ ⊢[PRAAx] zle (ZT.ofNat one) a) : Γ ⊢[PRAAx]
    zle (ZT.ofNat one) (a*a) := by
  have low : Nonneg Γ (ZT.toZ Γ a-1) := by simpa only [zsl_def,ZT.toZ_ofNat,Q.mk_one,map_one] using nn_zsl ha
  have high : Nonneg Γ (ZT.toZ Γ a+1) := nn_add (nn_zle0 (strict_nonnegative a ha)) nn_one
  exact zle_of_comb ((ZT.toZ Γ a-1)*(ZT.toZ Γ a+1))
    (by simp only [ZT.toZ_mul,ZT.toZ_ofNat]; ipra_simps; ring) (nn_mul low high)

theorem zero_norm_tag_positive (x : PTm n) (ha : Γ ⊢[PRAAx] zle (ZT.ofNat one) (first x)) : Γ ⊢[PRAAx]
    tag (norm zero x) ≐ one := by
  have hn : Γ ⊢[PRAAx] ZT.eq (norm zero x) (first x*first x) := by
    ipra_lc [norm]
  exact (tag_value_congr _ _ hn).eqTrans (tag_of_positive _ (positive_square _ ha))
theorem zero_norm_tag_negative (x : PTm n) (ha : Γ ⊢[PRAAx] zle (ZT.ofNat one) (-first x)) : Γ ⊢[PRAAx]
    tag (norm zero x) ≐ one := by
  have hn : Γ ⊢[PRAAx] ZT.eq (norm zero x) ((-first x)*(-first x)) := by
    ipra_lc [norm]
  exact (tag_value_congr _ _ hn).eqTrans (tag_of_positive _ (positive_square _ ha))

/-- The redundant zero extension is actually projected; no positive-d
cone theorem is invoked at zero. -/
theorem zero_radicand_dispatch (x : PTm n) : Γ ⊢[PRAAx] recipe zero x ≐ tag (first x) := by
  refine .orE (integer_tag_classification (first x)) ?_ ?_
  · let Δ := (tag (first x) ≐ one ⋏ zle (ZT.ofNat one) (first x)) :: Γ
    have an : Δ ⊢[PRAAx] neg (tag (first x) ≐ zero) := nonzero_from_code (Prf.andE₁ Prf.hyp0) nonzero_one
    have thirdOne : Δ ⊢[PRAAx] third zero x ≐ one :=
      (third_when_nonzero zero x an).eqTrans (zero_norm_tag_positive x (Prf.andE₂ Prf.hyp0))
    exact (dispatch_third_congr _ _ _ _ thirdOne).eqTrans (dispatch_nonzero_unit (first x) (tag (second x)) an)
  · refine .orE Prf.hyp0 ?_ ?_
    · let Δ := (tag (first x) ≐ two ⋏ zle (ZT.ofNat one) (-first x)) ::
        (tag (first x) ≐ two ⋏ zle (ZT.ofNat one) (-first x) ⋎ (tag (first x) ≐ zero ⋏ ZT.eq (first x) (ZT.ofNat zero))) :: Γ
      have an : Δ ⊢[PRAAx] neg (tag (first x) ≐ zero) := nonzero_from_code (Prf.andE₁ Prf.hyp0) nonzero_two
      have thirdOne : Δ ⊢[PRAAx] third zero x ≐ one :=
        (third_when_nonzero zero x an).eqTrans (zero_norm_tag_negative x (Prf.andE₂ Prf.hyp0))
      exact (dispatch_third_congr _ _ _ _ thirdOne).eqTrans (dispatch_nonzero_unit (first x) (tag (second x)) an)
    · have ha : (tag (first x) ≐ zero ⋏ ZT.eq (first x) (ZT.ofNat zero)) ::
          (tag (first x) ≐ two ⋏ zle (ZT.ofNat one) (-first x) ⋎ (tag (first x) ≐ zero ⋏ ZT.eq (first x) (ZT.ofNat zero))) :: Γ ⊢[PRAAx]
          tag (first x) ≐ zero := Prf.andE₁ Prf.hyp0
      have thirdZero := (third_when_zero zero x ha).eqTrans (tag_of_zero _ (ZT.derive rfl))
      exact (QuadraticTowerSignRecipe.dispatch_a_zero _ _ _ ha).eqTrans
        ((QuadraticTowerSignRecipe.tag_product_zero_right _ _ thirdZero).eqTrans ha.eqSymm)

def uniformSign (d x : PTm n) : PTm n := sel (eqb d zero) (tag (first x)) (sign d x)
ipra_subst uniformSign [sel]
theorem recipe_radicand_congr {d e : PTm n} (x : PTm n) (hd : Γ ⊢[PRAAx] d ≐ e) : Γ ⊢[PRAAx] recipe d x ≐ recipe e x := by
  ipra_congr (recipe (var 0) (var 1) : PTm 2) with [hd, .eqRefl x]

/-- All numerical natural radicands, with the actual zero projection branch. -/
theorem uniform_dispatch (d x : PTm n) : Γ ⊢[PRAAx] recipe d x ≐ uniformSign d x := by
  refine .orE (zero_or_succ d) ?_ ?_
  · exact ((recipe_radicand_congr x Prf.hyp0).eqTrans (zero_radicand_dispatch x)).eqTrans
      (sel_one (eqb_of_eq Prf.hyp0)).eqSymm
  · have hd : (d ≐ succ (PTm.pred d)) :: Γ ⊢[PRAAx] le one d :=
      Order.zero_lt_of_eq_succ Prf.hyp0
    have dn : (d ≐ succ (PTm.pred d)) :: Γ ⊢[PRAAx] neg (d ≐ zero) :=
      nonzero_from_code Prf.hyp0 (.impI (succ_ne_zero' _ Prf.hyp0))
    exact (positive_radicand_dispatch d x hd).eqTrans (sel_zero (eqb_of_ne dn)).eqSymm

/-! The actual program retains both independently specified signs, the
literal conditional third tag and the original native norm code. -/
def output (d x : PTm n) : PTm n := pairT (recipe d x) (pairT (uniformSign d x) (pairT (third d x) (code (norm d x))))
def outputF : PR 2 := PTm.toPR (output (var 0) (var 1))
def run (d x : PTm n) : PTm n := ap2 outputF d x
ipra_subst output
ipra_subst run
theorem program_at (d x : PTm n) : Γ ⊢[PRAAx] run d x ≐ output d x := by
  simpa [run,outputF,ap2] using toPR_eq (Γ := Γ) (output (var 0) (var 1) : PTm 2) ![d,x]
theorem returned_recipe (d x : PTm n) : Γ ⊢[PRAAx] fstT (run d x) ≐ recipe d x :=
  (program_at d x).fstE
theorem returned_tail (d x : PTm n) : Γ ⊢[PRAAx] sndT (run d x) ≐ pairT (uniformSign d x) (pairT (third d x) (code (norm d x))) :=
  (program_at d x).sndE
theorem returned_uniform (d x : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run d x)) ≐ uniformSign d x :=
  (returned_tail d x).fstE
theorem returned_pair (d x : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run d x)) ≐ pairT (third d x) (code (norm d x)) :=
  (returned_tail d x).sndE
theorem returned_third (d x : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run d x))) ≐ third d x :=
  (returned_pair d x).fstE
theorem returned_norm (d x : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (run d x))) ≐ code (norm d x) :=
  (returned_pair d x).sndE
theorem returned_equal (d x : PTm n) : Γ ⊢[PRAAx] fstT (run d x) ≐ fstT (sndT (run d x)) :=
  (returned_recipe d x).eqTrans ((uniform_dispatch d x).eqTrans (returned_uniform d x).eqSymm)
theorem returned_positive_sign (d x : PTm n) (hd : Γ ⊢[PRAAx] le one d) : Γ ⊢[PRAAx]
    fstT (run d x) ≐ sign d x := (returned_recipe d x).eqTrans (positive_radicand_dispatch d x hd)
theorem returned_zero_projection (x : PTm n) : Γ ⊢[PRAAx]
    fstT (run zero x) ≐ tag (first x) := (returned_recipe zero x).eqTrans (zero_radicand_dispatch x)

theorem actual_integer_positive_opposite_sign_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (zle (ZT.ofNat one) (first (var 1)) ⟶ zle (ZT.ofNat one) (-second (var 1)) ⟶
      sign (var 0) (var 1) ≐ tag (norm (var 0) (var 1))) :=
  closeUniv 2 (.impI (.impI (positive_opposite_sign _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_integer_negative_opposite_sign_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (zle (ZT.ofNat one) (-first (var 1)) ⟶ zle (ZT.ofNat one) (second (var 1)) ⟶
      sign (var 0) (var 1) ≐ tag (-norm (var 0) (var 1))) :=
  closeUniv 2 (.impI (.impI (negative_opposite_sign _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_integer_positive_radicand_dispatch_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (var 0) ⟶ recipe (var 0) (var 1) ≐ sign (var 0) (var 1)) :=
  closeUniv 2 (.impI (positive_radicand_dispatch _ _ Prf.hyp0))
theorem actual_integer_zero_radicand_dispatch_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (recipe zero (var 0) ≐ tag (first (var 0))) := closeUniv 1 (zero_radicand_dispatch _)
theorem actual_integer_uniform_dispatch_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (recipe (var 0) (var 1) ≐ uniformSign (var 0) (var 1)) := closeUniv 2 (uniform_dispatch _ _)
theorem actual_integer_dispatch_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (run (var 0) (var 1) ≐ output (var 0) (var 1)) := closeUniv 2 (program_at _ _)
theorem actual_returned_integer_dispatch_equal_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (fstT (run (var 0) (var 1)) ≐ fstT (sndT (run (var 0) (var 1)))) := closeUniv 2 (returned_equal _ _)
theorem actual_returned_integer_positive_dispatch_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (var 0) ⟶ fstT (run (var 0) (var 1)) ≐ sign (var 0) (var 1)) :=
  closeUniv 2 (.impI (returned_positive_sign _ _ Prf.hyp0))
theorem actual_returned_integer_zero_dispatch_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (fstT (run zero (var 0)) ≐ tag (first (var 0))) := closeUniv 1 (returned_zero_projection _)

end LeanProofs.IPRA.Algebra.QuadraticIntegerSignDispatch
