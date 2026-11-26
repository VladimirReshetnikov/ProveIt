import IPRADerivations.Analysis.RationalArithmetic.RationalIntervalArithmeticPrecision
import IPRADerivations.Core.CongruenceTactic

/-!
# Actual positive interval arithmetic at any sufficient common offset

An arbitrary larger offset is exactly a later stage of the checked minimum
offset. The actual PR3 endpoint arrays therefore retain quantitative widths
and nesting, and satisfy the original regular-interval-name predicate.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalIntervalArithmeticNames

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)
open RationalNestedIntervals (read regular positiveWitness)
open RationalArgmin (rationalLE rationalLE_congr)
open RationalIntervalPowerComparison (stage powerEndpoint productEndpoint)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

theorem power_congr {q r e f : PTm n} (hq : Γ ⊢[PRAAx] q ≐ r) (he : Γ ⊢[PRAAx] e ≐ f) : Γ ⊢[PRAAx]
    RationalMultiplicativeConvexity.power q e ≐ RationalMultiplicativeConvexity.power r f := by
  ipra_congr (RationalMultiplicativeConvexity.power (var 0) (var 1) : PTm 2) with [hq, he]

theorem power_endpoint_congr (F : PR 3) {q r e f o v k l x y : PTm n}
    (hq : Γ ⊢[PRAAx] q ≐ r) (he : Γ ⊢[PRAAx] e ≐ f) (ho : Γ ⊢[PRAAx] o ≐ v)
    (hk : Γ ⊢[PRAAx] k ≐ l) (hx : Γ ⊢[PRAAx] x ≐ y) : Γ ⊢[PRAAx]
    powerEndpoint F q e o k x ≐ powerEndpoint F r f v l y :=
  power_congr (congrAp3 F hq (congrAdd (congrSucc (congrSucc hk)) ho) hx) he

theorem product_endpoint_congr (F : PR 3) {X Y V W a b c d o v k l x y : PTm n}
    (hX : Γ ⊢[PRAAx] X ≐ V) (hY : Γ ⊢[PRAAx] Y ≐ W) (ha : Γ ⊢[PRAAx] a ≐ c)
    (hb : Γ ⊢[PRAAx] b ≐ d) (ho : Γ ⊢[PRAAx] o ≐ v) (hk : Γ ⊢[PRAAx] k ≐ l)
    (hx : Γ ⊢[PRAAx] x ≐ y) : Γ ⊢[PRAAx] productEndpoint F X Y a b o k x ≐ productEndpoint F V W c d v l y :=
  RationalAlgebra.multiply_congr (power_endpoint_congr F hX ha ho hk hx) (power_endpoint_congr F hY hb ho hk hx)

theorem stage_translate (small o k : PTm n) (h : Γ ⊢[PRAAx] le small o) : Γ ⊢[PRAAx]
    stage o k ≐ stage small (k+monus o small) := by
  have e := natEq (eq_add_of_le h)
  apply deriveNat
  unfold stage
  ipra_simps
  linear_combination e

theorem power_translate (F : PR 3) (q e small o k x : PTm n) (h : Γ ⊢[PRAAx] le small o) : Γ ⊢[PRAAx]
    powerEndpoint F q e o k x ≐ powerEndpoint F q e small (k+monus o small) x :=
  power_congr (congrAp3 F (.eqRefl _) (stage_translate small o k h) (.eqRefl _)) (.eqRefl _)

theorem product_translate (F : PR 3) (X Y a b small o k x : PTm n) (h : Γ ⊢[PRAAx] le small o) : Γ ⊢[PRAAx]
    productEndpoint F X Y a b o k x ≐ productEndpoint F X Y a b small (k+monus o small) x :=
  RationalAlgebra.multiply_congr (power_translate F X a small o k x h) (power_translate F Y b small o k x h)

theorem scale_later (k d : PTm n) : Γ ⊢[PRAAx] le (RationalCubeGrid.scale k) (RationalCubeGrid.scale (k+d)) :=
  le_congr (one_mul _) ((mul_comm _ _).eqTrans (pw_add two k d).eqSymm)
    (mul_le_mul_right (pw two k) (RationalCubeGrid.scale_positive d))

theorem power_width (L U : PR 3) (q e p s o k x : PTm n)
    (h : Γ ⊢[PRAAx] regular L U q x) (hp : Γ ⊢[PRAAx] positiveWitness L q p s x)
    (ho : Γ ⊢[PRAAx] le (RationalIntervalArithmeticPrecision.offset U q q e p x) o) : Γ ⊢[PRAAx]
    RationalValueBounds.upper (powerEndpoint U q e o k x) (powerEndpoint L q e o k x) one (RationalCubeGrid.scale k) := by
  let small := RationalIntervalArithmeticPrecision.offset U q q e p x
  let d := monus o small
  have old := RationalIntervalArithmeticPrecision.power_endpoint_width L U q e p s (k+d) x h hp
  have moved := RationalValueBounds.upper_congr (power_translate U q e small o k x ho).eqSymm
    (power_translate L q e small o k x ho).eqSymm (.eqRefl _) (.eqRefl _) old
  exact RationalValueBounds.upper_mono _ _ _ _ _ _ (RationalCubeGrid.scale_positive (k+d)) moved
    (le_congr (one_mul _).eqSymm (one_mul _).eqSymm (scale_later k d))

theorem product_width (L U : PR 3) (X Y a b p sx sy o k x : PTm n)
    (hx : Γ ⊢[PRAAx] regular L U X x) (hy : Γ ⊢[PRAAx] regular L U Y x)
    (hpx : Γ ⊢[PRAAx] positiveWitness L X p sx x) (hpy : Γ ⊢[PRAAx] positiveWitness L Y p sy x)
    (ho : Γ ⊢[PRAAx] le (RationalIntervalArithmeticPrecision.offset U X Y (a+b) p x) o) : Γ ⊢[PRAAx]
    RationalValueBounds.upper (productEndpoint U X Y a b o k x) (productEndpoint L X Y a b o k x)
      one (RationalCubeGrid.scale k) := by
  let small := RationalIntervalArithmeticPrecision.offset U X Y (a+b) p x
  let d := monus o small
  have old := RationalIntervalArithmeticPrecision.product_endpoint_width L U X Y a b p sx sy (k+d) x hx hy hpx hpy
  have moved := RationalValueBounds.upper_congr (product_translate U X Y a b small o k x ho).eqSymm
    (product_translate L X Y a b small o k x ho).eqSymm (.eqRefl _) (.eqRefl _) old
  exact RationalValueBounds.upper_mono _ _ _ _ _ _ (RationalCubeGrid.scale_positive (k+d)) moved
    (le_congr (one_mul _).eqSymm (one_mul _).eqSymm (scale_later k d))

theorem power_nested (L U : PR 3) (q e p s o k l x : PTm n)
    (h : Γ ⊢[PRAAx] regular L U q x) (hp : Γ ⊢[PRAAx] positiveWitness L q p s x)
    (ho : Γ ⊢[PRAAx] le (RationalIntervalArithmeticPrecision.offset U q q e p x) o)
    (hkl : Γ ⊢[PRAAx] le k l) : Γ ⊢[PRAAx]
    rationalLE (powerEndpoint L q e o k x) (powerEndpoint L q e o l x) ⋏
      rationalLE (powerEndpoint U q e o l x) (powerEndpoint U q e o k x) := by
  let small := RationalIntervalArithmeticPrecision.offset U q q e p x
  let d := monus o small
  have result := RationalIntervalArithmeticPrecision.power_endpoint_nested L U q e p s (k+d) (l+d) x h hp
    (add_le_add_right d hkl)
  exact .andI (rationalLE_congr (power_translate L q e small o k x ho).eqSymm
      (power_translate L q e small o l x ho).eqSymm result.andE₁)
    (rationalLE_congr (power_translate U q e small o l x ho).eqSymm
      (power_translate U q e small o k x ho).eqSymm result.andE₂)

theorem product_nested (L U : PR 3) (X Y a b p sx sy o k l x : PTm n)
    (hx : Γ ⊢[PRAAx] regular L U X x) (hy : Γ ⊢[PRAAx] regular L U Y x)
    (hpx : Γ ⊢[PRAAx] positiveWitness L X p sx x) (hpy : Γ ⊢[PRAAx] positiveWitness L Y p sy x)
    (ho : Γ ⊢[PRAAx] le (RationalIntervalArithmeticPrecision.offset U X Y (a+b) p x) o)
    (hkl : Γ ⊢[PRAAx] le k l) : Γ ⊢[PRAAx]
    rationalLE (productEndpoint L X Y a b o k x) (productEndpoint L X Y a b o l x) ⋏
      rationalLE (productEndpoint U X Y a b o l x) (productEndpoint U X Y a b o k x) := by
  let small := RationalIntervalArithmeticPrecision.offset U X Y (a+b) p x
  let d := monus o small
  have result := RationalIntervalArithmeticPrecision.product_endpoint_nested L U X Y a b p sx sy (k+d) (l+d) x hx hy hpx hpy
    (add_le_add_right d hkl)
  exact .andI (rationalLE_congr (product_translate L X Y a b small o k x ho).eqSymm
      (product_translate L X Y a b small o l x ho).eqSymm result.andE₁)
    (rationalLE_congr (product_translate U X Y a b small o l x ho).eqSymm
      (product_translate U X Y a b small o k x ho).eqSymm result.andE₂)

def powerData (q e o : PTm n) : PTm n := pairT q (pairT e o)
def productData (X Y a b o : PTm n) : PTm n := pairT X (pairT Y (pairT a (pairT b o)))
def powerArray (F : PR 3) : PR 3 := PTm.toPR
  (powerEndpoint F (fstT (var 0)) (fstT (sndT (var 0))) (sndT (sndT (var 0))) (var 1) (var 2) : PTm 3)
def productArray (F : PR 3) : PR 3 := PTm.toPR
  (productEndpoint F (fstT (var 0)) (fstT (sndT (var 0))) (fstT (sndT (sndT (var 0))))
    (fstT (sndT (sndT (sndT (var 0))))) (sndT (sndT (sndT (sndT (var 0))))) (var 1) (var 2) : PTm 3)

@[simp] theorem subst_powerData {m : ℕ} (σ : Fin n → PTm m) (q e o : PTm n) :
    Syn.subst σ (powerData q e o) = powerData (Syn.subst σ q) (Syn.subst σ e) (Syn.subst σ o) := by simp [powerData]
@[simp] theorem subst_productData {m : ℕ} (σ : Fin n → PTm m) (X Y a b o : PTm n) :
    Syn.subst σ (productData X Y a b o) = productData (Syn.subst σ X) (Syn.subst σ Y)
      (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ o) := by simp [productData]

theorem power_at (F : PR 3) (q e o k x : PTm n) : Γ ⊢[PRAAx]
    read (powerArray F) (powerData q e o) k x ≐ powerEndpoint F q e o k x := by
  have h : Γ ⊢[PRAAx] read (powerArray F) (powerData q e o) k x ≐
      powerEndpoint F (fstT (powerData q e o)) (fstT (sndT (powerData q e o)))
        (sndT (sndT (powerData q e o))) k x := by
    simpa [RationalNestedIntervals.read,powerArray,ap3] using toPR_eq (Γ := Γ)
      (powerEndpoint F (fstT (var 0)) (fstT (sndT (var 0))) (sndT (sndT (var 0))) (var 1) (var 2) : PTm 3)
      ![powerData q e o,k,x]
  exact h.eqTrans (power_endpoint_congr F (fst_pair _ _)
    ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _))
    ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)) (.eqRefl _) (.eqRefl _))

theorem product_at (F : PR 3) (X Y a b o k x : PTm n) : Γ ⊢[PRAAx]
    read (productArray F) (productData X Y a b o) k x ≐ productEndpoint F X Y a b o k x := by
  have h : Γ ⊢[PRAAx] read (productArray F) (productData X Y a b o) k x ≐
      productEndpoint F (fstT (productData X Y a b o)) (fstT (sndT (productData X Y a b o)))
        (fstT (sndT (sndT (productData X Y a b o)))) (fstT (sndT (sndT (sndT (productData X Y a b o)))))
        (sndT (sndT (sndT (sndT (productData X Y a b o))))) k x := by
    simpa [RationalNestedIntervals.read,productArray,ap3] using toPR_eq (Γ := Γ)
      (productEndpoint F (fstT (var 0)) (fstT (sndT (var 0))) (fstT (sndT (sndT (var 0))))
        (fstT (sndT (sndT (sndT (var 0))))) (sndT (sndT (sndT (sndT (var 0))))) (var 1) (var 2) : PTm 3)
      ![productData X Y a b o,k,x]
  have first : Γ ⊢[PRAAx] sndT (productData X Y a b o) ≐ pairT Y (pairT a (pairT b o)) := snd_pair _ _
  have second := (congrSnd first).eqTrans (snd_pair _ _)
  have third := (congrSnd second).eqTrans (snd_pair _ _)
  exact h.eqTrans (product_endpoint_congr F (fst_pair _ _)
    ((congrFst first).eqTrans (fst_pair _ _)) ((congrFst second).eqTrans (fst_pair _ _))
    ((congrFst third).eqTrans (fst_pair _ _)) ((congrSnd third).eqTrans (snd_pair _ _)) (.eqRefl _) (.eqRefl _))

theorem power_step (L U : PR 3) (q e p s o k x : PTm n)
    (h : Γ ⊢[PRAAx] regular L U q x) (hp : Γ ⊢[PRAAx] positiveWitness L q p s x)
    (ho : Γ ⊢[PRAAx] le (RationalIntervalArithmeticPrecision.offset U q q e p x) o) : Γ ⊢[PRAAx]
    RationalNestedIntervals.intervalStep (powerArray L) (powerArray U) (powerData q e o) k x := by
  have nested := power_nested L U q e p s o k (succ k) x h hp ho (le_succ_self k)
  have hpo := le_trans (RationalIntervalArithmeticPrecision.offset_after_cutoff (Γ := Γ) U q q e p x) ho
  have pos := RationalIntervalPowerComparison.positive_witness_refine L U q p o s x h hp hpo
  have ordered := RationalIntervalPowerComparison.power_interval_ordered L U q e o (succ k) s x h pos
  have width := power_width L U q e p s o k x h hp ho
  exact .andI (rationalLE_congr (power_at L q e o k x).eqSymm (power_at L q e o (succ k) x).eqSymm nested.andE₁)
    (.andI (rationalLE_congr (power_at L q e o (succ k) x).eqSymm (power_at U q e o (succ k) x).eqSymm ordered)
      (.andI (rationalLE_congr (power_at U q e o (succ k) x).eqSymm (power_at U q e o k x).eqSymm nested.andE₂)
        (RationalValueBounds.upper_congr (power_at U q e o k x).eqSymm (power_at L q e o k x).eqSymm
          (.eqRefl _) (.eqRefl _) width)))

theorem product_step (L U : PR 3) (X Y a b p sx sy o k x : PTm n)
    (hx : Γ ⊢[PRAAx] regular L U X x) (hy : Γ ⊢[PRAAx] regular L U Y x)
    (hpx : Γ ⊢[PRAAx] positiveWitness L X p sx x) (hpy : Γ ⊢[PRAAx] positiveWitness L Y p sy x)
    (ho : Γ ⊢[PRAAx] le (RationalIntervalArithmeticPrecision.offset U X Y (a+b) p x) o) : Γ ⊢[PRAAx]
    RationalNestedIntervals.intervalStep (productArray L) (productArray U) (productData X Y a b o) k x := by
  have nested := product_nested L U X Y a b p sx sy o k (succ k) x hx hy hpx hpy ho (le_succ_self k)
  have hpo := le_trans (RationalIntervalArithmeticPrecision.offset_after_cutoff (Γ := Γ) U X Y (a+b) p x) ho
  have px := RationalIntervalPowerComparison.positive_witness_refine L U X p o sx x hx hpx hpo
  have py := RationalIntervalPowerComparison.positive_witness_refine L U Y p o sy x hy hpy hpo
  have ordered := RationalIntervalPowerComparison.product_interval_ordered L U X Y a b o (succ k) sx sy x hx hy px py
  have width := product_width L U X Y a b p sx sy o k x hx hy hpx hpy ho
  exact .andI (rationalLE_congr (product_at L X Y a b o k x).eqSymm (product_at L X Y a b o (succ k) x).eqSymm nested.andE₁)
    (.andI (rationalLE_congr (product_at L X Y a b o (succ k) x).eqSymm (product_at U X Y a b o (succ k) x).eqSymm ordered)
      (.andI (rationalLE_congr (product_at U X Y a b o (succ k) x).eqSymm (product_at U X Y a b o k x).eqSymm nested.andE₂)
        (RationalValueBounds.upper_congr (product_at U X Y a b o k x).eqSymm (product_at L X Y a b o k x).eqSymm
          (.eqRefl _) (.eqRefl _) width)))

theorem power_regular (L U : PR 3) (q e p s o x : PTm n)
    (h : Γ ⊢[PRAAx] regular L U q x) (hp : Γ ⊢[PRAAx] positiveWitness L q p s x)
    (ho : Γ ⊢[PRAAx] le (RationalIntervalArithmeticPrecision.offset U q q e p x) o) : Γ ⊢[PRAAx]
    regular (powerArray L) (powerArray U) (powerData q e o) x := by
  unfold regular
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] regular L U (Syn.shift q) (Syn.shift x) := by simpa [Fm.shift,Syn.shift] using h.shift
  have ps : Γ.map Fm.shift ⊢[PRAAx] positiveWitness L (Syn.shift q) (Syn.shift p) (Syn.shift s) (Syn.shift x) := by
    simpa [Fm.shift,positiveWitness,RationalConvexFiniteModulus.eps,Syn.shift] using hp.shift
  have os : Γ.map Fm.shift ⊢[PRAAx] le
      (RationalIntervalArithmeticPrecision.offset U (Syn.shift q) (Syn.shift q) (Syn.shift e) (Syn.shift p) (Syn.shift x))
      (Syn.shift o) := by simpa [Fm.shift,Syn.shift] using ho.shift
  simpa [Syn.shift] using power_step L U (Syn.shift q) (Syn.shift e) (Syn.shift p) (Syn.shift s) (Syn.shift o)
    (var 0) (Syn.shift x) hs ps os

theorem product_regular (L U : PR 3) (X Y a b p sx sy o x : PTm n)
    (hx : Γ ⊢[PRAAx] regular L U X x) (hy : Γ ⊢[PRAAx] regular L U Y x)
    (hpx : Γ ⊢[PRAAx] positiveWitness L X p sx x) (hpy : Γ ⊢[PRAAx] positiveWitness L Y p sy x)
    (ho : Γ ⊢[PRAAx] le (RationalIntervalArithmeticPrecision.offset U X Y (a+b) p x) o) : Γ ⊢[PRAAx]
    regular (productArray L) (productArray U) (productData X Y a b o) x := by
  unfold regular
  refine .allI ?_
  have xs : Γ.map Fm.shift ⊢[PRAAx] regular L U (Syn.shift X) (Syn.shift x) := by simpa [Fm.shift,Syn.shift] using hx.shift
  have ys : Γ.map Fm.shift ⊢[PRAAx] regular L U (Syn.shift Y) (Syn.shift x) := by simpa [Fm.shift,Syn.shift] using hy.shift
  have px : Γ.map Fm.shift ⊢[PRAAx] positiveWitness L (Syn.shift X) (Syn.shift p) (Syn.shift sx) (Syn.shift x) := by
    simpa [Fm.shift,positiveWitness,RationalConvexFiniteModulus.eps,Syn.shift] using hpx.shift
  have py : Γ.map Fm.shift ⊢[PRAAx] positiveWitness L (Syn.shift Y) (Syn.shift p) (Syn.shift sy) (Syn.shift x) := by
    simpa [Fm.shift,positiveWitness,RationalConvexFiniteModulus.eps,Syn.shift] using hpy.shift
  have os : Γ.map Fm.shift ⊢[PRAAx] le
      (RationalIntervalArithmeticPrecision.offset U (Syn.shift X) (Syn.shift Y) (Syn.shift a+Syn.shift b) (Syn.shift p) (Syn.shift x))
      (Syn.shift o) := by simpa [Fm.shift,Syn.shift] using ho.shift
  simpa [Syn.shift] using product_step L U (Syn.shift X) (Syn.shift Y) (Syn.shift a) (Syn.shift b) (Syn.shift p)
    (Syn.shift sx) (Syn.shift sy) (Syn.shift o) (var 0) (Syn.shift x) xs ys px py os

theorem power_center_at (L U : PR 3) (q e o k x : PTm n) : Γ ⊢[PRAAx]
    RationalNestedIntervals.center (powerArray L) (powerArray U) (powerData q e o) k x ≐
      RationalIntervalPowerComparison.powerCenter L U q e o k x :=
  RationalIntervalPowerComparison.midpoint_congr (power_at L q e o k x) (power_at U q e o k x)
theorem product_center_at (L U : PR 3) (X Y a b o k x : PTm n) : Γ ⊢[PRAAx]
    RationalNestedIntervals.center (productArray L) (productArray U) (productData X Y a b o) k x ≐
      RationalIntervalPowerComparison.productCenter L U X Y a b o k x :=
  RationalIntervalPowerComparison.midpoint_congr (product_at L X Y a b o k x) (product_at U X Y a b o k x)

def commonOffset (U : PR 3) (X Y Z a b p x : PTm n) : PTm n :=
  RationalIntervalArithmeticPrecision.offset U Z Z (a+b) p x+
    RationalIntervalArithmeticPrecision.offset U X Y (a+b) p x
@[simp] theorem subst_commonOffset {m : ℕ} (σ : Fin n → PTm m) (U : PR 3) (X Y Z a b p x : PTm n) :
    Syn.subst σ (commonOffset U X Y Z a b p x) = commonOffset U (Syn.subst σ X) (Syn.subst σ Y)
      (Syn.subst σ Z) (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ p) (Syn.subst σ x) := by simp [commonOffset]
theorem common_offset_power (U : PR 3) (X Y Z a b p x : PTm n) : Γ ⊢[PRAAx]
    le (RationalIntervalArithmeticPrecision.offset U Z Z (a+b) p x) (commonOffset U X Y Z a b p x) := by
  unfold commonOffset
  ipra_le 𝔟 (RationalIntervalArithmeticPrecision.offset U X Y (a+b) p x)
theorem common_offset_product (U : PR 3) (X Y Z a b p x : PTm n) : Γ ⊢[PRAAx]
    le (RationalIntervalArithmeticPrecision.offset U X Y (a+b) p x) (commonOffset U X Y Z a b p x) := by
  unfold commonOffset
  ipra_le 𝔟 (RationalIntervalArithmeticPrecision.offset U Z Z (a+b) p x)

theorem common_names_regular (L U : PR 3) (X Y Z a b p sx sy sz x : PTm n)
    (h : Γ ⊢[PRAAx] RationalIntervalPowerComparison.input L U X Y Z p p sx sy sz x) : Γ ⊢[PRAAx]
    regular (powerArray L) (powerArray U) (powerData Z (a+b) (commonOffset U X Y Z a b p x)) x ⋏
      regular (productArray L) (productArray U) (productData X Y a b (commonOffset U X Y Z a b p x)) x :=
  .andI (power_regular L U Z (a+b) p sz (commonOffset U X Y Z a b p x) x h.andE₂.andE₂.andE₁
      h.andE₂.andE₂.andE₂.andE₂.andE₂.andE₁ (common_offset_power U X Y Z a b p x))
    (product_regular L U X Y a b p sx sy (commonOffset U X Y Z a b p x) x h.andE₁ h.andE₂.andE₁
      h.andE₂.andE₂.andE₂.andE₁ h.andE₂.andE₂.andE₂.andE₂.andE₁ (common_offset_product U X Y Z a b p x))

def output (U : PR 3) (X Y Z a b p x : PTm n) : PTm n :=
  pairT (powerData Z (a+b) (commonOffset U X Y Z a b p x))
    (pairT (productData X Y a b (commonOffset U X Y Z a b p x)) (commonOffset U X Y Z a b p x))
def outputF (U : PR 3) : PR 7 := PTm.toPR (output U (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))
def run (U : PR 3) (X Y Z a b p x : PTm n) : PTm n := PTm.app (outputF U) ![X,Y,Z,a,b,p,x]
@[simp] theorem subst_output {m : ℕ} (σ : Fin n → PTm m) (U : PR 3) (X Y Z a b p x : PTm n) :
    Syn.subst σ (output U X Y Z a b p x) = output U (Syn.subst σ X) (Syn.subst σ Y) (Syn.subst σ Z)
      (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ p) (Syn.subst σ x) := by simp [output]
@[simp] theorem subst_run {m : ℕ} (σ : Fin n → PTm m) (U : PR 3) (X Y Z a b p x : PTm n) :
    Syn.subst σ (run U X Y Z a b p x) = run U (Syn.subst σ X) (Syn.subst σ Y) (Syn.subst σ Z)
      (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ p) (Syn.subst σ x) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl
theorem program_at (U : PR 3) (X Y Z a b p x : PTm n) : Γ ⊢[PRAAx]
    run U X Y Z a b p x ≐ output U X Y Z a b p x := by
  simpa [run,outputF] using toPR_eq (Γ := Γ)
    (output U (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) : PTm 7) ![X,Y,Z,a,b,p,x]
theorem returned_power_data (U : PR 3) (X Y Z a b p x : PTm n) : Γ ⊢[PRAAx]
    fstT (run U X Y Z a b p x) ≐ powerData Z (a+b) (commonOffset U X Y Z a b p x) :=
  (congrFst (program_at U X Y Z a b p x)).eqTrans (fst_pair _ _)
theorem returned_product_data (U : PR 3) (X Y Z a b p x : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (run U X Y Z a b p x)) ≐ productData X Y a b (commonOffset U X Y Z a b p x) :=
  (congrFst ((congrSnd (program_at U X Y Z a b p x)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_offset (U : PR 3) (X Y Z a b p x : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (run U X Y Z a b p x)) ≐ commonOffset U X Y Z a b p x :=
  (congrSnd ((congrSnd (program_at U X Y Z a b p x)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)

theorem actual_stage_translation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le (var 0) (var 1) ⟶ stage (var 1) (var 2) ≐ stage (var 0) (var 2+monus (var 1) (var 0))) :=
  closeUniv 3 (.impI (stage_translate _ _ _ Prf.hyp0))
theorem actual_power_array_closed (F : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (read (powerArray F) (powerData (var 0) (var 1) (var 2)) (var 3) (var 4) ≐
      powerEndpoint F (var 0) (var 1) (var 2) (var 3) (var 4)) := closeUniv 5 (power_at F _ _ _ _ _)
theorem actual_product_array_closed (F : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (read (productArray F) (productData (var 0) (var 1) (var 2) (var 3) (var 4)) (var 5) (var 6) ≐
      productEndpoint F (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) := closeUniv 7 (product_at F _ _ _ _ _ _ _)
theorem actual_power_name_regular_closed (L U : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (regular L U (var 0) (var 5) ⟶ positiveWitness L (var 0) (var 2) (var 3) (var 5) ⟶
      le (RationalIntervalArithmeticPrecision.offset U (var 0) (var 0) (var 1) (var 2) (var 5)) (var 4) ⟶
      regular (powerArray L) (powerArray U) (powerData (var 0) (var 1) (var 4)) (var 5)) :=
  closeUniv 6 (.impI (.impI (.impI (power_regular L U _ _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))
theorem actual_product_name_regular_closed (L U : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (regular L U (var 0) (var 8) ⟶ regular L U (var 1) (var 8) ⟶
      positiveWitness L (var 0) (var 4) (var 5) (var 8) ⟶ positiveWitness L (var 1) (var 4) (var 6) (var 8) ⟶
      le (RationalIntervalArithmeticPrecision.offset U (var 0) (var 1) (var 2+var 3) (var 4) (var 8)) (var 7) ⟶
      regular (productArray L) (productArray U) (productData (var 0) (var 1) (var 2) (var 3) (var 7)) (var 8)) :=
  closeUniv 9 (.impI (.impI (.impI (.impI (.impI (product_regular L U _ _ _ _ _ _ _ _ _
    Prf.hyp0.wk.wk.wk.wk Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))))
theorem actual_common_names_regular_closed (L U : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    (RationalIntervalPowerComparison.input L U (var 0) (var 1) (var 2) (var 5) (var 5) (var 6) (var 7) (var 8) (var 9) ⟶
      (regular (powerArray L) (powerArray U)
          (powerData (var 2) (var 3+var 4) (commonOffset U (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 9))) (var 9) ⋏
        regular (productArray L) (productArray U)
          (productData (var 0) (var 1) (var 3) (var 4) (commonOffset U (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 9))) (var 9))) :=
  closeUniv 10 (.impI (common_names_regular L U _ _ _ _ _ _ _ _ _ _ Prf.hyp0))
theorem actual_common_data_program_closed (U : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (run U (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ≐
      output U (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) := closeUniv 7 (program_at U _ _ _ _ _ _ _)
theorem actual_returned_common_offset_closed (U : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (sndT (sndT (run U (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))) ≐
      commonOffset U (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) := closeUniv 7 (returned_offset U _ _ _ _ _ _ _)

end LeanProofs.IPRA.Analysis.RationalIntervalArithmeticNames
