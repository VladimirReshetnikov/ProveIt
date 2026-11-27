import IPRADerivations.Algebra.QuadraticTowerMultiplicationDistributivity
import IPRADerivations.Algebra.QuadraticTowerMultiplicationRecurrence

/-!
# Associativity of the actual numerical tower multiplication

The explicit cap covers original computed inner products. The actual
five-call table and the same finite forward state are retained. Local
lower associative, distributive and height instances are tracked by
bounded word predicates, rather than supplied as final output laws.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Algebra.QuadraticTowerMultiplicationAssociativity

open_ipra
open LeanProofs.IPRA.Analysis
open QuadraticTowerCoefficients (width singleton)
open QuadraticTowerArrayCodec (arrayHeight horizon code normalized)
open QuadraticTowerCoefficientArithmetic (added equalValues)
open QuadraticTowerScalarBudget (amp growth)
open QuadraticTowerMultiplicationTable (lookup budget recipe leftHalf rightHalf)
open QuadraticTowerMultiplicationHeight (radicandsHeight word cap state)
open LeanProofs.IPRA.Foundations.BoundedSyntax (BFm formula)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def productHeight (h b : PTm n) : PTm n := growth (QuadraticTowerGrowth.path h) b
ipra_subst productHeight

def rowLaw (h B D T b u v w : PTm n) : Fm PTm n := le (productHeight h b) B ⟶ radicandsHeight D h b ⟶
  arrayHeight h (word h b u) b ⟶ arrayHeight h (word h b v) b ⟶ arrayHeight h (word h b w) b ⟶
    lookup h B T (lookup h B T (word h b u) (word h b v)) (word h b w) ≐
      lookup h B T (word h b u) (lookup h B T (word h b v) (word h b w))
def atSecond (h B D T b u v : PTm n) : Fm PTm n := .all
  (lt (var 0) (Syn.shift (horizon h b)) ⟶ rowLaw (Syn.shift h) (Syn.shift B) (Syn.shift D)
    (Syn.shift T) (Syn.shift b) (Syn.shift u) (Syn.shift v) (var 0))
def atWord (h B D T b u : PTm n) : Fm PTm n := .all
  (lt (var 0) (Syn.shift (horizon h b)) ⟶ atSecond (Syn.shift h) (Syn.shift B)
    (Syn.shift D) (Syn.shift T) (Syn.shift b) (Syn.shift u) (var 0))
def atHeight (h B D T b : PTm n) : Fm PTm n := .all
  (lt (var 0) (Syn.shift (horizon h b)) ⟶ atWord (Syn.shift h) (Syn.shift B)
    (Syn.shift D) (Syn.shift T) (Syn.shift b) (var 0))
def localLaw (h B D T : PTm n) : Fm PTm n := .all
  (lt (var 0) (succ (Syn.shift B)) ⟶ atHeight (Syn.shift h) (Syn.shift B)
    (Syn.shift D) (Syn.shift T) (var 0))
ipra_subst rowLaw
@[simp] theorem subst_atSecond {k : ℕ} (σ : Fin n → PTm k) (h B D T b u v : PTm n) :
    (atSecond h B D T b u v).subst σ = atSecond (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ D)
      (Syn.subst σ T) (Syn.subst σ b) (Syn.subst σ u) (Syn.subst σ v) := by
  simp [atSecond,Syn.subst_shift,Syn.shift_subst]
  simp only [Syn.shift,QuadraticTowerArrayCodec.subst_horizon,Syn.subst_subst]
@[simp] theorem subst_atWord {k : ℕ} (σ : Fin n → PTm k) (h B D T b u : PTm n) :
    (atWord h B D T b u).subst σ = atWord (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ D)
      (Syn.subst σ T) (Syn.subst σ b) (Syn.subst σ u) := by
  simp [atWord,Syn.subst_shift,Syn.shift_subst]
  simp only [Syn.shift,QuadraticTowerArrayCodec.subst_horizon,Syn.subst_subst]
@[simp] theorem subst_atHeight {k : ℕ} (σ : Fin n → PTm k) (h B D T b : PTm n) :
    (atHeight h B D T b).subst σ = atHeight (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ D)
      (Syn.subst σ T) (Syn.subst σ b) := by
  simp [atHeight,Syn.subst_shift,Syn.shift_subst]
  simp only [Syn.shift,QuadraticTowerArrayCodec.subst_horizon,Syn.subst_subst]
ipra_subst localLaw [Syn.subst_shift, Syn.shift_subst]

def rowSyntax (h B D T b u v w : PTm n) : BFm n := .imp (.le (productHeight h b) B)
  (.imp (QuadraticTowerMultiplicationHeight.radicandsSyntax D h b)
    (.imp (QuadraticTowerMultiplicationHeight.heightSyntax h (word h b u) b)
      (.imp (QuadraticTowerMultiplicationHeight.heightSyntax h (word h b v) b)
        (.imp (QuadraticTowerMultiplicationHeight.heightSyntax h (word h b w) b)
          (.eq (lookup h B T (lookup h B T (word h b u) (word h b v)) (word h b w))
            (lookup h B T (word h b u) (lookup h B T (word h b v) (word h b w))))))))
def secondSyntax (h B D T b u v : PTm n) : BFm n := .all (horizon h b)
  (rowSyntax (Syn.shift h) (Syn.shift B) (Syn.shift D) (Syn.shift T) (Syn.shift b) (Syn.shift u) (Syn.shift v) (var 0))
def wordSyntax (h B D T b u : PTm n) : BFm n := .all (horizon h b)
  (secondSyntax (Syn.shift h) (Syn.shift B) (Syn.shift D) (Syn.shift T) (Syn.shift b) (Syn.shift u) (var 0))
def heightRowsSyntax (h B D T b : PTm n) : BFm n := .all (horizon h b)
  (wordSyntax (Syn.shift h) (Syn.shift B) (Syn.shift D) (Syn.shift T) (Syn.shift b) (var 0))
def localSyntax (h B D T : PTm n) : BFm n := .all (succ B)
  (heightRowsSyntax (Syn.shift h) (Syn.shift B) (Syn.shift D) (Syn.shift T) (var 0))
theorem row_formula (h B D T b u v w : PTm n) : formula (rowSyntax h B D T b u v w) = rowLaw h B D T b u v w := by
  simp [rowSyntax,rowLaw,formula,QuadraticTowerMultiplicationHeight.radicands_formula,
    QuadraticTowerMultiplicationHeight.height_formula,BFm.le,le]
theorem second_formula (h B D T b u v : PTm n) : formula (secondSyntax h B D T b u v) = atSecond h B D T b u v := by
  simp [secondSyntax,atSecond,formula,row_formula]
theorem word_formula (h B D T b u : PTm n) : formula (wordSyntax h B D T b u) = atWord h B D T b u := by
  simp [wordSyntax,atWord,formula,second_formula]
theorem height_rows_formula (h B D T b : PTm n) : formula (heightRowsSyntax h B D T b) = atHeight h B D T b := by
  simp [heightRowsSyntax,atHeight,formula,word_formula]
theorem local_formula (h B D T : PTm n) : formula (localSyntax h B D T) = localLaw h B D T := by
  simp [localSyntax,localLaw,formula,height_rows_formula,Syn.shift]

theorem local_at (h B D T b u v w : PTm n) (hL : Γ ⊢[PRAAx] localLaw h B D T)
    (hb : Γ ⊢[PRAAx] le (productHeight h b) B) (hu : Γ ⊢[PRAAx] lt u (horizon h b))
    (hv : Γ ⊢[PRAAx] lt v (horizon h b)) (hw : Γ ⊢[PRAAx] lt w (horizon h b))
    (hD : Γ ⊢[PRAAx] radicandsHeight D h b) (ha : Γ ⊢[PRAAx] arrayHeight h (word h b u) b)
    (hc : Γ ⊢[PRAAx] arrayHeight h (word h b v) b) (he : Γ ⊢[PRAAx] arrayHeight h (word h b w) b) : Γ ⊢[PRAAx]
    lookup h B T (lookup h B T (word h b u) (word h b v)) (word h b w) ≐
      lookup h B T (word h b u) (lookup h B T (word h b v) (word h b w)) := by
  have bound := le_trans (QuadraticTowerGrowth.growth_inflation (QuadraticTowerGrowth.path h) b) hb
  have bg : Γ ⊢[PRAAx] lt b (succ B) ⟶ atHeight h B D T b := by simpa [localLaw] using hL.allE b
  have ug : Γ ⊢[PRAAx] lt u (horizon h b) ⟶ atWord h B D T b u := by
    simpa [atHeight] using (Prf.impE bg ((succ_monus_succ _ _).eqTrans bound)).allE u
  have vg : Γ ⊢[PRAAx] lt v (horizon h b) ⟶ atSecond h B D T b u v := by
    simpa [atWord] using (Prf.impE ug hu).allE v
  have wg : Γ ⊢[PRAAx] lt w (horizon h b) ⟶ rowLaw h B D T b u v w := by
    simpa [atSecond] using (Prf.impE vg hv).allE w
  exact .impE (.impE (.impE (.impE (.impE (.impE wg hw) hb) hD) ha) hc) he

theorem values_of_equal (h A C : PTm n) (eq : Γ ⊢[PRAAx] A ≐ C) : Γ ⊢[PRAAx] equalValues h A C := by
  have proof := Prf.eqSubst (Γ := Γ) (Ax := PRAAx) (equalValues (var 0) (var 1) (var 2) : Fm PTm 3)
    ![h,A,A] ![h,A,C] (fun i => by fin_cases i; exact .eqRefl _; exact .eqRefl _; exact eq)
      (by simpa using QuadraticTowerMultiplicationZero.values_refl (Γ := Γ) h A)
  simpa using proof

theorem lookup_associative (h B D T A C E b : PTm n) (hL : Γ ⊢[PRAAx] localLaw h B D T)
    (hb : Γ ⊢[PRAAx] le (productHeight h b) B) (hD : Γ ⊢[PRAAx] radicandsHeight D h b)
    (ha : Γ ⊢[PRAAx] arrayHeight h A b) (hc : Γ ⊢[PRAAx] arrayHeight h C b)
    (he : Γ ⊢[PRAAx] arrayHeight h E b) : Γ ⊢[PRAAx]
    lookup h B T (lookup h B T A C) E ≐ lookup h B T A (lookup h B T C E) := by
  have middle := local_at h B D T b (code h A b) (code h C b) (code h E b) hL hb
    (QuadraticTowerArrayCodec.code_bound h A b ha) (QuadraticTowerArrayCodec.code_bound h C b hc)
    (QuadraticTowerArrayCodec.code_bound h E b he) hD
    (QuadraticTowerMultiplicationHeight.restored_height h A b b ha (le_refl _))
    (QuadraticTowerMultiplicationHeight.restored_height h C b b hc (le_refl _))
    (QuadraticTowerMultiplicationHeight.restored_height h E b b he (le_refl _))
  have av := QuadraticTowerMultiplicationCoherence.restored_values h A b ha
  have cv := QuadraticTowerMultiplicationCoherence.restored_values h C b hc
  have ev := QuadraticTowerMultiplicationCoherence.restored_values h E b he
  have ac := QuadraticTowerOperandProperness.lookup_proper h B T _ A _ C av cv
  have ce := QuadraticTowerOperandProperness.lookup_proper h B T _ C _ E cv ev
  exact (QuadraticTowerOperandProperness.lookup_proper h B T _ (lookup h B T A C) _ E
    (values_of_equal _ _ _ ac) ev).eqSymm.eqTrans
      (middle.eqTrans (QuadraticTowerOperandProperness.lookup_proper h B T _ A _ (lookup h B T C E)
        av (values_of_equal _ _ _ ce)))

theorem quartic_move (h B D T a b c d r : PTm n) (hL : Γ ⊢[PRAAx] localLaw h B D T)
    (hComm : Γ ⊢[PRAAx] QuadraticTowerMultiplicationCommutativity.localLaw h B D T)
    (hr : Γ ⊢[PRAAx] le (productHeight h r) B) (hD : Γ ⊢[PRAAx] radicandsHeight D h r)
    (ha : Γ ⊢[PRAAx] arrayHeight h a r) (hb : Γ ⊢[PRAAx] arrayHeight h b r)
    (hc : Γ ⊢[PRAAx] arrayHeight h c r) (hd : Γ ⊢[PRAAx] arrayHeight h d r)
    (hab : Γ ⊢[PRAAx] arrayHeight h (lookup h B T a b) r) : Γ ⊢[PRAAx]
    lookup h B T (lookup h B T (lookup h B T a b) d) c ≐
      lookup h B T (lookup h B T a (lookup h B T b c)) d := by
  have comm := QuadraticTowerMultiplicationCommutativity.lookup_commutative h B D T d c r hComm
    (le_trans (QuadraticTowerGrowth.growth_inflation (QuadraticTowerGrowth.path h) r) hr) hD hd hc
  exact (lookup_associative h B D T (lookup h B T a b) d c r hL hr hD hab hd hc).eqTrans
    ((QuadraticTowerMultiplicationCoherence.lookup_congr (.eqRefl h) (.eqRefl B) (.eqRefl T) (.eqRefl _) comm).eqTrans
      ((lookup_associative h B D T (lookup h B T a b) c d r hL hr hD hab hc hd).eqSymm.eqTrans
        (QuadraticTowerMultiplicationCoherence.lookup_congr (.eqRefl h) (.eqRefl B) (.eqRefl T)
          (lookup_associative h B D T a b c r hL hr hD ha hb hc) (.eqRefl d))))

theorem quartic_right (h B D T a b c d r : PTm n) (hL : Γ ⊢[PRAAx] localLaw h B D T)
    (hr : Γ ⊢[PRAAx] le (productHeight h r) B) (hD : Γ ⊢[PRAAx] radicandsHeight D h r)
    (ha : Γ ⊢[PRAAx] arrayHeight h a r) (hb : Γ ⊢[PRAAx] arrayHeight h b r)
    (hc : Γ ⊢[PRAAx] arrayHeight h c r) (hd : Γ ⊢[PRAAx] arrayHeight h d r)
    (hbc : Γ ⊢[PRAAx] arrayHeight h (lookup h B T b c) r) : Γ ⊢[PRAAx]
    lookup h B T (lookup h B T (lookup h B T a b) c) d ≐
      lookup h B T a (lookup h B T (lookup h B T b c) d) :=
  (QuadraticTowerMultiplicationCoherence.lookup_congr (.eqRefl h) (.eqRefl B) (.eqRefl T)
    (lookup_associative h B D T a b c r hL hr hD ha hb hc) (.eqRefl d)).eqTrans
      (lookup_associative h B D T a (lookup h B T b c) d r hL hr hD ha hbc hd)

def firstProduct (h K T d a b c e : PTm n) : PTm n := added h (lookup h K T a c) (lookup h K T (lookup h K T b e) d)
def secondProduct (h K T a b c e : PTm n) : PTm n := added h (lookup h K T a e) (lookup h K T b c)
def pairProduct (h K T d a b c e : PTm n) : PTm n := Foundations.SequenceComposition.append
  (firstProduct h K T d a b c e) (secondProduct h K T a b c e)
ipra_subst firstProduct
ipra_subst secondProduct
ipra_subst pairProduct

theorem recipe_pair (h B T D A C : PTm n) : Γ ⊢[PRAAx] recipe h B T D A C ≐
    pairProduct h (budget h B D) T (entry D h) (leftHalf h A) (rightHalf h A) (leftHalf h C) (rightHalf h C) := .eqRefl _

theorem pair_product_proper (h K T d a a' b b' c c' e e' : PTm n)
    (ha : Γ ⊢[PRAAx] equalValues h a a') (hb : Γ ⊢[PRAAx] equalValues h b b')
    (hc : Γ ⊢[PRAAx] equalValues h c c') (he : Γ ⊢[PRAAx] equalValues h e e') : Γ ⊢[PRAAx]
    pairProduct h K T d a b c e ≐ pairProduct h K T d a' b' c' e' :=
  QuadraticTowerCoefficients.append_congr
    (QuadraticTowerCoefficientArithmetic.added_congr (.eqRefl h)
      (QuadraticTowerOperandProperness.lookup_proper _ _ _ _ _ _ _ ha hc)
      (QuadraticTowerMultiplicationCoherence.lookup_congr (.eqRefl h) (.eqRefl K) (.eqRefl T)
        (QuadraticTowerOperandProperness.lookup_proper _ _ _ _ _ _ _ hb he) (.eqRefl d)))
    (QuadraticTowerCoefficientArithmetic.added_congr (.eqRefl h)
      (QuadraticTowerOperandProperness.lookup_proper _ _ _ _ _ _ _ ha he)
      (QuadraticTowerOperandProperness.lookup_proper _ _ _ _ _ _ _ hb hc))

theorem added_cycle (h A C E F : PTm n) : Γ ⊢[PRAAx]
    added h (added h A F) (added h C E) ≐ added h (added h A C) (added h E F) :=
  (QuadraticTowerAdditionLaws.added_four h A F C E).eqTrans
    (QuadraticTowerCoefficientArithmetic.added_congr (.eqRefl h) (.eqRefl (added h A C))
      (QuadraticTowerMultiplicationCommutativity.added_commutative h F E))

/-- A real bounded lower-table calculation for the two original pair
components. Every intermediate height below is derived from that table. -/
theorem pair_product_associative (h B D T a b c e f g d s : PTm n)
    (hL : Γ ⊢[PRAAx] localLaw h (budget h B D) D T)
    (hComm : Γ ⊢[PRAAx] QuadraticTowerMultiplicationCommutativity.localLaw h (budget h B D) D T)
    (hDist : Γ ⊢[PRAAx] QuadraticTowerMultiplicationDistributivity.localLaw h (budget h B D) D T)
    (hHeight : Γ ⊢[PRAAx] QuadraticTowerMultiplicationHeight.localLaw h (budget h B D) D T)
    (hCap : Γ ⊢[PRAAx] le (productHeight (succ h) s) B) (hD : Γ ⊢[PRAAx] radicandsHeight D h s)
    (ha : Γ ⊢[PRAAx] arrayHeight h a s) (hb : Γ ⊢[PRAAx] arrayHeight h b s)
    (hc : Γ ⊢[PRAAx] arrayHeight h c s) (he : Γ ⊢[PRAAx] arrayHeight h e s)
    (hf : Γ ⊢[PRAAx] arrayHeight h f s) (hg : Γ ⊢[PRAAx] arrayHeight h g s)
    (hd : Γ ⊢[PRAAx] arrayHeight h d s) : Γ ⊢[PRAAx]
    pairProduct h (budget h B D) T d (firstProduct h (budget h B D) T d a b c e) (secondProduct h (budget h B D) T a b c e) f g ≐
      pairProduct h (budget h B D) T d a b (firstProduct h (budget h B D) T d c e f g) (secondProduct h (budget h B D) T c e f g) := by
  let K := budget h B D
  let p := QuadraticTowerGrowth.path h
  let v := growth p s
  let r := growth p v
  let u := growth p r
  let m (X Y : PTm n) := lookup h K T X Y
  have sv := QuadraticTowerGrowth.growth_inflation (Γ := Γ) p s
  have vr := QuadraticTowerGrowth.growth_inflation (Γ := Γ) p v
  have sr := le_trans sv vr
  have ru := QuadraticTowerGrowth.growth_inflation (Γ := Γ) p r
  have rAmp : Γ ⊢[PRAAx] le (amp r) B := le_congr (QuadraticTowerGrowth.twice_then_add h s).eqSymm (.eqRefl _) hCap
  have rB := le_trans (QuadraticTowerGrowth.amp_inflation r) rAmp
  have uK : Γ ⊢[PRAAx] le u K := le_trans (QuadraticTowerGrowth.growth_mono p r B rB)
    (QuadraticTowerGrowth.lower_path_budget h B D B (le_refl _))
  have uAmp : Γ ⊢[PRAAx] le (amp u) K := le_trans
    (QuadraticTowerGrowth.amp_mono (QuadraticTowerGrowth.growth_mono p r B rB))
      (QuadraticTowerMultiplicationDistributivity.lower_sum_budget h B D B (le_refl _))
  have rK := le_trans ru uK
  have vK := le_trans vr rK
  have sK := le_trans sv vK
  have rCap := le_trans (QuadraticTowerGrowth.amp_mono ru) uAmp
  have dr := QuadraticTowerMultiplicationHeight.radicands_mono D h s r hD sr
  have du := QuadraticTowerMultiplicationHeight.radicands_mono D h r u dr ru
  have ar := QuadraticTowerMultiplicationHeight.array_mono _ _ _ _ ha sr
  have br := QuadraticTowerMultiplicationHeight.array_mono _ _ _ _ hb sr
  have cr := QuadraticTowerMultiplicationHeight.array_mono _ _ _ _ hc sr
  have er := QuadraticTowerMultiplicationHeight.array_mono _ _ _ _ he sr
  have fr := QuadraticTowerMultiplicationHeight.array_mono _ _ _ _ hf sr
  have gr := QuadraticTowerMultiplicationHeight.array_mono _ _ _ _ hg sr
  have dd := QuadraticTowerMultiplicationHeight.array_mono _ _ _ _ hd sr
  have oldH (X Y : PTm n) (hx : Γ ⊢[PRAAx] arrayHeight h X s) (hy : Γ ⊢[PRAAx] arrayHeight h Y s) : Γ ⊢[PRAAx]
      arrayHeight h (m X Y) v := QuadraticTowerMultiplicationHeight.lookup_height h K D T X Y s hHeight sK hD hx hy
  have newH (X Y : PTm n) (hx : Γ ⊢[PRAAx] arrayHeight h X s) (hy : Γ ⊢[PRAAx] arrayHeight h Y s) : Γ ⊢[PRAAx]
      arrayHeight h (m X Y) r := QuadraticTowerMultiplicationHeight.array_mono _ _ _ _ (oldH X Y hx hy) vr
  have acH := newH a c ha hc
  have beH := newH b e hb he
  have aeH := newH a e ha he
  have bcH := newH b c hb hc
  have cfH := newH c f hc hf
  have egH := newH e g he hg
  have cgH := newH c g hc hg
  have efH := newH e f he hf
  have bedH : Γ ⊢[PRAAx] arrayHeight h (m (m b e) d) r :=
    QuadraticTowerMultiplicationHeight.lookup_height h K D T _ d v hHeight vK
      (QuadraticTowerMultiplicationHeight.radicands_mono _ _ _ _ hD sv) (oldH b e hb he)
      (QuadraticTowerMultiplicationHeight.array_mono _ _ _ _ hd sv)
  have egdH : Γ ⊢[PRAAx] arrayHeight h (m (m e g) d) r :=
    QuadraticTowerMultiplicationHeight.lookup_height h K D T _ d v hHeight vK
      (QuadraticTowerMultiplicationHeight.radicands_mono _ _ _ _ hD sv) (oldH e g he hg)
      (QuadraticTowerMultiplicationHeight.array_mono _ _ _ _ hd sv)
  have nextH (X Y : PTm n) (hx : Γ ⊢[PRAAx] arrayHeight h X r) (hy : Γ ⊢[PRAAx] arrayHeight h Y r) : Γ ⊢[PRAAx]
      arrayHeight h (m X Y) u := QuadraticTowerMultiplicationHeight.lookup_height h K D T X Y r hHeight rK dr hx hy
  have leftR (X Y Z : PTm n) (hx : Γ ⊢[PRAAx] arrayHeight h X r) (hy : Γ ⊢[PRAAx] arrayHeight h Y r)
      (hz : Γ ⊢[PRAAx] arrayHeight h Z r) : Γ ⊢[PRAAx] m (added h X Y) Z ≐ added h (m X Z) (m Y Z) :=
    QuadraticTowerMultiplicationDistributivity.lookup_left_distributive h K D T X Y Z r hDist hComm rCap dr hx hy hz
  have rightR (X Y Z : PTm n) (hx : Γ ⊢[PRAAx] arrayHeight h X r) (hy : Γ ⊢[PRAAx] arrayHeight h Y r)
      (hz : Γ ⊢[PRAAx] arrayHeight h Z r) : Γ ⊢[PRAAx] m X (added h Y Z) ≐ added h (m X Y) (m X Z) :=
    QuadraticTowerMultiplicationDistributivity.lookup_distributive h K D T X Y Z r hDist rCap dr hx hy hz
  have leftU (X Y Z : PTm n) (hx : Γ ⊢[PRAAx] arrayHeight h X u) (hy : Γ ⊢[PRAAx] arrayHeight h Y u)
      (hz : Γ ⊢[PRAAx] arrayHeight h Z u) : Γ ⊢[PRAAx] m (added h X Y) Z ≐ added h (m X Z) (m Y Z) :=
    QuadraticTowerMultiplicationDistributivity.lookup_left_distributive h K D T X Y Z u hDist hComm uAmp du hx hy hz
  have asR (X Y Z : PTm n) (hx : Γ ⊢[PRAAx] arrayHeight h X r) (hy : Γ ⊢[PRAAx] arrayHeight h Y r)
      (hz : Γ ⊢[PRAAx] arrayHeight h Z r) : Γ ⊢[PRAAx] m (m X Y) Z ≐ m X (m Y Z) :=
    lookup_associative h K D T X Y Z r hL uK dr hx hy hz
  have ddU := QuadraticTowerMultiplicationHeight.array_mono _ _ _ _ dd ru
  have leftFirst : Γ ⊢[PRAAx]
      firstProduct h K T d (firstProduct h K T d a b c e) (secondProduct h K T a b c e) f g ≐
        added h (added h (m (m a c) f) (m (m (m b e) d) f))
          (added h (m (m (m a e) g) d) (m (m (m b c) g) d)) :=
    QuadraticTowerCoefficientArithmetic.added_congr (.eqRefl h)
      (leftR _ _ f acH bedH fr)
      ((QuadraticTowerMultiplicationCoherence.lookup_congr (.eqRefl h) (.eqRefl K) (.eqRefl T)
        (leftR _ _ g aeH bcH gr) (.eqRefl d)).eqTrans
          (leftU _ _ d (nextH _ _ aeH gr) (nextH _ _ bcH gr) ddU))
  have rightFirst : Γ ⊢[PRAAx]
      firstProduct h K T d a b (firstProduct h K T d c e f g) (secondProduct h K T c e f g) ≐
        added h (added h (m a (m c f)) (m a (m (m e g) d)))
          (added h (m (m b (m c g)) d) (m (m b (m e f)) d)) :=
    QuadraticTowerCoefficientArithmetic.added_congr (.eqRefl h)
      (rightR a _ _ ar cfH egdH)
      ((QuadraticTowerMultiplicationCoherence.lookup_congr (.eqRefl h) (.eqRefl K) (.eqRefl T)
        (rightR b _ _ br cgH efH) (.eqRefl d)).eqTrans
          (leftU _ _ d (nextH _ _ br cgH) (nextH _ _ br efH) ddU))
  have firstMap := QuadraticTowerCoefficientArithmetic.added_congr (.eqRefl h)
    (QuadraticTowerCoefficientArithmetic.added_congr (.eqRefl h) (asR a c f ar cr fr)
      (quartic_move h K D T b e f d r hL hComm uK dr br er fr dd beH))
    (QuadraticTowerCoefficientArithmetic.added_congr (.eqRefl h)
      (quartic_right h K D T a e g d r hL uK dr ar er gr dd egH)
      (QuadraticTowerMultiplicationCoherence.lookup_congr (.eqRefl h) (.eqRefl K) (.eqRefl T)
        (asR b c g br cr gr) (.eqRefl d)))
  have firstEq : Γ ⊢[PRAAx]
      firstProduct h K T d (firstProduct h K T d a b c e) (secondProduct h K T a b c e) f g ≐
        firstProduct h K T d a b (firstProduct h K T d c e f g) (secondProduct h K T c e f g) :=
    leftFirst.eqTrans (firstMap.eqTrans ((added_cycle h _ _ _ _).eqTrans rightFirst.eqSymm))
  have leftSecond : Γ ⊢[PRAAx]
      secondProduct h K T (firstProduct h K T d a b c e) (secondProduct h K T a b c e) f g ≐
        added h (added h (m (m a c) g) (m (m (m b e) d) g)) (added h (m (m a e) f) (m (m b c) f)) :=
    QuadraticTowerCoefficientArithmetic.added_congr (.eqRefl h) (leftR _ _ g acH bedH gr) (leftR _ _ f aeH bcH fr)
  have rightSecond : Γ ⊢[PRAAx]
      secondProduct h K T a b (firstProduct h K T d c e f g) (secondProduct h K T c e f g) ≐
        added h (added h (m a (m c g)) (m a (m e f))) (added h (m b (m c f)) (m b (m (m e g) d))) :=
    QuadraticTowerCoefficientArithmetic.added_congr (.eqRefl h) (rightR a _ _ ar cgH efH) (rightR b _ _ br cfH egdH)
  have secondMap := QuadraticTowerCoefficientArithmetic.added_congr (.eqRefl h)
    (QuadraticTowerCoefficientArithmetic.added_congr (.eqRefl h) (asR a c g ar cr gr)
      ((quartic_move h K D T b e g d r hL hComm uK dr br er gr dd beH).eqTrans (asR b (m e g) d br egH dd)))
    (QuadraticTowerCoefficientArithmetic.added_congr (.eqRefl h) (asR a e f ar er fr) (asR b c f br cr fr))
  have secondEq : Γ ⊢[PRAAx]
      secondProduct h K T (firstProduct h K T d a b c e) (secondProduct h K T a b c e) f g ≐
        secondProduct h K T a b (firstProduct h K T d c e f g) (secondProduct h K T c e f g) :=
    leftSecond.eqTrans (secondMap.eqTrans ((added_cycle h _ _ _ _).eqTrans rightSecond.eqSymm))
  exact QuadraticTowerCoefficients.append_congr firstEq secondEq

theorem step_associative (h B D T A C E s : PTm n)
    (hL : Γ ⊢[PRAAx] localLaw h (budget h B D) D T)
    (hComm : Γ ⊢[PRAAx] QuadraticTowerMultiplicationCommutativity.localLaw h (budget h B D) D T)
    (hDist : Γ ⊢[PRAAx] QuadraticTowerMultiplicationDistributivity.localLaw h (budget h B D) D T)
    (hHeight : Γ ⊢[PRAAx] QuadraticTowerMultiplicationHeight.localLaw h (budget h B D) D T)
    (hCap : Γ ⊢[PRAAx] le (productHeight (succ h) s) B) (hD : Γ ⊢[PRAAx] radicandsHeight D (succ h) s)
    (ha : Γ ⊢[PRAAx] arrayHeight (succ h) A s) (hc : Γ ⊢[PRAAx] arrayHeight (succ h) C s)
    (he : Γ ⊢[PRAAx] arrayHeight (succ h) E s) : Γ ⊢[PRAAx]
    lookup (succ h) B (QuadraticTowerMultiplicationTable.step h B T D)
      (lookup (succ h) B (QuadraticTowerMultiplicationTable.step h B T D) A C) E ≐
    lookup (succ h) B (QuadraticTowerMultiplicationTable.step h B T D) A
      (lookup (succ h) B (QuadraticTowerMultiplicationTable.step h B T D) C E) := by
  let S := QuadraticTowerMultiplicationTable.step h B T D
  let K := budget h B D
  let P := lookup (succ h) B S A C
  let Q := lookup (succ h) B S C E
  let a := leftHalf h A
  let b := rightHalf h A
  let c := leftHalf h C
  let e := rightHalf h C
  let f := leftHalf h E
  let g := rightHalf h E
  let d := entry D h
  have sB := le_trans (QuadraticTowerGrowth.growth_inflation (QuadraticTowerGrowth.path (succ h)) s) hCap
  have aB := QuadraticTowerMultiplicationHeight.array_mono _ _ _ _ ha sB
  have cB := QuadraticTowerMultiplicationHeight.array_mono _ _ _ _ hc sB
  have eB := QuadraticTowerMultiplicationHeight.array_mono _ _ _ _ he sB
  have heightS := QuadraticTowerMultiplicationHeight.local_step h B D T hHeight
  have pH : Γ ⊢[PRAAx] arrayHeight (succ h) P (productHeight (succ h) s) :=
    QuadraticTowerMultiplicationHeight.lookup_height (succ h) B D S A C s heightS sB hD ha hc
  have qH : Γ ⊢[PRAAx] arrayHeight (succ h) Q (productHeight (succ h) s) :=
    QuadraticTowerMultiplicationHeight.lookup_height (succ h) B D S C E s heightS sB hD hc he
  have pB := QuadraticTowerMultiplicationHeight.array_mono _ _ _ _ pH hCap
  have qB := QuadraticTowerMultiplicationHeight.array_mono _ _ _ _ qH hCap
  have pLeft : Γ ⊢[PRAAx] equalValues h (leftHalf h P) (firstProduct h K T d a b c e) :=
    QuadraticTowerMultiplicationRecurrence.left_step_values h B T D A C aB cB
  have pRight : Γ ⊢[PRAAx] equalValues h (rightHalf h P) (secondProduct h K T a b c e) :=
    QuadraticTowerMultiplicationRecurrence.right_step_values h B T D A C aB cB
  have qLeft : Γ ⊢[PRAAx] equalValues h (leftHalf h Q) (firstProduct h K T d c e f g) :=
    QuadraticTowerMultiplicationRecurrence.left_step_values h B T D C E cB eB
  have qRight : Γ ⊢[PRAAx] equalValues h (rightHalf h Q) (secondProduct h K T c e f g) :=
    QuadraticTowerMultiplicationRecurrence.right_step_values h B T D C E cB eB
  have left := (QuadraticTowerMultiplicationRecurrence.step_lookup_original h B T D P E pB eB).eqTrans
    ((recipe_pair h B T D P E).eqTrans (pair_product_proper h K T d _ _ _ _ f f g g pLeft pRight
      (QuadraticTowerMultiplicationZero.values_refl h f) (QuadraticTowerMultiplicationZero.values_refl h g)))
  have right := (QuadraticTowerMultiplicationRecurrence.step_lookup_original h B T D A Q aB qB).eqTrans
    ((recipe_pair h B T D A Q).eqTrans (pair_product_proper h K T d a a b b _ _ _ _
      (QuadraticTowerMultiplicationZero.values_refl h a) (QuadraticTowerMultiplicationZero.values_refl h b) qLeft qRight))
  have middle := pair_product_associative h B D T a b c e f g d s hL hComm hDist hHeight hCap
    (QuadraticTowerMultiplicationHeight.radicands_prefix D h (succ h) s hD (le_succ_self h))
    (QuadraticTowerMultiplicationHeight.left_height h A s ha) (QuadraticTowerMultiplicationHeight.right_height h A s ha)
    (QuadraticTowerMultiplicationHeight.left_height h C s hc) (QuadraticTowerMultiplicationHeight.right_height h C s hc)
    (QuadraticTowerMultiplicationHeight.left_height h E s he) (QuadraticTowerMultiplicationHeight.right_height h E s he)
    (QuadraticTowerMultiplicationHeight.radicand_at D (succ h) s h hD (le_refl _))
  exact left.eqTrans (middle.eqTrans right.eqSymm)

theorem base_associative (B D A C E s : PTm n) (hCap : Γ ⊢[PRAAx] le (productHeight zero s) B)
    (hD : Γ ⊢[PRAAx] radicandsHeight D zero s) (ha : Γ ⊢[PRAAx] arrayHeight zero A s)
    (hc : Γ ⊢[PRAAx] arrayHeight zero C s) (he : Γ ⊢[PRAAx] arrayHeight zero E s) : Γ ⊢[PRAAx]
    lookup zero B (QuadraticTowerMultiplicationTable.base B) (lookup zero B (QuadraticTowerMultiplicationTable.base B) A C) E ≐
      lookup zero B (QuadraticTowerMultiplicationTable.base B) A (lookup zero B (QuadraticTowerMultiplicationTable.base B) C E) := by
  let T := QuadraticTowerMultiplicationTable.base B
  let P := lookup zero B T A C
  let Q := lookup zero B T C E
  have sB := le_trans (QuadraticTowerGrowth.growth_inflation (QuadraticTowerGrowth.path zero) s) hCap
  have aB := QuadraticTowerMultiplicationHeight.array_mono _ _ _ _ ha sB
  have cB := QuadraticTowerMultiplicationHeight.array_mono _ _ _ _ hc sB
  have eB := QuadraticTowerMultiplicationHeight.array_mono _ _ _ _ he sB
  have heightT := QuadraticTowerMultiplicationHeight.local_base (Γ := Γ) B D
  have pH : Γ ⊢[PRAAx] arrayHeight zero P (productHeight zero s) :=
    QuadraticTowerMultiplicationHeight.lookup_height zero B D T A C s heightT sB hD ha hc
  have qH : Γ ⊢[PRAAx] arrayHeight zero Q (productHeight zero s) :=
    QuadraticTowerMultiplicationHeight.lookup_height zero B D T C E s heightT sB hD hc he
  have pB := QuadraticTowerMultiplicationHeight.array_mono _ _ _ _ pH hCap
  have qB := QuadraticTowerMultiplicationHeight.array_mono _ _ _ _ qH hCap
  have pHead := (Foundations.SequenceComposition.entry_congr (Γ := Γ)
    (QuadraticTowerMultiplicationCoherence.base_lookup_original B A C aB cB) (.eqRefl zero)).eqTrans
      (QuadraticTowerCoefficients.singleton_entry _)
  have qHead := (Foundations.SequenceComposition.entry_congr (Γ := Γ)
    (QuadraticTowerMultiplicationCoherence.base_lookup_original B C E cB eB) (.eqRefl zero)).eqTrans
      (QuadraticTowerCoefficients.singleton_entry _)
  have left := (QuadraticTowerMultiplicationCoherence.base_lookup_original B P E pB eB).eqTrans
    (QuadraticTowerOperandProperness.singleton_congr (RationalAlgebra.multiply_congr pHead (.eqRefl (entry E zero))))
  have right := (QuadraticTowerMultiplicationCoherence.base_lookup_original B A Q aB qB).eqTrans
    (QuadraticTowerOperandProperness.singleton_congr (RationalAlgebra.multiply_congr (.eqRefl (entry A zero)) qHead))
  exact left.eqTrans ((QuadraticTowerOperandProperness.singleton_congr (RationalAlgebra.multiply_associative _ _ _)).eqTrans right.eqSymm)

theorem local_base (B D : PTm n) : Γ ⊢[PRAAx] localLaw zero B D (QuadraticTowerMultiplicationTable.base B) := by
  refine .allI (.impI ?_)
  refine .allI (.impI ?_)
  refine .allI (.impI ?_)
  refine .allI (.impI ?_)
  refine .impI (.impI (.impI (.impI (.impI ?_))))
  let B' := Syn.shift (Syn.shift (Syn.shift (Syn.shift B)))
  let D' := Syn.shift (Syn.shift (Syn.shift (Syn.shift D)))
  let b := (var 3 : PTm (n+4))
  let u := (var 2 : PTm (n+4))
  let v := (var 1 : PTm (n+4))
  let w := (var 0 : PTm (n+4))
  let Δ := arrayHeight zero (word zero b w) b :: arrayHeight zero (word zero b v) b :: arrayHeight zero (word zero b u) b ::
    radicandsHeight D' zero b :: le (productHeight zero b) B' :: lt w (horizon zero b) :: lt v (horizon zero b) ::
    lt u (horizon zero b) :: lt b (succ B') :: (((Γ.map Fm.shift).map Fm.shift).map Fm.shift).map Fm.shift
  have ha : Δ ⊢[PRAAx] arrayHeight zero (word zero b u) b := .hyp (by simp [Δ])
  have hc : Δ ⊢[PRAAx] arrayHeight zero (word zero b v) b := Prf.hyp1
  have he : Δ ⊢[PRAAx] arrayHeight zero (word zero b w) b := Prf.hyp0
  have hd : Δ ⊢[PRAAx] radicandsHeight D' zero b := .hyp (by simp [Δ])
  have hb : Δ ⊢[PRAAx] le (productHeight zero b) B' := .hyp (by simp [Δ])
  simpa [Δ,B',D',b,u,v,w,Fm.shift,Syn.shift] using
    base_associative B' D' (word zero b u) (word zero b v) (word zero b w) b hb hd ha hc he

theorem local_step (h B D T : PTm n)
    (hL : Γ ⊢[PRAAx] localLaw h (budget h B D) D T)
    (hComm : Γ ⊢[PRAAx] QuadraticTowerMultiplicationCommutativity.localLaw h (budget h B D) D T)
    (hDist : Γ ⊢[PRAAx] QuadraticTowerMultiplicationDistributivity.localLaw h (budget h B D) D T)
    (hHeight : Γ ⊢[PRAAx] QuadraticTowerMultiplicationHeight.localLaw h (budget h B D) D T) : Γ ⊢[PRAAx]
    localLaw (succ h) B D (QuadraticTowerMultiplicationTable.step h B T D) := by
  have ls : (((Γ.map Fm.shift).map Fm.shift).map Fm.shift).map Fm.shift ⊢[PRAAx]
      localLaw (Syn.shift (Syn.shift (Syn.shift (Syn.shift h))))
        (budget (Syn.shift (Syn.shift (Syn.shift (Syn.shift h)))) (Syn.shift (Syn.shift (Syn.shift (Syn.shift B)))) (Syn.shift (Syn.shift (Syn.shift (Syn.shift D)))))
        (Syn.shift (Syn.shift (Syn.shift (Syn.shift D)))) (Syn.shift (Syn.shift (Syn.shift (Syn.shift T)))) := by
    simpa only [Fm.shift,subst_localLaw,QuadraticTowerMultiplicationTable.subst_budget,Syn.shift] using hL.shift.shift.shift.shift
  have cs : (((Γ.map Fm.shift).map Fm.shift).map Fm.shift).map Fm.shift ⊢[PRAAx]
      QuadraticTowerMultiplicationCommutativity.localLaw (Syn.shift (Syn.shift (Syn.shift (Syn.shift h))))
        (budget (Syn.shift (Syn.shift (Syn.shift (Syn.shift h)))) (Syn.shift (Syn.shift (Syn.shift (Syn.shift B)))) (Syn.shift (Syn.shift (Syn.shift (Syn.shift D)))))
        (Syn.shift (Syn.shift (Syn.shift (Syn.shift D)))) (Syn.shift (Syn.shift (Syn.shift (Syn.shift T)))) := by
    simpa only [Fm.shift,QuadraticTowerMultiplicationCommutativity.subst_localLaw,QuadraticTowerMultiplicationTable.subst_budget,Syn.shift] using hComm.shift.shift.shift.shift
  have hs : (((Γ.map Fm.shift).map Fm.shift).map Fm.shift).map Fm.shift ⊢[PRAAx]
      QuadraticTowerMultiplicationHeight.localLaw (Syn.shift (Syn.shift (Syn.shift (Syn.shift h))))
        (budget (Syn.shift (Syn.shift (Syn.shift (Syn.shift h)))) (Syn.shift (Syn.shift (Syn.shift (Syn.shift B)))) (Syn.shift (Syn.shift (Syn.shift (Syn.shift D)))))
        (Syn.shift (Syn.shift (Syn.shift (Syn.shift D)))) (Syn.shift (Syn.shift (Syn.shift (Syn.shift T)))) := by
    simpa only [Fm.shift,QuadraticTowerMultiplicationHeight.subst_localLaw,QuadraticTowerMultiplicationTable.subst_budget,Syn.shift] using hHeight.shift.shift.shift.shift
  have ds : (((Γ.map Fm.shift).map Fm.shift).map Fm.shift).map Fm.shift ⊢[PRAAx]
      QuadraticTowerMultiplicationDistributivity.localLaw (Syn.shift (Syn.shift (Syn.shift (Syn.shift h))))
        (budget (Syn.shift (Syn.shift (Syn.shift (Syn.shift h)))) (Syn.shift (Syn.shift (Syn.shift (Syn.shift B)))) (Syn.shift (Syn.shift (Syn.shift (Syn.shift D)))))
        (Syn.shift (Syn.shift (Syn.shift (Syn.shift D)))) (Syn.shift (Syn.shift (Syn.shift (Syn.shift T)))) := by
    simpa only [Fm.shift,QuadraticTowerMultiplicationDistributivity.subst_localLaw,QuadraticTowerMultiplicationTable.subst_budget,Syn.shift] using hDist.shift.shift.shift.shift
  refine .allI (.impI ?_)
  refine .allI (.impI ?_)
  refine .allI (.impI ?_)
  refine .allI (.impI ?_)
  refine .impI (.impI (.impI (.impI (.impI ?_))))
  let h' := Syn.shift (Syn.shift (Syn.shift (Syn.shift h)))
  let B' := Syn.shift (Syn.shift (Syn.shift (Syn.shift B)))
  let D' := Syn.shift (Syn.shift (Syn.shift (Syn.shift D)))
  let T' := Syn.shift (Syn.shift (Syn.shift (Syn.shift T)))
  let b := (var 3 : PTm (n+4))
  let u := (var 2 : PTm (n+4))
  let v := (var 1 : PTm (n+4))
  let w := (var 0 : PTm (n+4))
  let Δ := arrayHeight (succ h') (word (succ h') b w) b :: arrayHeight (succ h') (word (succ h') b v) b ::
    arrayHeight (succ h') (word (succ h') b u) b :: radicandsHeight D' (succ h') b :: le (productHeight (succ h') b) B' ::
    lt w (horizon (succ h') b) :: lt v (horizon (succ h') b) :: lt u (horizon (succ h') b) :: lt b (succ B') ::
      (((Γ.map Fm.shift).map Fm.shift).map Fm.shift).map Fm.shift
  have ha : Δ ⊢[PRAAx] arrayHeight (succ h') (word (succ h') b u) b := .hyp (by simp [Δ])
  have hc : Δ ⊢[PRAAx] arrayHeight (succ h') (word (succ h') b v) b := Prf.hyp1
  have he : Δ ⊢[PRAAx] arrayHeight (succ h') (word (succ h') b w) b := Prf.hyp0
  have hd : Δ ⊢[PRAAx] radicandsHeight D' (succ h') b := .hyp (by simp [Δ])
  have hb : Δ ⊢[PRAAx] le (productHeight (succ h') b) B' := .hyp (by simp [Δ])
  have lower : Δ ⊢[PRAAx] localLaw h' (budget h' B' D') D' T' := ls.wk.wk.wk.wk.wk.wk.wk.wk.wk
  have comm : Δ ⊢[PRAAx] QuadraticTowerMultiplicationCommutativity.localLaw h' (budget h' B' D') D' T' := cs.wk.wk.wk.wk.wk.wk.wk.wk.wk
  have distribution : Δ ⊢[PRAAx] QuadraticTowerMultiplicationDistributivity.localLaw h' (budget h' B' D') D' T' := ds.wk.wk.wk.wk.wk.wk.wk.wk.wk
  have heights : Δ ⊢[PRAAx] QuadraticTowerMultiplicationHeight.localLaw h' (budget h' B' D') D' T' := hs.wk.wk.wk.wk.wk.wk.wk.wk.wk
  simpa [Δ,h',B',D',T',b,u,v,w,Fm.shift,Syn.shift] using
    step_associative h' B' D' T' (word (succ h') b u) (word (succ h') b v) (word (succ h') b w) b lower comm distribution heights hb hd ha hc he

theorem local_congr {h h' B B' D D' T T' : PTm n} (hh : Γ ⊢[PRAAx] h ≐ h')
    (hb : Γ ⊢[PRAAx] B ≐ B') (hd : Γ ⊢[PRAAx] D ≐ D') (ht : Γ ⊢[PRAAx] T ≐ T')
    (hL : Γ ⊢[PRAAx] localLaw h B D T) : Γ ⊢[PRAAx] localLaw h' B' D' T' := by
  have p := Prf.eqSubst (localLaw (var 0) (var 1) (var 2) (var 3) : Fm PTm 4)
    ![h,B,D,T] ![h',B',D',T'] (fun i => by fin_cases i; exact hh; exact hb; exact hd; exact ht) (by simpa using hL)
  simpa using p

def forwardLaw (H B D t : PTm n) : Fm PTm n := le t H ⟶ localLaw t (cap H B t D) D (state H B t D)
def forwardSyntax (H B D t : PTm n) : BFm n := .imp (.le t H)
  (localSyntax t (cap H B t D) D (state H B t D))
ipra_subst forwardLaw
theorem forward_formula (H B D t : PTm n) : formula (forwardSyntax H B D t) = forwardLaw H B D t := by
  simp [forwardSyntax,forwardLaw,formula,local_formula,BFm.le,le]

theorem forward_zero (H B D : PTm n) : Γ ⊢[PRAAx] forwardLaw H B D zero :=
  .impI (local_congr (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (QuadraticTowerMultiplicationHeight.state_zero H B D).wk.eqSymm (local_base _ D))

theorem forward_step (H B D t : PTm n) (ih : Γ ⊢[PRAAx] forwardLaw H B D t) : Γ ⊢[PRAAx]
    forwardLaw H B D (succ t) := by
  refine QuadraticTowerMultiplicationHeight.forward_step_of_local localLaw H B D t local_congr ih ?_
  intro Δ ht adjusted
  have tle : Δ ⊢[PRAAx] le t H := le_trans (le_succ_self t) ht
  have link := QuadraticTowerMultiplicationHeight.cap_link H B t D ht
  have commGate : Δ ⊢[PRAAx] QuadraticTowerMultiplicationCommutativity.forwardLaw H B D t := by
    simpa only [QuadraticTowerMultiplicationCommutativity.forward_formula,QuadraticTowerMultiplicationCommutativity.subst_forwardLaw,
      Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
        (QuadraticTowerMultiplicationCommutativity.forward_all (Γ := Δ) H B D).allE t
  have commPrevious : Δ ⊢[PRAAx] QuadraticTowerMultiplicationCommutativity.localLaw t (cap H B t D) D (state H B t D) := .impE commGate tle
  have commAdjusted := QuadraticTowerMultiplicationCommutativity.local_congr (.eqRefl _) link (.eqRefl _) (.eqRefl _) commPrevious
  have heightGate : Δ ⊢[PRAAx] QuadraticTowerMultiplicationHeight.forwardLaw H B D t := by
    simpa only [QuadraticTowerMultiplicationHeight.forward_formula,QuadraticTowerMultiplicationHeight.subst_forwardLaw,
      Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
        (QuadraticTowerMultiplicationHeight.forward_all (Γ := Δ) H B D).allE t
  have heightPrevious : Δ ⊢[PRAAx] QuadraticTowerMultiplicationHeight.localLaw t (cap H B t D) D (state H B t D) := .impE heightGate tle
  have heightAdjusted := QuadraticTowerMultiplicationHeight.local_congr (.eqRefl _) link (.eqRefl _) (.eqRefl _) heightPrevious
  have distGate : Δ ⊢[PRAAx] QuadraticTowerMultiplicationDistributivity.forwardLaw H B D t := by
    simpa only [QuadraticTowerMultiplicationDistributivity.forward_formula,QuadraticTowerMultiplicationDistributivity.subst_forwardLaw,
      Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
        (QuadraticTowerMultiplicationDistributivity.forward_all (Γ := Δ) H B D).allE t
  have distPrevious : Δ ⊢[PRAAx] QuadraticTowerMultiplicationDistributivity.localLaw t (cap H B t D) D (state H B t D) := .impE distGate tle
  have distAdjusted := QuadraticTowerMultiplicationDistributivity.local_congr (.eqRefl _) link (.eqRefl _) (.eqRefl _) distPrevious
  exact local_step t (cap H B (succ t) D) D (state H B t D) adjusted commAdjusted distAdjusted heightAdjusted

/-- The full bounded triple-word predicate, not a host-degree induction. -/
theorem forward_all (H B D : PTm n) : Γ ⊢[PRAAx] .all
    (formula (forwardSyntax (Syn.shift H) (Syn.shift B) (Syn.shift D) (var 0))) := by
  refine Foundations.BoundedSyntaxInduction.induction _ ?_ ?_
  · simpa only [forward_formula,subst_forwardLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      forward_zero (Γ := Γ) H B D
  · simpa only [forward_formula,subst_forwardLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift] using
      forward_step (Γ := formula (forwardSyntax (Syn.shift H) (Syn.shift B) (Syn.shift D) (var 0)) :: Γ.map Fm.shift)
        (Syn.shift H) (Syn.shift B) (Syn.shift D) (var 0)
        (by simpa only [forward_formula] using (Prf.hyp0 (Ax := PRAAx)))

theorem table_associativity (h B D : PTm n) : Γ ⊢[PRAAx] localLaw h B D (QuadraticTowerMultiplicationTable.table h B D) := by
  have gate : Γ ⊢[PRAAx] forwardLaw h B D h := by
    simpa only [forward_formula,subst_forwardLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      (forward_all (Γ := Γ) h B D).allE h
  exact local_congr (.eqRefl _)
    (Foundations.BackwardDemand.horizon_final QuadraticTowerMultiplicationTable.demandF h B D)
    (.eqRefl _) (.eqRefl _) (Prf.impE gate (le_refl h))

theorem query_associative (h B D A C E b : PTm n) (hb : Γ ⊢[PRAAx] le (productHeight h b) B)
    (hD : Γ ⊢[PRAAx] radicandsHeight D h b) (ha : Γ ⊢[PRAAx] arrayHeight h A b)
    (hc : Γ ⊢[PRAAx] arrayHeight h C b) (he : Γ ⊢[PRAAx] arrayHeight h E b) : Γ ⊢[PRAAx]
    QuadraticTowerMultiplicationTable.query h B D (QuadraticTowerMultiplicationTable.query h B D A C) E ≐
      QuadraticTowerMultiplicationTable.query h B D A (QuadraticTowerMultiplicationTable.query h B D C E) :=
  lookup_associative h B D _ A C E b (table_associativity h B D) hb hD ha hc he

theorem original_program_associative (h B D A C E b : PTm n) (hb : Γ ⊢[PRAAx] le (productHeight h b) B)
    (hD : Γ ⊢[PRAAx] radicandsHeight D h b) (ha : Γ ⊢[PRAAx] arrayHeight h A b)
    (hc : Γ ⊢[PRAAx] arrayHeight h C b) (he : Γ ⊢[PRAAx] arrayHeight h E b) : Γ ⊢[PRAAx]
    PTm.app QuadraticTowerMultiplicationTable.queryF ![h,B,D,PTm.app QuadraticTowerMultiplicationTable.queryF ![h,B,D,A,C],E] ≐
      PTm.app QuadraticTowerMultiplicationTable.queryF ![h,B,D,A,PTm.app QuadraticTowerMultiplicationTable.queryF ![h,B,D,C,E]] := by
  have left := (QuadraticTowerMultiplicationTable.query_program_at (Γ := Γ) h B D
    (PTm.app QuadraticTowerMultiplicationTable.queryF ![h,B,D,A,C]) E).eqTrans
      (QuadraticTowerOperandProperness.query_operands_proper h B D _ _ E E
        (values_of_equal h _ _ (QuadraticTowerMultiplicationTable.query_program_at _ _ _ _ _))
        (QuadraticTowerMultiplicationZero.values_refl h E))
  have right := (QuadraticTowerMultiplicationTable.query_program_at (Γ := Γ) h B D A
    (PTm.app QuadraticTowerMultiplicationTable.queryF ![h,B,D,C,E])).eqTrans
      (QuadraticTowerOperandProperness.query_operands_proper h B D A A _ _
        (QuadraticTowerMultiplicationZero.values_refl h A)
        (values_of_equal h _ _ (QuadraticTowerMultiplicationTable.query_program_at _ _ _ _ _)))
  exact left.eqTrans ((query_associative h B D A C E b hb hD ha hc he).eqTrans right.eqSymm)

def output (h b D A C E : PTm n) : PTm n := pairT
  (QuadraticTowerMultiplicationTable.query h (productHeight h b) D (QuadraticTowerMultiplicationTable.query h (productHeight h b) D A C) E)
    (pairT (QuadraticTowerMultiplicationTable.query h (productHeight h b) D A (QuadraticTowerMultiplicationTable.query h (productHeight h b) D C E))
      (productHeight h b))
def outputF : PR 6 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
def run (h b D A C E : PTm n) : PTm n := PTm.app outputF ![h,b,D,A,C,E]
ipra_subst output
ipra_subst run

theorem program_at (h b D A C E : PTm n) : Γ ⊢[PRAAx] run h b D A C E ≐ output h b D A C E := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6) ![h,b,D,A,C,E]
theorem returned_left (h b D A C E : PTm n) : Γ ⊢[PRAAx] fstT (run h b D A C E) ≐
    QuadraticTowerMultiplicationTable.query h (productHeight h b) D (QuadraticTowerMultiplicationTable.query h (productHeight h b) D A C) E :=
  (program_at _ _ _ _ _ _).fstE
theorem returned_tail (h b D A C E : PTm n) : Γ ⊢[PRAAx] sndT (run h b D A C E) ≐
    pairT (QuadraticTowerMultiplicationTable.query h (productHeight h b) D A (QuadraticTowerMultiplicationTable.query h (productHeight h b) D C E)) (productHeight h b) :=
  (program_at _ _ _ _ _ _).sndE
theorem returned_right (h b D A C E : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run h b D A C E)) ≐
    QuadraticTowerMultiplicationTable.query h (productHeight h b) D A (QuadraticTowerMultiplicationTable.query h (productHeight h b) D C E) :=
  (returned_tail _ _ _ _ _ _).fstE
theorem returned_cap (h b D A C E : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run h b D A C E)) ≐ productHeight h b :=
  (returned_tail _ _ _ _ _ _).sndE
theorem returned_associative (h b D A C E : PTm n)
    (hD : Γ ⊢[PRAAx] radicandsHeight D h b) (ha : Γ ⊢[PRAAx] arrayHeight h A b)
    (hc : Γ ⊢[PRAAx] arrayHeight h C b) (he : Γ ⊢[PRAAx] arrayHeight h E b) : Γ ⊢[PRAAx]
    fstT (run h b D A C E) ≐ fstT (sndT (run h b D A C E)) :=
  (returned_left _ _ _ _ _ _).eqTrans
    ((query_associative h (productHeight h b) D A C E b (le_refl _) hD ha hc he).eqTrans (returned_right _ _ _ _ _ _).eqSymm)

theorem actual_associativity_table_predicate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (localLaw (var 0) (var 1) (var 2) (QuadraticTowerMultiplicationTable.table (var 0) (var 1) (var 2))) := closeUniv 3 (table_associativity _ _ _)
theorem actual_finite_forward_associativity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (forwardLaw (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (by simpa only [forward_formula,subst_forwardLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
    (forward_all (Γ := ([] : List (Fm PTm 4))) (var 0) (var 1) (var 2)).allE (var 3))
theorem original_heights_cap_actual_associativity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (le (productHeight (var 0) (var 6)) (var 1) ⟶ radicandsHeight (var 2) (var 0) (var 6) ⟶ arrayHeight (var 0) (var 3) (var 6) ⟶
      arrayHeight (var 0) (var 4) (var 6) ⟶ arrayHeight (var 0) (var 5) (var 6) ⟶
        QuadraticTowerMultiplicationTable.query (var 0) (var 1) (var 2) (QuadraticTowerMultiplicationTable.query (var 0) (var 1) (var 2) (var 3) (var 4)) (var 5) ≐
          QuadraticTowerMultiplicationTable.query (var 0) (var 1) (var 2) (var 3) (QuadraticTowerMultiplicationTable.query (var 0) (var 1) (var 2) (var 4) (var 5))) :=
  closeUniv 7 (.impI (.impI (.impI (.impI (.impI (query_associative _ _ _ _ _ _ (var 6)
    (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) Prf.hyp1 Prf.hyp0))))))
theorem original_heights_cap_nested_query_program_associativity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (le (productHeight (var 0) (var 6)) (var 1) ⟶ radicandsHeight (var 2) (var 0) (var 6) ⟶ arrayHeight (var 0) (var 3) (var 6) ⟶
      arrayHeight (var 0) (var 4) (var 6) ⟶ arrayHeight (var 0) (var 5) (var 6) ⟶
        PTm.app QuadraticTowerMultiplicationTable.queryF ![var 0,var 1,var 2,PTm.app QuadraticTowerMultiplicationTable.queryF ![var 0,var 1,var 2,var 3,var 4],var 5] ≐
          PTm.app QuadraticTowerMultiplicationTable.queryF ![var 0,var 1,var 2,var 3,PTm.app QuadraticTowerMultiplicationTable.queryF ![var 0,var 1,var 2,var 4,var 5]]) :=
  closeUniv 7 (.impI (.impI (.impI (.impI (.impI (original_program_associative _ _ _ _ _ _ (var 6)
    (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) Prf.hyp1 Prf.hyp0))))))
theorem actual_associative_pair_recipe_binding_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (recipe (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ≐ pairProduct (var 0) (budget (var 0) (var 1) (var 3)) (var 2) (entry (var 3) (var 0))
      (leftHalf (var 0) (var 4)) (rightHalf (var 0) (var 4)) (leftHalf (var 0) (var 5)) (rightHalf (var 0) (var 5))) := closeUniv 6 (recipe_pair _ _ _ _ _ _)
theorem actual_computed_cap_associativity_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ≐ output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) := closeUniv 6 (program_at _ _ _ _ _ _)
theorem original_heights_computed_cap_returned_associativity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (radicandsHeight (var 2) (var 0) (var 1) ⟶ arrayHeight (var 0) (var 3) (var 1) ⟶ arrayHeight (var 0) (var 4) (var 1) ⟶ arrayHeight (var 0) (var 5) (var 1) ⟶
      fstT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) ≐ fstT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)))) :=
  closeUniv 6 (.impI (.impI (.impI (.impI (returned_associative _ _ _ _ _ _
    (.hyp (by simp)) (.hyp (by simp)) Prf.hyp1 Prf.hyp0)))))

end LeanProofs.IPRA.Algebra.QuadraticTowerMultiplicationAssociativity
