import IPRADerivations.Algebra.QuadraticTowerAdditionLaws

/-!
# Actual tower multiplication distributes over constructed addition

The sufficient cap amp(b)<=B explicitly covers the original sum input.
The SAME five-call table, forward state and budget are used. Actual lower
be outputs have the proved original height before their sum enters the
third query. All finite predicates are compiled before QF induction.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Algebra.QuadraticTowerMultiplicationDistributivity

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

theorem lower_sum_budget (h B D b : PTm n) (hb : Γ ⊢[PRAAx] le b B) : Γ ⊢[PRAAx]
    le (amp (growth (QuadraticTowerGrowth.path h) b)) (budget h B D) := by
  have step : Γ ⊢[PRAAx] le (succ (QuadraticTowerGrowth.path h)) (QuadraticTowerGrowth.path (succ h)) :=
    le_congr (.eqRefl _) (QuadraticTowerGrowth.path_succ h).eqSymm
      (le_of_eq_add (d := QuadraticTowerGrowth.path h) (by ipra_ring))
  exact le_trans (le_congr (QuadraticTowerScalarBudget.growth_succ _ _) (.eqRefl _)
    (QuadraticTowerGrowth.growth_counter_mono _ _ b step))
      (QuadraticTowerGrowth.path_growth_budget h B D b hb)

def rowLaw (h B D T b u v w : PTm n) : Fm PTm n := le (amp b) B ⟶ radicandsHeight D h b ⟶
  arrayHeight h (word h b u) b ⟶ arrayHeight h (word h b v) b ⟶ arrayHeight h (word h b w) b ⟶
    lookup h B T (word h b u) (added h (word h b v) (word h b w)) ≐
      added h (lookup h B T (word h b u) (word h b v)) (lookup h B T (word h b u) (word h b w))
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

def rowSyntax (h B D T b u v w : PTm n) : BFm n := .imp (.le (amp b) B)
  (.imp (QuadraticTowerMultiplicationHeight.radicandsSyntax D h b)
    (.imp (QuadraticTowerMultiplicationHeight.heightSyntax h (word h b u) b)
      (.imp (QuadraticTowerMultiplicationHeight.heightSyntax h (word h b v) b)
        (.imp (QuadraticTowerMultiplicationHeight.heightSyntax h (word h b w) b)
          (.eq (lookup h B T (word h b u) (added h (word h b v) (word h b w)))
            (added h (lookup h B T (word h b u) (word h b v)) (lookup h B T (word h b u) (word h b w))))))))
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
    (hb : Γ ⊢[PRAAx] le (amp b) B) (hu : Γ ⊢[PRAAx] lt u (horizon h b))
    (hv : Γ ⊢[PRAAx] lt v (horizon h b)) (hw : Γ ⊢[PRAAx] lt w (horizon h b))
    (hD : Γ ⊢[PRAAx] radicandsHeight D h b) (ha : Γ ⊢[PRAAx] arrayHeight h (word h b u) b)
    (hc : Γ ⊢[PRAAx] arrayHeight h (word h b v) b) (he : Γ ⊢[PRAAx] arrayHeight h (word h b w) b) : Γ ⊢[PRAAx]
    lookup h B T (word h b u) (added h (word h b v) (word h b w)) ≐
      added h (lookup h B T (word h b u) (word h b v)) (lookup h B T (word h b u) (word h b w)) := by
  have bound := le_trans (QuadraticTowerGrowth.amp_inflation b) hb
  have bg : Γ ⊢[PRAAx] lt b (succ B) ⟶ atHeight h B D T b := by simpa [localLaw] using hL.allE b
  have ug : Γ ⊢[PRAAx] lt u (horizon h b) ⟶ atWord h B D T b u := by
    simpa [atHeight] using (Prf.impE bg ((succ_monus_succ _ _).eqTrans bound)).allE u
  have vg : Γ ⊢[PRAAx] lt v (horizon h b) ⟶ atSecond h B D T b u v := by
    simpa [atWord] using (Prf.impE ug hu).allE v
  have wg : Γ ⊢[PRAAx] lt w (horizon h b) ⟶ rowLaw h B D T b u v w := by
    simpa [atSecond] using (Prf.impE vg hv).allE w
  exact .impE (.impE (.impE (.impE (.impE (.impE wg hw) hb) hD) ha) hc) he

theorem lookup_distributive (h B D T A C E b : PTm n) (hL : Γ ⊢[PRAAx] localLaw h B D T)
    (hb : Γ ⊢[PRAAx] le (amp b) B) (hD : Γ ⊢[PRAAx] radicandsHeight D h b)
    (ha : Γ ⊢[PRAAx] arrayHeight h A b) (hc : Γ ⊢[PRAAx] arrayHeight h C b)
    (he : Γ ⊢[PRAAx] arrayHeight h E b) : Γ ⊢[PRAAx]
    lookup h B T A (added h C E) ≐ added h (lookup h B T A C) (lookup h B T A E) := by
  have middle := local_at h B D T b (code h A b) (code h C b) (code h E b) hL hb
    (QuadraticTowerArrayCodec.code_bound h A b ha) (QuadraticTowerArrayCodec.code_bound h C b hc)
    (QuadraticTowerArrayCodec.code_bound h E b he) hD
    (QuadraticTowerMultiplicationHeight.restored_height h A b b ha (le_refl _))
    (QuadraticTowerMultiplicationHeight.restored_height h C b b hc (le_refl _))
    (QuadraticTowerMultiplicationHeight.restored_height h E b b he (le_refl _))
  have av := QuadraticTowerMultiplicationCoherence.restored_values h A b ha
  have cv := QuadraticTowerMultiplicationCoherence.restored_values h C b hc
  have ev := QuadraticTowerMultiplicationCoherence.restored_values h E b he
  exact (QuadraticTowerOperandProperness.lookup_proper h B T _ A _ (added h C E) av
    (QuadraticTowerCoefficientArithmetic.added_proper _ _ _ _ _ cv ev)).eqSymm.eqTrans
      (middle.eqTrans (QuadraticTowerCoefficientArithmetic.added_congr (.eqRefl _)
        (QuadraticTowerOperandProperness.lookup_proper _ _ _ _ _ _ _ av cv)
        (QuadraticTowerOperandProperness.lookup_proper _ _ _ _ _ _ _ av ev)))

theorem lookup_left_distributive (h B D T A C E b : PTm n) (hL : Γ ⊢[PRAAx] localLaw h B D T)
    (hComm : Γ ⊢[PRAAx] QuadraticTowerMultiplicationCommutativity.localLaw h B D T)
    (hb : Γ ⊢[PRAAx] le (amp b) B) (hD : Γ ⊢[PRAAx] radicandsHeight D h b)
    (ha : Γ ⊢[PRAAx] arrayHeight h A b) (hc : Γ ⊢[PRAAx] arrayHeight h C b)
    (he : Γ ⊢[PRAAx] arrayHeight h E b) : Γ ⊢[PRAAx]
    lookup h B T (added h A C) E ≐ added h (lookup h B T A E) (lookup h B T C E) := by
  have bg := QuadraticTowerGrowth.amp_inflation (Γ := Γ) b
  have bB := le_trans bg hb
  have move := QuadraticTowerMultiplicationCommutativity.lookup_commutative h B D T (added h A C) E (amp b) hComm hb
    (QuadraticTowerMultiplicationHeight.radicands_mono _ _ _ _ hD bg)
    (QuadraticTowerMultiplicationHeight.added_height h A C b ha hc)
    (QuadraticTowerMultiplicationHeight.array_mono _ _ _ _ he bg)
  exact move.eqTrans ((lookup_distributive h B D T E A C b hL hb hD he ha hc).eqTrans
    (QuadraticTowerCoefficientArithmetic.added_congr (.eqRefl _)
      (QuadraticTowerMultiplicationCommutativity.lookup_commutative _ _ _ _ _ _ b hComm bB hD he ha)
      (QuadraticTowerMultiplicationCommutativity.lookup_commutative _ _ _ _ _ _ b hComm bB hD he hc)))

theorem recipe_distributive (h B D T A C E b : PTm n)
    (hL : Γ ⊢[PRAAx] localLaw h (budget h B D) D T)
    (hComm : Γ ⊢[PRAAx] QuadraticTowerMultiplicationCommutativity.localLaw h (budget h B D) D T)
    (hHeight : Γ ⊢[PRAAx] QuadraticTowerMultiplicationHeight.localLaw h (budget h B D) D T)
    (hb : Γ ⊢[PRAAx] le (amp b) B) (hD : Γ ⊢[PRAAx] radicandsHeight D (succ h) b)
    (ha : Γ ⊢[PRAAx] arrayHeight (succ h) A b) (hc : Γ ⊢[PRAAx] arrayHeight (succ h) C b)
    (he : Γ ⊢[PRAAx] arrayHeight (succ h) E b) : Γ ⊢[PRAAx]
    recipe h B T D A (added (succ h) C E) ≐ added (succ h) (recipe h B T D A C) (recipe h B T D A E) := by
  let K := budget h B D
  let g := growth (QuadraticTowerGrowth.path h) b
  have bg := QuadraticTowerGrowth.growth_inflation (Γ := Γ) (QuadraticTowerGrowth.path h) b
  have bB := le_trans (QuadraticTowerGrowth.amp_inflation b) hb
  have gCap : Γ ⊢[PRAAx] le (amp g) K := lower_sum_budget h B D b bB
  have bCap : Γ ⊢[PRAAx] le (amp b) K := le_trans (QuadraticTowerGrowth.amp_mono bg) gCap
  have bK := le_trans (QuadraticTowerGrowth.amp_inflation b) bCap
  have rh := QuadraticTowerMultiplicationHeight.radicands_prefix D h (succ h) b hD (le_succ_self h)
  have a0 := QuadraticTowerMultiplicationHeight.left_height h A b ha
  have a1 := QuadraticTowerMultiplicationHeight.right_height h A b ha
  have c0 := QuadraticTowerMultiplicationHeight.left_height h C b hc
  have c1 := QuadraticTowerMultiplicationHeight.right_height h C b hc
  have e0 := QuadraticTowerMultiplicationHeight.left_height h E b he
  have e1 := QuadraticTowerMultiplicationHeight.right_height h E b he
  let beC := lookup h K T (rightHalf h A) (rightHalf h C)
  let beE := lookup h K T (rightHalf h A) (rightHalf h E)
  have beCH : Γ ⊢[PRAAx] arrayHeight h beC g :=
    QuadraticTowerMultiplicationHeight.lookup_height h K D T _ _ b hHeight bK rh a1 c1
  have beEH : Γ ⊢[PRAAx] arrayHeight h beE g :=
    QuadraticTowerMultiplicationHeight.lookup_height h K D T _ _ b hHeight bK rh a1 e1
  have dH : Γ ⊢[PRAAx] arrayHeight h (entry D h) g :=
    QuadraticTowerMultiplicationHeight.array_mono _ _ _ _
      (QuadraticTowerMultiplicationHeight.radicand_at D (succ h) b h hD (le_refl _)) bg
  have lowSum := QuadraticTowerAdditionLaws.left_added (Γ := Γ) h C E
  have highSum := QuadraticTowerAdditionLaws.right_added (Γ := Γ) h C E
  have ac := (QuadraticTowerMultiplicationCoherence.lookup_congr (.eqRefl h) (.eqRefl K) (.eqRefl T)
    (.eqRefl (leftHalf h A)) lowSum).eqTrans
      (lookup_distributive h K D T _ _ _ b hL bCap rh a0 c0 e0)
  have be := (QuadraticTowerMultiplicationCoherence.lookup_congr (.eqRefl h) (.eqRefl K) (.eqRefl T)
    (.eqRefl (rightHalf h A)) highSum).eqTrans
      (lookup_distributive h K D T _ _ _ b hL bCap rh a1 c1 e1)
  have ae := (QuadraticTowerMultiplicationCoherence.lookup_congr (.eqRefl h) (.eqRefl K) (.eqRefl T)
    (.eqRefl (leftHalf h A)) highSum).eqTrans
      (lookup_distributive h K D T _ _ _ b hL bCap rh a0 c1 e1)
  have bc := (QuadraticTowerMultiplicationCoherence.lookup_congr (.eqRefl h) (.eqRefl K) (.eqRefl T)
    (.eqRefl (rightHalf h A)) lowSum).eqTrans
      (lookup_distributive h K D T _ _ _ b hL bCap rh a1 c0 e0)
  have bed := (QuadraticTowerMultiplicationCoherence.lookup_congr (.eqRefl h) (.eqRefl K) (.eqRefl T)
    be (.eqRefl (entry D h))).eqTrans
      (lookup_left_distributive h K D T beC beE (entry D h) g hL hComm gCap
        (QuadraticTowerMultiplicationHeight.radicands_mono _ _ _ _ rh bg) beCH beEH dH)
  have low := (QuadraticTowerCoefficientArithmetic.added_congr (.eqRefl h) ac bed).eqTrans
    (QuadraticTowerAdditionLaws.added_four h _ _ _ _)
  have high := (QuadraticTowerCoefficientArithmetic.added_congr (.eqRefl h) ae bc).eqTrans
    (QuadraticTowerAdditionLaws.added_four h _ _ _ _)
  have joined := QuadraticTowerAdditionLaws.added_join (Γ := Γ) h
    (added h (lookup h K T (leftHalf h A) (leftHalf h C)) (lookup h K T beC (entry D h)))
    (added h (lookup h K T (leftHalf h A) (rightHalf h C)) (lookup h K T (rightHalf h A) (leftHalf h C)))
    (added h (lookup h K T (leftHalf h A) (leftHalf h E)) (lookup h K T beE (entry D h)))
    (added h (lookup h K T (leftHalf h A) (rightHalf h E)) (lookup h K T (rightHalf h A) (leftHalf h E)))
    (QuadraticTowerCoefficientArithmetic.added_length _ _ _) (QuadraticTowerCoefficientArithmetic.added_length _ _ _)
    (QuadraticTowerCoefficientArithmetic.added_length _ _ _) (QuadraticTowerCoefficientArithmetic.added_length _ _ _)
  exact (QuadraticTowerCoefficients.append_congr low high).eqTrans joined.eqSymm

theorem step_distributive (h B D T A C E b : PTm n)
    (hL : Γ ⊢[PRAAx] localLaw h (budget h B D) D T)
    (hComm : Γ ⊢[PRAAx] QuadraticTowerMultiplicationCommutativity.localLaw h (budget h B D) D T)
    (hHeight : Γ ⊢[PRAAx] QuadraticTowerMultiplicationHeight.localLaw h (budget h B D) D T)
    (hb : Γ ⊢[PRAAx] le (amp b) B) (hD : Γ ⊢[PRAAx] radicandsHeight D (succ h) b)
    (ha : Γ ⊢[PRAAx] arrayHeight (succ h) A b) (hc : Γ ⊢[PRAAx] arrayHeight (succ h) C b)
    (he : Γ ⊢[PRAAx] arrayHeight (succ h) E b) : Γ ⊢[PRAAx]
    lookup (succ h) B (QuadraticTowerMultiplicationTable.step h B T D) A (added (succ h) C E) ≐
      added (succ h) (lookup (succ h) B (QuadraticTowerMultiplicationTable.step h B T D) A C)
        (lookup (succ h) B (QuadraticTowerMultiplicationTable.step h B T D) A E) := by
  have bB := le_trans (QuadraticTowerGrowth.amp_inflation b) hb
  have aB := QuadraticTowerMultiplicationHeight.array_mono _ _ _ _ ha bB
  have cB := QuadraticTowerMultiplicationHeight.array_mono _ _ _ _ hc bB
  have eB := QuadraticTowerMultiplicationHeight.array_mono _ _ _ _ he bB
  have sumB := QuadraticTowerMultiplicationHeight.array_mono _ _ _ _
    (QuadraticTowerMultiplicationHeight.added_height (succ h) C E b hc he) hb
  have first := QuadraticTowerMultiplicationCoherence.step_lookup_normalized h B T D A (added (succ h) C E) aB sumB
  have sumReset : Γ ⊢[PRAAx] normalized (succ h) (added (succ h) C E) ≐
      added (succ h) (normalized (succ h) C) (normalized (succ h) E) :=
    (QuadraticTowerArrayNormalization.normalized_added _ _ _).eqTrans (QuadraticTowerAdditionLaws.added_normalized _ _ _).eqSymm
  have reset := QuadraticTowerMultiplicationTable.recipe_congr (Γ := Γ) (.eqRefl h) (.eqRefl B) (.eqRefl T) (.eqRefl D)
    (.eqRefl (normalized (succ h) A)) sumReset
  have middle := recipe_distributive h B D T _ _ _ b hL hComm hHeight hb hD
    (QuadraticTowerMultiplicationZero.normalized_height _ _ _ ha)
    (QuadraticTowerMultiplicationZero.normalized_height _ _ _ hc)
    (QuadraticTowerMultiplicationZero.normalized_height _ _ _ he)
  exact first.eqTrans (reset.eqTrans (middle.eqTrans
    (QuadraticTowerCoefficientArithmetic.added_congr (.eqRefl _)
      (QuadraticTowerMultiplicationCoherence.step_lookup_normalized h B T D A C aB cB).eqSymm
      (QuadraticTowerMultiplicationCoherence.step_lookup_normalized h B T D A E aB eB).eqSymm)))

theorem base_distributive (B A C E b : PTm n) (hb : Γ ⊢[PRAAx] le (amp b) B)
    (ha : Γ ⊢[PRAAx] arrayHeight zero A b) (hc : Γ ⊢[PRAAx] arrayHeight zero C b)
    (he : Γ ⊢[PRAAx] arrayHeight zero E b) : Γ ⊢[PRAAx]
    lookup zero B (QuadraticTowerMultiplicationTable.base B) A (added zero C E) ≐
      added zero (lookup zero B (QuadraticTowerMultiplicationTable.base B) A C)
        (lookup zero B (QuadraticTowerMultiplicationTable.base B) A E) := by
  have bB := le_trans (QuadraticTowerGrowth.amp_inflation b) hb
  have aB := QuadraticTowerMultiplicationHeight.array_mono _ _ _ _ ha bB
  have cB := QuadraticTowerMultiplicationHeight.array_mono _ _ _ _ hc bB
  have eB := QuadraticTowerMultiplicationHeight.array_mono _ _ _ _ he bB
  have sumB := QuadraticTowerMultiplicationHeight.array_mono _ _ _ _
    (QuadraticTowerMultiplicationHeight.added_height zero C E b hc he) hb
  have first := QuadraticTowerMultiplicationCoherence.base_lookup_original B A (added zero C E) aB sumB
  have scalar := (RationalAlgebra.multiply_congr (Γ := Γ) (.eqRefl (entry A zero))
    (QuadraticTowerCoefficientArithmetic.added_lookup zero C E zero QuadraticTowerCoefficientArithmetic.base_index)).eqTrans
      (RationalAlgebra.multiply_add _ _ _)
  have right := (QuadraticTowerCoefficientArithmetic.added_congr (.eqRefl zero)
    (QuadraticTowerMultiplicationCoherence.base_lookup_original B A C aB cB)
    (QuadraticTowerMultiplicationCoherence.base_lookup_original B A E aB eB)).eqTrans
      (QuadraticTowerAdditionLaws.added_singletons _ _)
  exact first.eqTrans ((QuadraticTowerMultiplicationZero.sequence_congr (var 1) (.eqRefl one) scalar).eqTrans right.eqSymm)

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
    radicandsHeight D' zero b :: le (amp b) B' :: lt w (horizon zero b) :: lt v (horizon zero b) ::
    lt u (horizon zero b) :: lt b (succ B') :: (((Γ.map Fm.shift).map Fm.shift).map Fm.shift).map Fm.shift
  have ha : Δ ⊢[PRAAx] arrayHeight zero (word zero b u) b := .hyp (by simp [Δ])
  have hc : Δ ⊢[PRAAx] arrayHeight zero (word zero b v) b := Prf.hyp1
  have he : Δ ⊢[PRAAx] arrayHeight zero (word zero b w) b := Prf.hyp0
  have hb : Δ ⊢[PRAAx] le (amp b) B' := .hyp (by simp [Δ])
  simpa [Δ,B',D',b,u,v,w,Fm.shift,Syn.shift] using
    base_distributive B' (word zero b u) (word zero b v) (word zero b w) b hb ha hc he

theorem local_step (h B D T : PTm n)
    (hL : Γ ⊢[PRAAx] localLaw h (budget h B D) D T)
    (hComm : Γ ⊢[PRAAx] QuadraticTowerMultiplicationCommutativity.localLaw h (budget h B D) D T)
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
    arrayHeight (succ h') (word (succ h') b u) b :: radicandsHeight D' (succ h') b :: le (amp b) B' ::
    lt w (horizon (succ h') b) :: lt v (horizon (succ h') b) :: lt u (horizon (succ h') b) :: lt b (succ B') ::
      (((Γ.map Fm.shift).map Fm.shift).map Fm.shift).map Fm.shift
  have ha : Δ ⊢[PRAAx] arrayHeight (succ h') (word (succ h') b u) b := .hyp (by simp [Δ])
  have hc : Δ ⊢[PRAAx] arrayHeight (succ h') (word (succ h') b v) b := Prf.hyp1
  have he : Δ ⊢[PRAAx] arrayHeight (succ h') (word (succ h') b w) b := Prf.hyp0
  have hd : Δ ⊢[PRAAx] radicandsHeight D' (succ h') b := .hyp (by simp [Δ])
  have hb : Δ ⊢[PRAAx] le (amp b) B' := .hyp (by simp [Δ])
  have lower : Δ ⊢[PRAAx] localLaw h' (budget h' B' D') D' T' := ls.wk.wk.wk.wk.wk.wk.wk.wk.wk
  have comm : Δ ⊢[PRAAx] QuadraticTowerMultiplicationCommutativity.localLaw h' (budget h' B' D') D' T' := cs.wk.wk.wk.wk.wk.wk.wk.wk.wk
  have heights : Δ ⊢[PRAAx] QuadraticTowerMultiplicationHeight.localLaw h' (budget h' B' D') D' T' := hs.wk.wk.wk.wk.wk.wk.wk.wk.wk
  simpa [Δ,h',B',D',T',b,u,v,w,Fm.shift,Syn.shift] using
    step_distributive h' B' D' T' (word (succ h') b u) (word (succ h') b v) (word (succ h') b w) b lower comm heights hb hd ha hc he

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
  exact local_step t (cap H B (succ t) D) D (state H B t D) adjusted commAdjusted heightAdjusted

/-- The full bounded triple-word predicate, not a host-degree induction. -/
theorem forward_all (H B D : PTm n) : Γ ⊢[PRAAx] .all
    (formula (forwardSyntax (Syn.shift H) (Syn.shift B) (Syn.shift D) (var 0))) := by
  refine Foundations.BoundedSyntaxInduction.induction_of_formula _ (forward_formula _ _ _ _) ?_ ?_
  · simpa only [subst_forwardLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      forward_zero (Γ := Γ) H B D
  · simpa only [subst_forwardLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift] using
      forward_step (Syn.shift H) (Syn.shift B) (Syn.shift D) (var 0) (Prf.hyp0 (Γ := Γ.map Fm.shift))

theorem table_distributivity (h B D : PTm n) : Γ ⊢[PRAAx] localLaw h B D (QuadraticTowerMultiplicationTable.table h B D) := by
  have gate : Γ ⊢[PRAAx] forwardLaw h B D h := by
    simpa only [forward_formula,subst_forwardLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      (forward_all (Γ := Γ) h B D).allE h
  exact local_congr (.eqRefl _)
    (Foundations.BackwardDemand.horizon_final QuadraticTowerMultiplicationTable.demandF h B D)
    (.eqRefl _) (.eqRefl _) (Prf.impE gate (le_refl h))

theorem query_right_distributive (h B D A C E b : PTm n) (hb : Γ ⊢[PRAAx] le (amp b) B)
    (hD : Γ ⊢[PRAAx] radicandsHeight D h b) (ha : Γ ⊢[PRAAx] arrayHeight h A b)
    (hc : Γ ⊢[PRAAx] arrayHeight h C b) (he : Γ ⊢[PRAAx] arrayHeight h E b) : Γ ⊢[PRAAx]
    QuadraticTowerMultiplicationTable.query h B D A (added h C E) ≐
      added h (QuadraticTowerMultiplicationTable.query h B D A C) (QuadraticTowerMultiplicationTable.query h B D A E) :=
  lookup_distributive h B D _ A C E b (table_distributivity h B D) hb hD ha hc he

theorem query_left_distributive (h B D A C E b : PTm n) (hb : Γ ⊢[PRAAx] le (amp b) B)
    (hD : Γ ⊢[PRAAx] radicandsHeight D h b) (ha : Γ ⊢[PRAAx] arrayHeight h A b)
    (hc : Γ ⊢[PRAAx] arrayHeight h C b) (he : Γ ⊢[PRAAx] arrayHeight h E b) : Γ ⊢[PRAAx]
    QuadraticTowerMultiplicationTable.query h B D (added h A C) E ≐
      added h (QuadraticTowerMultiplicationTable.query h B D A E) (QuadraticTowerMultiplicationTable.query h B D C E) :=
  lookup_left_distributive h B D _ A C E b (table_distributivity h B D)
    (QuadraticTowerMultiplicationCommutativity.table_commutativity h B D) hb hD ha hc he

def output (h b D A C E : PTm n) : PTm n := pairT
  (QuadraticTowerMultiplicationTable.query h (amp b) D A (added h C E))
    (pairT (added h (QuadraticTowerMultiplicationTable.query h (amp b) D A C)
      (QuadraticTowerMultiplicationTable.query h (amp b) D A E)) (amp b))
def outputF : PR 6 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
def run (h b D A C E : PTm n) : PTm n := PTm.app outputF ![h,b,D,A,C,E]
ipra_subst output
ipra_subst run

theorem program_at (h b D A C E : PTm n) : Γ ⊢[PRAAx] run h b D A C E ≐ output h b D A C E := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6) ![h,b,D,A,C,E]
theorem returned_product (h b D A C E : PTm n) : Γ ⊢[PRAAx] fstT (run h b D A C E) ≐
    QuadraticTowerMultiplicationTable.query h (amp b) D A (added h C E) :=
  (program_at _ _ _ _ _ _).fstE
theorem returned_tail (h b D A C E : PTm n) : Γ ⊢[PRAAx] sndT (run h b D A C E) ≐
    pairT (added h (QuadraticTowerMultiplicationTable.query h (amp b) D A C) (QuadraticTowerMultiplicationTable.query h (amp b) D A E)) (amp b) :=
  (program_at _ _ _ _ _ _).sndE
theorem returned_sum (h b D A C E : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run h b D A C E)) ≐
    added h (QuadraticTowerMultiplicationTable.query h (amp b) D A C) (QuadraticTowerMultiplicationTable.query h (amp b) D A E) :=
  (returned_tail _ _ _ _ _ _).fstE
theorem returned_cap (h b D A C E : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run h b D A C E)) ≐ amp b :=
  (returned_tail _ _ _ _ _ _).sndE
theorem returned_distributive (h b D A C E : PTm n)
    (hD : Γ ⊢[PRAAx] radicandsHeight D h b) (ha : Γ ⊢[PRAAx] arrayHeight h A b)
    (hc : Γ ⊢[PRAAx] arrayHeight h C b) (he : Γ ⊢[PRAAx] arrayHeight h E b) : Γ ⊢[PRAAx]
    fstT (run h b D A C E) ≐ fstT (sndT (run h b D A C E)) :=
  (returned_product _ _ _ _ _ _).eqTrans
    ((query_right_distributive h (amp b) D A C E b (le_refl _) hD ha hc he).eqTrans (returned_sum _ _ _ _ _ _).eqSymm)

theorem actual_lower_computed_sum_budget_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le (var 3) (var 1) ⟶ le (amp (growth (QuadraticTowerGrowth.path (var 0)) (var 3))) (budget (var 0) (var 1) (var 2))) :=
  closeUniv 4 (.impI (lower_sum_budget _ _ _ _ Prf.hyp0))
theorem actual_distributivity_table_predicate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (localLaw (var 0) (var 1) (var 2) (QuadraticTowerMultiplicationTable.table (var 0) (var 1) (var 2))) := closeUniv 3 (table_distributivity _ _ _)
theorem actual_finite_forward_distributivity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (forwardLaw (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (by simpa only [forward_formula,subst_forwardLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
    (forward_all (Γ := ([] : List (Fm PTm 4))) (var 0) (var 1) (var 2)).allE (var 3))
theorem original_heights_cap_right_distributivity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (le (amp (var 6)) (var 1) ⟶ radicandsHeight (var 2) (var 0) (var 6) ⟶ arrayHeight (var 0) (var 3) (var 6) ⟶
      arrayHeight (var 0) (var 4) (var 6) ⟶ arrayHeight (var 0) (var 5) (var 6) ⟶
        QuadraticTowerMultiplicationTable.query (var 0) (var 1) (var 2) (var 3) (added (var 0) (var 4) (var 5)) ≐
          added (var 0) (QuadraticTowerMultiplicationTable.query (var 0) (var 1) (var 2) (var 3) (var 4))
            (QuadraticTowerMultiplicationTable.query (var 0) (var 1) (var 2) (var 3) (var 5))) :=
  closeUniv 7 (.impI (.impI (.impI (.impI (.impI (query_right_distributive _ _ _ _ _ _ (var 6)
    (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) Prf.hyp1 Prf.hyp0))))))
theorem original_heights_cap_left_distributivity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (le (amp (var 6)) (var 1) ⟶ radicandsHeight (var 2) (var 0) (var 6) ⟶ arrayHeight (var 0) (var 3) (var 6) ⟶
      arrayHeight (var 0) (var 4) (var 6) ⟶ arrayHeight (var 0) (var 5) (var 6) ⟶
        QuadraticTowerMultiplicationTable.query (var 0) (var 1) (var 2) (added (var 0) (var 3) (var 4)) (var 5) ≐
          added (var 0) (QuadraticTowerMultiplicationTable.query (var 0) (var 1) (var 2) (var 3) (var 5))
            (QuadraticTowerMultiplicationTable.query (var 0) (var 1) (var 2) (var 4) (var 5))) :=
  closeUniv 7 (.impI (.impI (.impI (.impI (.impI (query_left_distributive _ _ _ _ _ _ (var 6)
    (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) Prf.hyp1 Prf.hyp0))))))
theorem actual_computed_cap_distributivity_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ≐ output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) := closeUniv 6 (program_at _ _ _ _ _ _)
theorem original_heights_computed_cap_returned_distributivity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (radicandsHeight (var 2) (var 0) (var 1) ⟶ arrayHeight (var 0) (var 3) (var 1) ⟶ arrayHeight (var 0) (var 4) (var 1) ⟶ arrayHeight (var 0) (var 5) (var 1) ⟶
      fstT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) ≐ fstT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)))) :=
  closeUniv 6 (.impI (.impI (.impI (.impI (returned_distributive _ _ _ _ _ _
    (.hyp (by simp)) (.hyp (by simp)) Prf.hyp1 Prf.hyp0)))))

end LeanProofs.IPRA.Algebra.QuadraticTowerMultiplicationDistributivity
