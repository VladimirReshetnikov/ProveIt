import IPRADerivations.Algebra.QuadraticTowerMultiplicationZero

/-!
# Commutativity of the actual numerical-depth multiplication table

Original operand/radicand height guards suffice. A genuine bounded
word-pair predicate is proved along the SAME multiplication forward state.
The actual lower be products commute, so their third queries have literally
identical arguments. No ring/output law or extra cap floor is assumed.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Algebra.QuadraticTowerMultiplicationCommutativity

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis
open QuadraticTowerCoefficients (width)
open QuadraticTowerArrayCodec (arrayHeight horizon code)
open QuadraticTowerCoefficientArithmetic (added)
open QuadraticTowerMultiplicationTable (lookup budget recipe)
open QuadraticTowerMultiplicationHeight (radicandsHeight word cap state)
open LeanProofs.IPRA.Foundations.BoundedSyntax (BFm formula)
open LeanProofs.IPRA.Foundations.SequenceEquality (sequence_equal)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem added_commutative (h A C : PTm n) : Γ ⊢[PRAAx] added h A C ≐ added h C A := by
  apply sequence_equal QuadraticTowerCoefficientArithmetic.addBody QuadraticTowerCoefficientArithmetic.addBody
    (width h) (pairT A C) (pairT C A)
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (width (Syn.shift h)) :: Γ.map Fm.shift
  have value : Δ ⊢[PRAAx] inst2 QuadraticTowerCoefficientArithmetic.addBody (var 0) (pairT (Syn.shift A) (Syn.shift C)) ≐
      inst2 QuadraticTowerCoefficientArithmetic.addBody (var 0) (pairT (Syn.shift C) (Syn.shift A)) :=
    (QuadraticTowerCoefficientArithmetic.add_body_at _ _ _).eqTrans
      ((RationalAlgebra.add_commutative _ _).eqTrans (QuadraticTowerCoefficientArithmetic.add_body_at _ _ _).eqSymm)
  simpa only [Δ,Syn.shift,subst_pairT,QuadraticTowerCoefficients.subst_width] using value

def rowLaw (h B D T b u v : PTm n) : Fm PTm n := radicandsHeight D h b ⟶
  arrayHeight h (word h b u) b ⟶ arrayHeight h (word h b v) b ⟶
    lookup h B T (word h b u) (word h b v) ≐ lookup h B T (word h b v) (word h b u)
def atWord (h B D T b u : PTm n) : Fm PTm n := .all
  (lt (var 0) (Syn.shift (horizon h b)) ⟶ rowLaw (Syn.shift h) (Syn.shift B)
    (Syn.shift D) (Syn.shift T) (Syn.shift b) (Syn.shift u) (var 0))
def atHeight (h B D T b : PTm n) : Fm PTm n := .all
  (lt (var 0) (Syn.shift (horizon h b)) ⟶ atWord (Syn.shift h) (Syn.shift B)
    (Syn.shift D) (Syn.shift T) (Syn.shift b) (var 0))
def localLaw (h B D T : PTm n) : Fm PTm n := .all
  (lt (var 0) (succ (Syn.shift B)) ⟶ atHeight (Syn.shift h) (Syn.shift B)
    (Syn.shift D) (Syn.shift T) (var 0))
@[simp] theorem subst_rowLaw {k : ℕ} (σ : Fin n → PTm k) (h B D T b u v : PTm n) :
    (rowLaw h B D T b u v).subst σ = rowLaw (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ D)
      (Syn.subst σ T) (Syn.subst σ b) (Syn.subst σ u) (Syn.subst σ v) := by simp [rowLaw]
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
@[simp] theorem subst_localLaw {k : ℕ} (σ : Fin n → PTm k) (h B D T : PTm n) :
    (localLaw h B D T).subst σ = localLaw (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ D) (Syn.subst σ T) := by
  simp [localLaw,Syn.subst_shift,Syn.shift_subst]

def rowSyntax (h B D T b u v : PTm n) : BFm n :=
  .imp (QuadraticTowerMultiplicationHeight.radicandsSyntax D h b)
    (.imp (QuadraticTowerMultiplicationHeight.heightSyntax h (word h b u) b)
      (.imp (QuadraticTowerMultiplicationHeight.heightSyntax h (word h b v) b)
        (.eq (lookup h B T (word h b u) (word h b v)) (lookup h B T (word h b v) (word h b u)))))
def wordSyntax (h B D T b u : PTm n) : BFm n := .all (horizon h b)
  (rowSyntax (Syn.shift h) (Syn.shift B) (Syn.shift D) (Syn.shift T) (Syn.shift b) (Syn.shift u) (var 0))
def heightRowsSyntax (h B D T b : PTm n) : BFm n := .all (horizon h b)
  (wordSyntax (Syn.shift h) (Syn.shift B) (Syn.shift D) (Syn.shift T) (Syn.shift b) (var 0))
def localSyntax (h B D T : PTm n) : BFm n := .all (succ B)
  (heightRowsSyntax (Syn.shift h) (Syn.shift B) (Syn.shift D) (Syn.shift T) (var 0))
theorem row_formula (h B D T b u v : PTm n) : formula (rowSyntax h B D T b u v) = rowLaw h B D T b u v := by
  simp [rowSyntax,rowLaw,formula,QuadraticTowerMultiplicationHeight.radicands_formula,
    QuadraticTowerMultiplicationHeight.height_formula]
theorem word_formula (h B D T b u : PTm n) : formula (wordSyntax h B D T b u) = atWord h B D T b u := by
  simp [wordSyntax,atWord,formula,row_formula]
theorem height_rows_formula (h B D T b : PTm n) : formula (heightRowsSyntax h B D T b) = atHeight h B D T b := by
  simp [heightRowsSyntax,atHeight,formula,word_formula]
theorem local_formula (h B D T : PTm n) : formula (localSyntax h B D T) = localLaw h B D T := by
  simp [localSyntax,localLaw,formula,height_rows_formula,Syn.shift]

theorem local_at (h B D T b u v : PTm n) (hL : Γ ⊢[PRAAx] localLaw h B D T)
    (hb : Γ ⊢[PRAAx] le b B) (hu : Γ ⊢[PRAAx] lt u (horizon h b)) (hv : Γ ⊢[PRAAx] lt v (horizon h b))
    (hD : Γ ⊢[PRAAx] radicandsHeight D h b) (ha : Γ ⊢[PRAAx] arrayHeight h (word h b u) b)
    (hc : Γ ⊢[PRAAx] arrayHeight h (word h b v) b) : Γ ⊢[PRAAx]
    lookup h B T (word h b u) (word h b v) ≐ lookup h B T (word h b v) (word h b u) := by
  have bg : Γ ⊢[PRAAx] lt b (succ B) ⟶ atHeight h B D T b := by simpa [localLaw] using hL.allE b
  have ug : Γ ⊢[PRAAx] lt u (horizon h b) ⟶ atWord h B D T b u := by
    simpa [atHeight] using (Prf.impE bg ((succ_monus_succ _ _).eqTrans hb)).allE u
  have vg : Γ ⊢[PRAAx] lt v (horizon h b) ⟶ rowLaw h B D T b u v := by
    simpa [atWord] using (Prf.impE ug hu).allE v
  exact .impE (.impE (.impE (.impE vg hv) hD) ha) hc

theorem lookup_commutative (h B D T A C b : PTm n) (hL : Γ ⊢[PRAAx] localLaw h B D T)
    (hb : Γ ⊢[PRAAx] le b B) (hD : Γ ⊢[PRAAx] radicandsHeight D h b)
    (ha : Γ ⊢[PRAAx] arrayHeight h A b) (hc : Γ ⊢[PRAAx] arrayHeight h C b) : Γ ⊢[PRAAx]
    lookup h B T A C ≐ lookup h B T C A := by
  have middle := local_at h B D T b (code h A b) (code h C b) hL hb
    (QuadraticTowerArrayCodec.code_bound h A b ha) (QuadraticTowerArrayCodec.code_bound h C b hc) hD
    (QuadraticTowerMultiplicationHeight.restored_height h A b b ha (le_refl _))
    (QuadraticTowerMultiplicationHeight.restored_height h C b b hc (le_refl _))
  have av := QuadraticTowerMultiplicationCoherence.restored_values h A b ha
  have cv := QuadraticTowerMultiplicationCoherence.restored_values h C b hc
  exact (QuadraticTowerOperandProperness.lookup_proper h B T _ A _ C av cv).eqSymm.eqTrans
    (middle.eqTrans (QuadraticTowerOperandProperness.lookup_proper h B T _ C _ A cv av))

theorem recipe_commutative (h B D T A C b : PTm n) (hL : Γ ⊢[PRAAx] localLaw h (budget h B D) D T)
    (hb : Γ ⊢[PRAAx] le b B) (hD : Γ ⊢[PRAAx] radicandsHeight D (succ h) b)
    (ha : Γ ⊢[PRAAx] arrayHeight (succ h) A b) (hc : Γ ⊢[PRAAx] arrayHeight (succ h) C b) : Γ ⊢[PRAAx]
    recipe h B T D A C ≐ recipe h B T D C A := by
  let K := budget h B D
  have bK := le_trans (QuadraticTowerGrowth.growth_inflation (QuadraticTowerGrowth.path h) b)
    (QuadraticTowerGrowth.lower_path_budget h B D b hb)
  have rh := QuadraticTowerMultiplicationHeight.radicands_prefix D h (succ h) b hD (le_succ_self h)
  have a0 := QuadraticTowerMultiplicationHeight.left_height h A b ha
  have a1 := QuadraticTowerMultiplicationHeight.right_height h A b ha
  have c0 := QuadraticTowerMultiplicationHeight.left_height h C b hc
  have c1 := QuadraticTowerMultiplicationHeight.right_height h C b hc
  have ac := lookup_commutative h K D T _ _ b hL bK rh a0 c0
  have be := lookup_commutative h K D T _ _ b hL bK rh a1 c1
  have ae := lookup_commutative h K D T _ _ b hL bK rh a0 c1
  have bc := lookup_commutative h K D T _ _ b hL bK rh a1 c0
  have bed := QuadraticTowerMultiplicationCoherence.lookup_congr (.eqRefl h) (.eqRefl K) (.eqRefl T) be (.eqRefl (entry D h))
  have cross := (QuadraticTowerCoefficientArithmetic.added_congr (.eqRefl h) ae bc).eqTrans
    (added_commutative h _ _)
  exact QuadraticTowerCoefficients.append_congr
    (QuadraticTowerCoefficientArithmetic.added_congr (.eqRefl _) ac bed) cross

theorem step_commutative (h B D T A C b : PTm n) (hL : Γ ⊢[PRAAx] localLaw h (budget h B D) D T)
    (hb : Γ ⊢[PRAAx] le b B) (hD : Γ ⊢[PRAAx] radicandsHeight D (succ h) b)
    (ha : Γ ⊢[PRAAx] arrayHeight (succ h) A b) (hc : Γ ⊢[PRAAx] arrayHeight (succ h) C b) : Γ ⊢[PRAAx]
    lookup (succ h) B (QuadraticTowerMultiplicationTable.step h B T D) A C ≐
      lookup (succ h) B (QuadraticTowerMultiplicationTable.step h B T D) C A :=
  (QuadraticTowerMultiplicationCoherence.step_lookup_normalized h B T D A C
    (QuadraticTowerMultiplicationHeight.array_mono _ _ _ _ ha hb) (QuadraticTowerMultiplicationHeight.array_mono _ _ _ _ hc hb)).eqTrans
      ((recipe_commutative h B D T _ _ b hL hb hD
        (QuadraticTowerMultiplicationZero.normalized_height _ _ _ ha)
        (QuadraticTowerMultiplicationZero.normalized_height _ _ _ hc)).eqTrans
          (QuadraticTowerMultiplicationCoherence.step_lookup_normalized h B T D C A
            (QuadraticTowerMultiplicationHeight.array_mono _ _ _ _ hc hb)
            (QuadraticTowerMultiplicationHeight.array_mono _ _ _ _ ha hb)).eqSymm)

theorem base_commutative (B A C b : PTm n) (hb : Γ ⊢[PRAAx] le b B)
    (ha : Γ ⊢[PRAAx] arrayHeight zero A b) (hc : Γ ⊢[PRAAx] arrayHeight zero C b) : Γ ⊢[PRAAx]
    lookup zero B (QuadraticTowerMultiplicationTable.base B) A C ≐
      lookup zero B (QuadraticTowerMultiplicationTable.base B) C A := by
  have ab := QuadraticTowerMultiplicationHeight.array_mono zero A b B ha hb
  have cb := QuadraticTowerMultiplicationHeight.array_mono zero C b B hc hb
  exact (QuadraticTowerMultiplicationCoherence.base_lookup_original B A C ab cb).eqTrans
    ((QuadraticTowerMultiplicationZero.sequence_congr (var 1) (.eqRefl one) (RationalAlgebra.multiply_commutative _ _)).eqTrans
      (QuadraticTowerMultiplicationCoherence.base_lookup_original B C A cb ab).eqSymm)

theorem local_base (B D : PTm n) : Γ ⊢[PRAAx] localLaw zero B D (QuadraticTowerMultiplicationTable.base B) := by
  refine .allI (.impI (.allI (.impI (.allI (.impI (.impI (.impI (.impI ?_))))))))
  let B' := Syn.shift (Syn.shift (Syn.shift B))
  let D' := Syn.shift (Syn.shift (Syn.shift D))
  let b := (var 2 : PTm (n+3))
  let u := (var 1 : PTm (n+3))
  let v := (var 0 : PTm (n+3))
  let Δ := arrayHeight zero (word zero b v) b :: arrayHeight zero (word zero b u) b :: radicandsHeight D' zero b ::
    lt v (horizon zero b) :: lt u (horizon zero b) :: lt b (succ B') :: ((Γ.map Fm.shift).map Fm.shift).map Fm.shift
  have ha : Δ ⊢[PRAAx] arrayHeight zero (word zero b u) b := Prf.hyp1
  have hc : Δ ⊢[PRAAx] arrayHeight zero (word zero b v) b := Prf.hyp0
  have hr : Δ ⊢[PRAAx] lt b (succ B') := .hyp (by simp [Δ])
  have hb : Δ ⊢[PRAAx] le b B' := (succ_monus_succ _ _).eqSymm.eqTrans hr
  simpa [Δ,B',D',b,u,v,Fm.shift,Syn.shift] using base_commutative B' (word zero b u) (word zero b v) b hb ha hc

theorem local_step (h B D T : PTm n) (hL : Γ ⊢[PRAAx] localLaw h (budget h B D) D T) : Γ ⊢[PRAAx]
    localLaw (succ h) B D (QuadraticTowerMultiplicationTable.step h B T D) := by
  have ls : ((Γ.map Fm.shift).map Fm.shift).map Fm.shift ⊢[PRAAx]
      localLaw (Syn.shift (Syn.shift (Syn.shift h)))
        (budget (Syn.shift (Syn.shift (Syn.shift h))) (Syn.shift (Syn.shift (Syn.shift B))) (Syn.shift (Syn.shift (Syn.shift D))))
        (Syn.shift (Syn.shift (Syn.shift D))) (Syn.shift (Syn.shift (Syn.shift T))) := by
    simpa only [Fm.shift,subst_localLaw,QuadraticTowerMultiplicationTable.subst_budget,Syn.shift] using hL.shift.shift.shift
  refine .allI (.impI (.allI (.impI (.allI (.impI (.impI (.impI (.impI ?_))))))))
  let h' := Syn.shift (Syn.shift (Syn.shift h))
  let B' := Syn.shift (Syn.shift (Syn.shift B))
  let D' := Syn.shift (Syn.shift (Syn.shift D))
  let T' := Syn.shift (Syn.shift (Syn.shift T))
  let b := (var 2 : PTm (n+3))
  let u := (var 1 : PTm (n+3))
  let v := (var 0 : PTm (n+3))
  let Δ := arrayHeight (succ h') (word (succ h') b v) b :: arrayHeight (succ h') (word (succ h') b u) b ::
    radicandsHeight D' (succ h') b :: lt v (horizon (succ h') b) :: lt u (horizon (succ h') b) :: lt b (succ B') ::
      ((Γ.map Fm.shift).map Fm.shift).map Fm.shift
  have ha : Δ ⊢[PRAAx] arrayHeight (succ h') (word (succ h') b u) b := Prf.hyp1
  have hc : Δ ⊢[PRAAx] arrayHeight (succ h') (word (succ h') b v) b := Prf.hyp0
  have hd : Δ ⊢[PRAAx] radicandsHeight D' (succ h') b := .hyp (by simp [Δ])
  have hr : Δ ⊢[PRAAx] lt b (succ B') := .hyp (by simp [Δ])
  have hb : Δ ⊢[PRAAx] le b B' := (succ_monus_succ _ _).eqSymm.eqTrans hr
  have lower : Δ ⊢[PRAAx] localLaw h' (budget h' B' D') D' T' := ls.wk.wk.wk.wk.wk.wk
  simpa [Δ,h',B',D',T',b,u,v,Fm.shift,Syn.shift] using
    step_commutative h' B' D' T' (word (succ h') b u) (word (succ h') b v) b lower hb hd ha hc

theorem local_congr {h h' B B' D D' T T' : PTm n} (hh : Γ ⊢[PRAAx] h ≐ h')
    (hb : Γ ⊢[PRAAx] B ≐ B') (hd : Γ ⊢[PRAAx] D ≐ D') (ht : Γ ⊢[PRAAx] T ≐ T')
    (hL : Γ ⊢[PRAAx] localLaw h B D T) : Γ ⊢[PRAAx] localLaw h' B' D' T' := by
  have p := Prf.eqSubst (localLaw (var 0) (var 1) (var 2) (var 3) : Fm PTm 4)
    ![h,B,D,T] ![h',B',D',T'] (fun i => by fin_cases i; exact hh; exact hb; exact hd; exact ht) (by simpa using hL)
  simpa using p

def forwardLaw (H B D t : PTm n) : Fm PTm n := le t H ⟶ localLaw t (cap H B t D) D (state H B t D)
def forwardSyntax (H B D t : PTm n) : BFm n := .imp (.le t H)
  (localSyntax t (cap H B t D) D (state H B t D))
@[simp] theorem subst_forwardLaw {k : ℕ} (σ : Fin n → PTm k) (H B D t : PTm n) :
    (forwardLaw H B D t).subst σ = forwardLaw (Syn.subst σ H) (Syn.subst σ B) (Syn.subst σ D) (Syn.subst σ t) := by
  simp [forwardLaw]
theorem forward_formula (H B D t : PTm n) : formula (forwardSyntax H B D t) = forwardLaw H B D t := by
  simp [forwardSyntax,forwardLaw,formula,local_formula,BFm.le,le]

theorem forward_zero (H B D : PTm n) : Γ ⊢[PRAAx] forwardLaw H B D zero :=
  .impI (local_congr (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (QuadraticTowerMultiplicationHeight.state_zero H B D).wk.eqSymm (local_base _ D))

theorem forward_step (H B D t : PTm n) (ih : Γ ⊢[PRAAx] forwardLaw H B D t) : Γ ⊢[PRAAx]
    forwardLaw H B D (succ t) := by
  refine .impI ?_
  let Δ := le (succ t) H :: Γ
  have ht : Δ ⊢[PRAAx] lt t H := Prf.hyp0
  have previous : Δ ⊢[PRAAx] localLaw t (cap H B t D) D (state H B t D) :=
    .impE ih.wk (le_trans (le_succ_self t) ht)
  have adjusted : Δ ⊢[PRAAx] localLaw t (budget t (cap H B (succ t) D) D) D (state H B t D) :=
    local_congr (.eqRefl _) (QuadraticTowerMultiplicationHeight.cap_link H B t D ht) (.eqRefl _) (.eqRefl _) previous
  have next := local_step t (cap H B (succ t) D) D (state H B t D) adjusted
  exact local_congr (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (QuadraticTowerMultiplicationHeight.state_succ H B t D).eqSymm next

/-- One fixed finite word-pair syntax is reflected before induction. -/
theorem forward_all (H B D : PTm n) : Γ ⊢[PRAAx] .all
    (formula (forwardSyntax (Syn.shift H) (Syn.shift B) (Syn.shift D) (var 0))) := by
  refine Foundations.BoundedSyntaxInduction.induction _ ?_ ?_
  · simpa only [forward_formula,subst_forwardLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      forward_zero (Γ := Γ) H B D
  · simpa only [forward_formula,subst_forwardLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift] using
      forward_step (Γ := formula (forwardSyntax (Syn.shift H) (Syn.shift B) (Syn.shift D) (var 0)) :: Γ.map Fm.shift)
        (Syn.shift H) (Syn.shift B) (Syn.shift D) (var 0)
        (by simpa only [forward_formula] using (Prf.hyp0 (Ax := PRAAx)))

theorem table_commutativity (h B D : PTm n) : Γ ⊢[PRAAx]
    localLaw h B D (QuadraticTowerMultiplicationTable.table h B D) := by
  have gate : Γ ⊢[PRAAx] forwardLaw h B D h := by
    simpa only [forward_formula,subst_forwardLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      (forward_all (Γ := Γ) h B D).allE h
  exact local_congr (.eqRefl _)
    (Foundations.BackwardDemand.horizon_final QuadraticTowerMultiplicationTable.demandF h B D)
    (.eqRefl _) (.eqRefl _) (Prf.impE gate (le_refl h))

theorem query_commutative (h B D A C b : PTm n) (hb : Γ ⊢[PRAAx] le b B)
    (hD : Γ ⊢[PRAAx] radicandsHeight D h b) (ha : Γ ⊢[PRAAx] arrayHeight h A b)
    (hc : Γ ⊢[PRAAx] arrayHeight h C b) : Γ ⊢[PRAAx]
    QuadraticTowerMultiplicationTable.query h B D A C ≐ QuadraticTowerMultiplicationTable.query h B D C A :=
  lookup_commutative h B D _ A C b (table_commutativity h B D) hb hD ha hc

theorem returned_original_commutative (h B D A C b : PTm n) (hb : Γ ⊢[PRAAx] le b B)
    (hD : Γ ⊢[PRAAx] radicandsHeight D h b) (ha : Γ ⊢[PRAAx] arrayHeight h A b)
    (hc : Γ ⊢[PRAAx] arrayHeight h C b) : Γ ⊢[PRAAx]
    PTm.app QuadraticTowerMultiplicationTable.queryF ![h,B,D,A,C] ≐
      PTm.app QuadraticTowerMultiplicationTable.queryF ![h,B,D,C,A] :=
  (QuadraticTowerMultiplicationTable.query_program_at _ _ _ _ _).eqTrans
    ((query_commutative h B D A C b hb hD ha hc).eqTrans
      (QuadraticTowerMultiplicationTable.query_program_at _ _ _ _ _).eqSymm)

def output (h B D A C : PTm n) : PTm n := pairT
  (QuadraticTowerMultiplicationTable.query h B D A C)
    (pairT (QuadraticTowerMultiplicationTable.query h B D C A) (pairT A C))
def outputF : PR 5 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4))
def run (h B D A C : PTm n) : PTm n := PTm.app outputF ![h,B,D,A,C]
@[simp] theorem subst_output {k : ℕ} (σ : Fin n → PTm k) (h B D A C : PTm n) :
    Syn.subst σ (output h B D A C) = output (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ D) (Syn.subst σ A) (Syn.subst σ C) := by simp [output]
@[simp] theorem subst_run {k : ℕ} (σ : Fin n → PTm k) (h B D A C : PTm n) :
    Syn.subst σ (run h B D A C) = run (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ D) (Syn.subst σ A) (Syn.subst σ C) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem program_at (h B D A C : PTm n) : Γ ⊢[PRAAx] run h B D A C ≐ output h B D A C := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![h,B,D,A,C]
theorem returned_forward (h B D A C : PTm n) : Γ ⊢[PRAAx] fstT (run h B D A C) ≐
    QuadraticTowerMultiplicationTable.query h B D A C :=
  (congrFst (program_at _ _ _ _ _)).eqTrans (fst_pair _ _)
theorem returned_tail (h B D A C : PTm n) : Γ ⊢[PRAAx] sndT (run h B D A C) ≐
    pairT (QuadraticTowerMultiplicationTable.query h B D C A) (pairT A C) :=
  (congrSnd (program_at _ _ _ _ _)).eqTrans (snd_pair _ _)
theorem returned_reverse (h B D A C : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run h B D A C)) ≐
    QuadraticTowerMultiplicationTable.query h B D C A :=
  (congrFst (returned_tail _ _ _ _ _)).eqTrans (fst_pair _ _)
theorem returned_originals (h B D A C : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run h B D A C)) ≐ pairT A C :=
  (congrSnd (returned_tail _ _ _ _ _)).eqTrans (snd_pair _ _)
theorem returned_equality (h B D A C b : PTm n) (hb : Γ ⊢[PRAAx] le b B)
    (hD : Γ ⊢[PRAAx] radicandsHeight D h b) (ha : Γ ⊢[PRAAx] arrayHeight h A b)
    (hc : Γ ⊢[PRAAx] arrayHeight h C b) : Γ ⊢[PRAAx]
    fstT (run h B D A C) ≐ fstT (sndT (run h B D A C)) :=
  (returned_forward _ _ _ _ _).eqTrans ((query_commutative h B D A C b hb hD ha hc).eqTrans (returned_reverse _ _ _ _ _).eqSymm)

theorem actual_coefficient_addition_commutative_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (added (var 0) (var 1) (var 2) ≐ added (var 0) (var 2) (var 1)) := closeUniv 3 (added_commutative _ _ _)
theorem actual_multiplication_commutative_predicate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (localLaw (var 0) (var 1) (var 2) (QuadraticTowerMultiplicationTable.table (var 0) (var 1) (var 2))) :=
  closeUniv 3 (table_commutativity _ _ _)
theorem actual_finite_forward_commutativity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (forwardLaw (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (by simpa only [forward_formula,subst_forwardLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
    (forward_all (Γ := ([] : List (Fm PTm 4))) (var 0) (var 1) (var 2)).allE (var 3))
theorem original_heights_actual_multiplication_commutative_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le (var 5) (var 1) ⟶ radicandsHeight (var 2) (var 0) (var 5) ⟶ arrayHeight (var 0) (var 3) (var 5) ⟶ arrayHeight (var 0) (var 4) (var 5) ⟶
      QuadraticTowerMultiplicationTable.query (var 0) (var 1) (var 2) (var 3) (var 4) ≐
        QuadraticTowerMultiplicationTable.query (var 0) (var 1) (var 2) (var 4) (var 3)) :=
  closeUniv 6 (.impI (.impI (.impI (.impI (query_commutative _ _ _ _ _ (var 5) (.hyp (by simp)) (.hyp (by simp)) Prf.hyp1 Prf.hyp0)))))
theorem original_returned_multiplication_commutative_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le (var 5) (var 1) ⟶ radicandsHeight (var 2) (var 0) (var 5) ⟶ arrayHeight (var 0) (var 3) (var 5) ⟶ arrayHeight (var 0) (var 4) (var 5) ⟶
      PTm.app QuadraticTowerMultiplicationTable.queryF ![var 0,var 1,var 2,var 3,var 4] ≐
        PTm.app QuadraticTowerMultiplicationTable.queryF ![var 0,var 1,var 2,var 4,var 3]) :=
  closeUniv 6 (.impI (.impI (.impI (.impI (returned_original_commutative _ _ _ _ _ (var 5) (.hyp (by simp)) (.hyp (by simp)) Prf.hyp1 Prf.hyp0)))))
theorem actual_multiplication_commutativity_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (run (var 0) (var 1) (var 2) (var 3) (var 4) ≐ output (var 0) (var 1) (var 2) (var 3) (var 4)) := closeUniv 5 (program_at _ _ _ _ _)
theorem original_returned_commutativity_payload_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le (var 5) (var 1) ⟶ radicandsHeight (var 2) (var 0) (var 5) ⟶ arrayHeight (var 0) (var 3) (var 5) ⟶ arrayHeight (var 0) (var 4) (var 5) ⟶
      fstT (run (var 0) (var 1) (var 2) (var 3) (var 4)) ≐ fstT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4)))) :=
  closeUniv 6 (.impI (.impI (.impI (.impI (returned_equality _ _ _ _ _ (var 5) (.hyp (by simp)) (.hyp (by simp)) Prf.hyp1 Prf.hyp0)))))

end LeanProofs.IPRA.Algebra.QuadraticTowerMultiplicationCommutativity
