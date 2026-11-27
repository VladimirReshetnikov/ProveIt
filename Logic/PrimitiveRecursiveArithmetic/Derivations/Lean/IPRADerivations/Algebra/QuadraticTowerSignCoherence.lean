import IPRADerivations.Algebra.QuadraticTowerSignTable
import IPRADerivations.Algebra.QuadraticTowerMultiplicationCoherence

/-!
# Independent-cap coherence of the actual recursive sign table

Original scalar-height bounds supply common operands for two actual sign
tables. Checked multiplication coherence compares the exact computed
norms. The real conditional third operand is preserved, then compared at
its derived height bound. No sign-correctness or coherence law is an input.
The conclusion concerns the SAME original numerical radicand array D.
Mathematical sign correctness, change of radicand representation, ordered
quotient laws and the source operation-count bound remain separate.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Algebra.QuadraticTowerSignCoherence

open_ipra
open LeanProofs.IPRA.Analysis
open QuadraticTowerCoefficients (width)
open QuadraticTowerArrayCodec (arrayHeight code horizon)
open QuadraticTowerMultiplicationTable (budget leftHalf rightHalf)
open QuadraticTowerMultiplicationHeight (radicandsHeight word)
open QuadraticTowerSignRecipe (read)
open LeanProofs.IPRA.Foundations.BoundedSyntax (BFm formula)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (entry_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem read_values_proper (h B S A E : PTm n)
    (hV : Γ ⊢[PRAAx] QuadraticTowerCoefficientArithmetic.equalValues h A E) : Γ ⊢[PRAAx]
    read h B S A ≐ read h B S E :=
  congrAp2 remF (entry_congr (.eqRefl _) (QuadraticTowerOperandProperness.code_proper h A E B hV)) (.eqRefl _)

def rowLaw (h B C D T U b u : PTm n) : Fm PTm n := radicandsHeight D h b ⟶
  arrayHeight h (word h b u) b ⟶ read h B T (word h b u) ≐ read h C U (word h b u)
def atHeight (h B C D T U b : PTm n) : Fm PTm n := .all
  (lt (var 0) (Syn.shift (horizon h b)) ⟶ rowLaw (Syn.shift h) (Syn.shift B) (Syn.shift C)
    (Syn.shift D) (Syn.shift T) (Syn.shift U) (Syn.shift b) (var 0))
def localLaw (h B C D T U : PTm n) : Fm PTm n := .all
  (lt (var 0) (succ (Syn.shift B)) ⟶ le (var 0) (Syn.shift C) ⟶
    atHeight (Syn.shift h) (Syn.shift B) (Syn.shift C) (Syn.shift D) (Syn.shift T) (Syn.shift U) (var 0))
ipra_subst rowLaw
@[simp] theorem subst_atHeight {k : ℕ} (σ : Fin n → PTm k) (h B C D T U b : PTm n) :
    (atHeight h B C D T U b).subst σ = atHeight (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ C)
      (Syn.subst σ D) (Syn.subst σ T) (Syn.subst σ U) (Syn.subst σ b) := by
  simp [atHeight,Syn.subst_shift,Syn.shift_subst]
  simp only [Syn.shift,QuadraticTowerArrayCodec.subst_horizon,Syn.subst_subst]
ipra_subst localLaw [Syn.subst_shift, Syn.shift_subst]

def rowSyntax (h B C D T U b u : PTm n) : BFm n :=
  .imp (QuadraticTowerMultiplicationHeight.radicandsSyntax D h b)
    (.imp (QuadraticTowerMultiplicationHeight.heightSyntax h (word h b u) b)
      (.eq (read h B T (word h b u)) (read h C U (word h b u))))
def heightRowsSyntax (h B C D T U b : PTm n) : BFm n := .all (horizon h b)
  (rowSyntax (Syn.shift h) (Syn.shift B) (Syn.shift C) (Syn.shift D) (Syn.shift T) (Syn.shift U)
    (Syn.shift b) (var 0))
def localSyntax (h B C D T U : PTm n) : BFm n := .all (succ B)
  (.imp (.le (var 0) (Syn.shift C)) (heightRowsSyntax (Syn.shift h) (Syn.shift B) (Syn.shift C)
    (Syn.shift D) (Syn.shift T) (Syn.shift U) (var 0)))
theorem row_formula (h B C D T U b u : PTm n) : formula (rowSyntax h B C D T U b u) = rowLaw h B C D T U b u := by
  simp [rowSyntax,rowLaw,formula,QuadraticTowerMultiplicationHeight.radicands_formula,
    QuadraticTowerMultiplicationHeight.height_formula]
theorem height_rows_formula (h B C D T U b : PTm n) : formula (heightRowsSyntax h B C D T U b) = atHeight h B C D T U b := by
  simp [heightRowsSyntax,atHeight,formula,row_formula]
theorem local_formula (h B C D T U : PTm n) : formula (localSyntax h B C D T U) = localLaw h B C D T U := by
  simp [localSyntax,localLaw,formula,height_rows_formula,BFm.le,le,Syn.shift]

theorem local_at (h B C D T U b u : PTm n) (hL : Γ ⊢[PRAAx] localLaw h B C D T U)
    (hb : Γ ⊢[PRAAx] le b B) (hc : Γ ⊢[PRAAx] le b C) (hu : Γ ⊢[PRAAx] lt u (horizon h b))
    (hD : Γ ⊢[PRAAx] radicandsHeight D h b) (ha : Γ ⊢[PRAAx] arrayHeight h (word h b u) b) : Γ ⊢[PRAAx]
    read h B T (word h b u) ≐ read h C U (word h b u) := by
  have bg : Γ ⊢[PRAAx] lt b (succ B) ⟶ le b C ⟶ atHeight h B C D T U b := by
    simpa [localLaw] using hL.allE b
  have heightRule := Prf.impE (Prf.impE bg ((succ_monus_succ _ _).eqTrans hb)) hc
  have ug : Γ ⊢[PRAAx] lt u (horizon h b) ⟶ rowLaw h B C D T U b u := by
    simpa [atHeight] using heightRule.allE u
  exact .impE (.impE (.impE ug hu) hD) ha

theorem read_coherent (h B C D T U b A : PTm n) (hL : Γ ⊢[PRAAx] localLaw h B C D T U)
    (hb : Γ ⊢[PRAAx] le b B) (hc : Γ ⊢[PRAAx] le b C)
    (hD : Γ ⊢[PRAAx] radicandsHeight D h b) (ha : Γ ⊢[PRAAx] arrayHeight h A b) : Γ ⊢[PRAAx]
    read h B T A ≐ read h C U A := by
  have aw := QuadraticTowerMultiplicationHeight.restored_height h A b b ha (le_refl _)
  have middle := local_at h B C D T U b (code h A b) hL hb hc (QuadraticTowerArrayCodec.code_bound h A b ha) hD aw
  have av := QuadraticTowerMultiplicationCoherence.restored_values h A b ha
  exact (read_values_proper h B T _ A av).eqSymm.eqTrans (middle.eqTrans (read_values_proper h C U _ A av))

theorem norm_coherent (h B C D A b : PTm n) (hb : Γ ⊢[PRAAx] le b B) (hc : Γ ⊢[PRAAx] le b C)
    (hD : Γ ⊢[PRAAx] radicandsHeight D (succ h) b) (ha : Γ ⊢[PRAAx] arrayHeight (succ h) A b) : Γ ⊢[PRAAx]
    QuadraticTowerSignRecipe.norm h B D A ≐ QuadraticTowerSignRecipe.norm h C D A := by
  let K := budget h B D
  let J := budget h C D
  let g := QuadraticTowerScalarBudget.growth (QuadraticTowerGrowth.path h) b
  have bg : Γ ⊢[PRAAx] le b g := QuadraticTowerGrowth.growth_inflation _ _
  have gK : Γ ⊢[PRAAx] le g K := QuadraticTowerGrowth.lower_path_budget h B D b hb
  have gJ : Γ ⊢[PRAAx] le g J := QuadraticTowerGrowth.lower_path_budget h C D b hc
  have bK := le_trans bg gK
  have bJ := le_trans bg gJ
  have rh := QuadraticTowerMultiplicationHeight.radicands_prefix D h (succ h) b hD (le_succ_self h)
  have a0 := QuadraticTowerMultiplicationHeight.left_height h A b ha
  have a1 := QuadraticTowerMultiplicationHeight.right_height h A b ha
  have aa := QuadraticTowerMultiplicationCoherence.query_cap_independent h K J D _ _ b bK bJ rh a0 a0
  have bb := QuadraticTowerMultiplicationCoherence.query_cap_independent h K J D _ _ b bK bJ rh a1 a1
  let bbK := QuadraticTowerMultiplicationTable.query h K D (rightHalf h A) (rightHalf h A)
  have bbH : Γ ⊢[PRAAx] arrayHeight h bbK g := QuadraticTowerMultiplicationHeight.query_height h K D _ _ b bK rh a1 a1
  have dH := QuadraticTowerMultiplicationHeight.array_mono h (entry D h) b g
    (QuadraticTowerMultiplicationHeight.radicand_at D (succ h) b h hD (le_refl _)) bg
  have dbb := (QuadraticTowerMultiplicationCoherence.query_cap_independent h K J D (entry D h) bbK g gK gJ
    (QuadraticTowerMultiplicationHeight.radicands_mono D h b g rh bg) dH bbH).eqTrans
      (QuadraticTowerMultiplicationCoherence.lookup_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) (.eqRefl _) bb)
  exact QuadraticTowerCoefficientArithmetic.added_congr (.eqRefl _) aa
    (QuadraticTowerCoefficientArithmetic.negated_congr (.eqRefl _) dbb)

theorem third_select_congr {s s' d d' q q' : PTm n}
    (hs : Γ ⊢[PRAAx] s ≐ s') (hd : Γ ⊢[PRAAx] d ≐ d') (hq : Γ ⊢[PRAAx] q ≐ q') : Γ ⊢[PRAAx]
    Foundations.GuardedTotalization.sel (eqb s zero) d q ≐ Foundations.GuardedTotalization.sel (eqb s' zero) d' q' := by
  ipra_congr (Foundations.GuardedTotalization.sel (eqb (var 0) zero) (var 1) (var 2) : PTm 3) with
    [hs, hd, hq] using [Foundations.GuardedTotalization.sel]

theorem dispatch_congr {s s' t t' u u' : PTm n}
    (hs : Γ ⊢[PRAAx] s ≐ s') (ht : Γ ⊢[PRAAx] t ≐ t') (hu : Γ ⊢[PRAAx] u ≐ u') : Γ ⊢[PRAAx]
    QuadraticTowerSignRecipe.dispatch s t u ≐ QuadraticTowerSignRecipe.dispatch s' t' u' := by
  ipra_congr (QuadraticTowerSignRecipe.dispatch (var 0) (var 1) (var 2) : PTm 3) with [hs, ht, hu]

theorem recipe_coherent (h B C D T U b A : PTm n)
    (hL : Γ ⊢[PRAAx] localLaw h (budget h B D) (budget h C D) D T U)
    (hb : Γ ⊢[PRAAx] le b B) (hc : Γ ⊢[PRAAx] le b C)
    (hD : Γ ⊢[PRAAx] radicandsHeight D (succ h) b) (ha : Γ ⊢[PRAAx] arrayHeight (succ h) A b) : Γ ⊢[PRAAx]
    QuadraticTowerSignRecipe.recipe h B D T A ≐ QuadraticTowerSignRecipe.recipe h C D U A := by
  let K := budget h B D
  let J := budget h C D
  let g := QuadraticTowerScalarBudget.growth (QuadraticTowerGrowth.path (succ h)) b
  have bg : Γ ⊢[PRAAx] le b g := QuadraticTowerGrowth.growth_inflation _ _
  have gK : Γ ⊢[PRAAx] le g K := QuadraticTowerGrowth.path_growth_budget h B D b hb
  have gJ : Γ ⊢[PRAAx] le g J := QuadraticTowerGrowth.path_growth_budget h C D b hc
  have bK := le_trans bg gK
  have bJ := le_trans bg gJ
  have rh := QuadraticTowerMultiplicationHeight.radicands_prefix D h (succ h) b hD (le_succ_self h)
  have a0 := QuadraticTowerMultiplicationHeight.left_height h A b ha
  have a1 := QuadraticTowerMultiplicationHeight.right_height h A b ha
  have first : Γ ⊢[PRAAx] QuadraticTowerSignRecipe.firstTag h B D T A ≐ QuadraticTowerSignRecipe.firstTag h C D U A :=
    read_coherent h K J D T U b (leftHalf h A) hL bK bJ rh a0
  have second : Γ ⊢[PRAAx] QuadraticTowerSignRecipe.secondTag h B D T A ≐ QuadraticTowerSignRecipe.secondTag h C D U A :=
    read_coherent h K J D T U b (rightHalf h A) hL bK bJ rh a1
  have thirdInput : Γ ⊢[PRAAx] QuadraticTowerSignRecipe.thirdInput h B D T A ≐ QuadraticTowerSignRecipe.thirdInput h C D U A :=
    third_select_congr first (.eqRefl _) (norm_coherent h B C D A b hb hc hD ha)
  have thirdH : Γ ⊢[PRAAx] arrayHeight h (QuadraticTowerSignRecipe.thirdInput h B D T A) g :=
    QuadraticTowerSignRecipe.third_input_height h B D T A b hb hD ha
  have third : Γ ⊢[PRAAx] QuadraticTowerSignRecipe.thirdTag h B D T A ≐ QuadraticTowerSignRecipe.thirdTag h C D U A :=
    (read_coherent h K J D T U g _ hL gK gJ (QuadraticTowerMultiplicationHeight.radicands_mono D h b g rh bg) thirdH).eqTrans
      (QuadraticTowerSignRecipe.read_operand_congr h J U _ _ thirdInput)
  exact dispatch_congr first second third

theorem step_read_normalized (h B S D A : PTm n) (ha : Γ ⊢[PRAAx] arrayHeight (succ h) A B) : Γ ⊢[PRAAx]
    read (succ h) B (QuadraticTowerSignTable.step h B S D) A ≐ QuadraticTowerSignRecipe.recipe h B D S
      (QuadraticTowerArrayCodec.normalized (succ h) A) :=
  (QuadraticTowerSignRecipe.read_exact _ _ _ _
    (QuadraticTowerSignTable.step_entry_bound h B S D _ (QuadraticTowerArrayCodec.code_bound (succ h) A B ha))).eqTrans
      ((QuadraticTowerSignTable.step_lookup h B S D _ (QuadraticTowerArrayCodec.code_bound (succ h) A B ha)).eqTrans
        (QuadraticTowerSignTable.recipe_operand_congr _ _ _ _ _ _ (QuadraticTowerArrayNormalization.restored_normalized _ _ _ ha)))

theorem step_coherent_at (h B C D T U b A : PTm n)
    (hL : Γ ⊢[PRAAx] localLaw h (budget h B D) (budget h C D) D T U)
    (hb : Γ ⊢[PRAAx] le b B) (hc : Γ ⊢[PRAAx] le b C)
    (hD : Γ ⊢[PRAAx] radicandsHeight D (succ h) b) (ha : Γ ⊢[PRAAx] arrayHeight (succ h) A b) : Γ ⊢[PRAAx]
    read (succ h) B (QuadraticTowerSignTable.step h B T D) A ≐ read (succ h) C (QuadraticTowerSignTable.step h C U D) A := by
  have an := QuadraticTowerMultiplicationHeight.array_congr (.eqRefl _)
    (QuadraticTowerArrayNormalization.restored_normalized (succ h) A b ha) (.eqRefl _)
      (QuadraticTowerMultiplicationHeight.restored_height (succ h) A b b ha (le_refl _))
  exact (step_read_normalized h B T D A (QuadraticTowerMultiplicationHeight.array_mono _ _ _ _ ha hb)).eqTrans
    ((recipe_coherent h B C D T U b _ hL hb hc hD an).eqTrans
      (step_read_normalized h C U D A (QuadraticTowerMultiplicationHeight.array_mono _ _ _ _ ha hc)).eqSymm)

theorem local_step (h B C D T U : PTm n)
    (hL : Γ ⊢[PRAAx] localLaw h (budget h B D) (budget h C D) D T U) : Γ ⊢[PRAAx]
    localLaw (succ h) B C D (QuadraticTowerSignTable.step h B T D) (QuadraticTowerSignTable.step h C U D) := by
  have ls : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx]
      localLaw (Syn.shift (Syn.shift h))
        (budget (Syn.shift (Syn.shift h)) (Syn.shift (Syn.shift B)) (Syn.shift (Syn.shift D)))
        (budget (Syn.shift (Syn.shift h)) (Syn.shift (Syn.shift C)) (Syn.shift (Syn.shift D)))
        (Syn.shift (Syn.shift D)) (Syn.shift (Syn.shift T)) (Syn.shift (Syn.shift U)) := by
    simpa only [Fm.shift,subst_localLaw,QuadraticTowerMultiplicationTable.subst_budget,Syn.shift] using hL.shift.shift
  refine .allI (.impI (.impI (.allI (.impI (.impI (.impI ?_))))))
  let h' := Syn.shift (Syn.shift h)
  let B' := Syn.shift (Syn.shift B)
  let C' := Syn.shift (Syn.shift C)
  let D' := Syn.shift (Syn.shift D)
  let T' := Syn.shift (Syn.shift T)
  let U' := Syn.shift (Syn.shift U)
  let b := (var 1 : PTm (n+2))
  let u := (var 0 : PTm (n+2))
  let R := horizon (succ h') b
  let Δ := arrayHeight (succ h') (word (succ h') b u) b :: radicandsHeight D' (succ h') b ::
    lt u R :: le b C' :: lt b (succ B') :: (Γ.map Fm.shift).map Fm.shift
  have ha : Δ ⊢[PRAAx] arrayHeight (succ h') (word (succ h') b u) b := Prf.hyp0
  have hd : Δ ⊢[PRAAx] radicandsHeight D' (succ h') b := .hyp (by simp [Δ])
  have hbRange : Δ ⊢[PRAAx] lt b (succ B') := .hyp (by simp [Δ])
  have hb : Δ ⊢[PRAAx] le b B' := (succ_monus_succ _ _).eqSymm.eqTrans hbRange
  have hc : Δ ⊢[PRAAx] le b C' := .hyp (by simp [Δ])
  have lower : Δ ⊢[PRAAx] localLaw h' (budget h' B' D') (budget h' C' D') D' T' U' := ls.wk.wk.wk.wk.wk
  simpa [Δ,h',B',C',D',T',U',b,u,R,Fm.shift,Syn.shift] using
    step_coherent_at (Γ := Δ) h' B' C' D' T' U' b (word (succ h') b u) lower hb hc hd ha

theorem read_table_congr (h B S T A : PTm n) (hS : Γ ⊢[PRAAx] S ≐ T) : Γ ⊢[PRAAx] read h B S A ≐ read h B T A :=
  congrAp2 remF (entry_congr hS (.eqRefl _)) (.eqRefl _)

theorem base_read_ground (B A : PTm n) (ha : Γ ⊢[PRAAx] arrayHeight zero A B) : Γ ⊢[PRAAx]
    read zero B (QuadraticTowerSignTable.base B) A ≐
      QuadraticTowerSignTable.groundTag (RationalArithmetic.recode (entry A zero)) :=
  (read_table_congr zero B _ _ A (QuadraticTowerSignTable.table_zero B zero).eqSymm).eqTrans
    (QuadraticTowerSignTable.query_zero B zero A ha)

theorem base_coherent_at (B C b A : PTm n) (hb : Γ ⊢[PRAAx] le b B) (hc : Γ ⊢[PRAAx] le b C)
    (ha : Γ ⊢[PRAAx] arrayHeight zero A b) : Γ ⊢[PRAAx]
    read zero B (QuadraticTowerSignTable.base B) A ≐ read zero C (QuadraticTowerSignTable.base C) A :=
  (base_read_ground B A (QuadraticTowerMultiplicationHeight.array_mono _ _ _ _ ha hb)).eqTrans
    (base_read_ground C A (QuadraticTowerMultiplicationHeight.array_mono _ _ _ _ ha hc)).eqSymm

theorem local_base (B C D : PTm n) : Γ ⊢[PRAAx] localLaw zero B C D
    (QuadraticTowerSignTable.base B) (QuadraticTowerSignTable.base C) := by
  refine .allI (.impI (.impI (.allI (.impI (.impI (.impI ?_))))))
  let B' := Syn.shift (Syn.shift B)
  let C' := Syn.shift (Syn.shift C)
  let D' := Syn.shift (Syn.shift D)
  let b := (var 1 : PTm (n+2))
  let u := (var 0 : PTm (n+2))
  let R := horizon zero b
  let Δ := arrayHeight zero (word zero b u) b :: radicandsHeight D' zero b ::
    lt u R :: le b C' :: lt b (succ B') :: (Γ.map Fm.shift).map Fm.shift
  have hbRange : Δ ⊢[PRAAx] lt b (succ B') := .hyp (by simp [Δ])
  have hb : Δ ⊢[PRAAx] le b B' := (succ_monus_succ _ _).eqSymm.eqTrans hbRange
  have hc : Δ ⊢[PRAAx] le b C' := .hyp (by simp [Δ])
  have ha : Δ ⊢[PRAAx] arrayHeight zero (word zero b u) b := Prf.hyp0
  simpa [Δ,B',C',D',b,u,R,Fm.shift,Syn.shift] using base_coherent_at (Γ := Δ) B' C' b (word zero b u) hb hc ha

theorem local_congr {h h' B B' C C' D D' T T' U U' : PTm n}
    (hh : Γ ⊢[PRAAx] h ≐ h') (hb : Γ ⊢[PRAAx] B ≐ B') (hc : Γ ⊢[PRAAx] C ≐ C')
    (hd : Γ ⊢[PRAAx] D ≐ D') (ht : Γ ⊢[PRAAx] T ≐ T') (hu : Γ ⊢[PRAAx] U ≐ U')
    (hL : Γ ⊢[PRAAx] localLaw h B C D T U) : Γ ⊢[PRAAx] localLaw h' B' C' D' T' U' := by
  have p := Prf.eqSubst (localLaw (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : Fm PTm 6)
    ![h,B,C,D,T,U] ![h',B',C',D',T',U']
      (fun i => by fin_cases i; exact hh; exact hb; exact hc; exact hd; exact ht; exact hu) (by simpa using hL)
  simpa using p

open QuadraticTowerMultiplicationHeight (cap)

def state (H B t D : PTm n) : PTm n := Foundations.DemandRecursion.V QuadraticTowerMultiplicationTable.demandF
  QuadraticTowerSignTable.baseSchema QuadraticTowerSignTable.stepSchema H B t D
def forwardLaw (H B C D t : PTm n) : Fm PTm n := le t H ⟶
  localLaw t (cap H B t D) (cap H C t D) D (state H B t D) (state H C t D)
def forwardSyntax (H B C D t : PTm n) : BFm n := .imp (.le t H)
  (localSyntax t (cap H B t D) (cap H C t D) D (state H B t D) (state H C t D))
ipra_subst state
ipra_subst forwardLaw
theorem forward_formula (H B C D t : PTm n) : formula (forwardSyntax H B C D t) = forwardLaw H B C D t := by
  simp [forwardSyntax,forwardLaw,formula,local_formula,BFm.le,le]

theorem state_zero (H B D : PTm n) : Γ ⊢[PRAAx] state H B zero D ≐ QuadraticTowerSignTable.base (cap H B zero D) := by
  simpa only [state,QuadraticTowerMultiplicationHeight.cap,QuadraticTowerSignTable.baseSchema,
    inst2,QuadraticTowerSignTable.subst_base,Syn.subst_var,Matrix.cons_val_zero] using
      Foundations.DemandRecursion.V_zero (Γ := Γ) QuadraticTowerMultiplicationTable.demandF
        QuadraticTowerSignTable.baseSchema QuadraticTowerSignTable.stepSchema H B D
theorem state_succ (H B t D : PTm n) : Γ ⊢[PRAAx] state H B (succ t) D ≐
    QuadraticTowerSignTable.step t (cap H B (succ t) D) (state H B t D) D := by
  simpa only [state,QuadraticTowerMultiplicationHeight.cap,Foundations.DemandRecursion.appF,
    QuadraticTowerSignTable.stepSchema,QuadraticTowerSignTable.subst_step,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] using
      Foundations.DemandRecursion.V_succ (Γ := Γ) QuadraticTowerMultiplicationTable.demandF
        QuadraticTowerSignTable.baseSchema QuadraticTowerSignTable.stepSchema H B t D

theorem forward_zero (H B C D : PTm n) : Γ ⊢[PRAAx] forwardLaw H B C D zero :=
  .impI (local_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (state_zero H B D).wk.eqSymm (state_zero H C D).wk.eqSymm (local_base _ _ D))

theorem forward_step (H B C D t : PTm n) (ih : Γ ⊢[PRAAx] forwardLaw H B C D t) :
    Γ ⊢[PRAAx] forwardLaw H B C D (succ t) := by
  refine .impI ?_
  let Δ := le (succ t) H :: Γ
  have ht : Δ ⊢[PRAAx] lt t H := Prf.hyp0
  have previous : Δ ⊢[PRAAx] localLaw t (cap H B t D) (cap H C t D) D (state H B t D) (state H C t D) :=
    .impE ih.wk (le_trans (le_succ_self t) ht)
  have adjusted : Δ ⊢[PRAAx] localLaw t (budget t (cap H B (succ t) D) D) (budget t (cap H C (succ t) D) D)
      D (state H B t D) (state H C t D) :=
    local_congr (.eqRefl _) (QuadraticTowerMultiplicationHeight.cap_link H B t D ht)
      (QuadraticTowerMultiplicationHeight.cap_link H C t D ht) (.eqRefl _) (.eqRefl _) (.eqRefl _) previous
  have next := local_step t (cap H B (succ t) D) (cap H C (succ t) D) D (state H B t D) (state H C t D) adjusted
  exact local_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (state_succ H B t D).eqSymm (state_succ H C t D).eqSymm next

theorem forward_all (H B C D : PTm n) : Γ ⊢[PRAAx] .all
    (formula (forwardSyntax (Syn.shift H) (Syn.shift B) (Syn.shift C) (Syn.shift D) (var 0))) := by
  refine Foundations.BoundedSyntaxInduction.induction_of_formula _ (forward_formula _ _ _ _ _) ?_ ?_
  · simpa only [subst_forwardLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      forward_zero (Γ := Γ) H B C D
  · simpa only [subst_forwardLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift] using
      forward_step (Syn.shift H) (Syn.shift B) (Syn.shift C) (Syn.shift D) (var 0) (Prf.hyp0 (Γ := Γ.map Fm.shift))

theorem table_coherence (h B C D : PTm n) : Γ ⊢[PRAAx] localLaw h B C D
    (QuadraticTowerSignTable.table h B D) (QuadraticTowerSignTable.table h C D) := by
  have gate : Γ ⊢[PRAAx] forwardLaw h B C D h := by
    simpa only [forward_formula,subst_forwardLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      (forward_all (Γ := Γ) h B C D).allE h
  have terminal : Γ ⊢[PRAAx] localLaw h (cap h B h D) (cap h C h D) D (state h B h D) (state h C h D) :=
    .impE gate (le_refl h)
  exact local_congr (.eqRefl _)
    (Foundations.BackwardDemand.horizon_final QuadraticTowerMultiplicationTable.demandF h B D)
    (Foundations.BackwardDemand.horizon_final QuadraticTowerMultiplicationTable.demandF h C D)
    (.eqRefl _) (.eqRefl _) (.eqRefl _) terminal

theorem query_cap_independent (h B C D A b : PTm n) (hb : Γ ⊢[PRAAx] le b B) (hc : Γ ⊢[PRAAx] le b C)
    (hD : Γ ⊢[PRAAx] radicandsHeight D h b) (ha : Γ ⊢[PRAAx] arrayHeight h A b) : Γ ⊢[PRAAx]
    QuadraticTowerSignTable.query h B D A ≐ QuadraticTowerSignTable.query h C D A :=
  read_coherent h B C D _ _ b A (table_coherence h B C D) hb hc hD ha

theorem query_values_independent_caps (h B C D A E b : PTm n) (hb : Γ ⊢[PRAAx] le b B) (hc : Γ ⊢[PRAAx] le b C)
    (hD : Γ ⊢[PRAAx] radicandsHeight D h b) (ha : Γ ⊢[PRAAx] arrayHeight h A b)
    (hV : Γ ⊢[PRAAx] QuadraticTowerCoefficientArithmetic.equalValues h A E) : Γ ⊢[PRAAx]
    QuadraticTowerSignTable.query h B D A ≐ QuadraticTowerSignTable.query h C D E :=
  (query_cap_independent h B C D A b hb hc hD ha).eqTrans
    (read_values_proper h C (QuadraticTowerSignTable.table h C D) A E hV)

theorem query_program_independent_caps (h B C D A b : PTm n) (hb : Γ ⊢[PRAAx] le b B) (hc : Γ ⊢[PRAAx] le b C)
    (hD : Γ ⊢[PRAAx] radicandsHeight D h b) (ha : Γ ⊢[PRAAx] arrayHeight h A b) : Γ ⊢[PRAAx]
    PTm.app QuadraticTowerSignTable.queryF ![h,B,D,A] ≐ PTm.app QuadraticTowerSignTable.queryF ![h,C,D,A] :=
  (QuadraticTowerSignTable.query_program_at _ _ _ _).eqTrans
    ((query_cap_independent h B C D A b hb hc hD ha).eqTrans (QuadraticTowerSignTable.query_program_at _ _ _ _).eqSymm)

theorem returned_cap_independent (h B C D A b : PTm n) (hb : Γ ⊢[PRAAx] le b B) (hc : Γ ⊢[PRAAx] le b C)
    (hD : Γ ⊢[PRAAx] radicandsHeight D h b) (ha : Γ ⊢[PRAAx] arrayHeight h A b) : Γ ⊢[PRAAx]
    fstT (QuadraticTowerSignTable.run h B D A) ≐ fstT (QuadraticTowerSignTable.run h C D A) :=
  (QuadraticTowerSignTable.returned_tag _ _ _ _).eqTrans
    ((query_cap_independent h B C D A b hb hc hD ha).eqTrans (QuadraticTowerSignTable.returned_tag _ _ _ _).eqSymm)

theorem actual_norm_independent_caps_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le (var 5) (var 1) ⟶ le (var 5) (var 2) ⟶ radicandsHeight (var 3) (succ (var 0)) (var 5) ⟶
      arrayHeight (succ (var 0)) (var 4) (var 5) ⟶
        QuadraticTowerSignRecipe.norm (var 0) (var 1) (var 3) (var 4) ≐ QuadraticTowerSignRecipe.norm (var 0) (var 2) (var 3) (var 4)) :=
  closeUniv 6 (.impI (.impI (.impI (.impI (norm_coherent _ _ _ _ _ (var 5)
    (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)))))))

theorem actual_independent_sign_tables_coherent_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (localLaw (var 0) (var 1) (var 2) (var 3)
      (QuadraticTowerSignTable.table (var 0) (var 1) (var 3)) (QuadraticTowerSignTable.table (var 0) (var 2) (var 3))) :=
  closeUniv 4 (table_coherence _ _ _ _)

theorem actual_paired_sign_forward_coherent_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le (var 4) (var 0) ⟶ localLaw (var 4) (cap (var 0) (var 1) (var 4) (var 3)) (cap (var 0) (var 2) (var 4) (var 3))
      (var 3) (state (var 0) (var 1) (var 4) (var 3)) (state (var 0) (var 2) (var 4) (var 3))) := by
  apply closeUniv 5
  have proof : ([] : List (Fm PTm 5)) ⊢[PRAAx] forwardLaw (var 0) (var 1) (var 2) (var 3) (var 4) := by
    simpa only [forward_formula,subst_forwardLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      (forward_all (Γ := []) (var 0 : PTm 5) (var 1) (var 2) (var 3)).allE (var 4)
  exact proof

theorem actual_sign_query_independent_caps_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le (var 5) (var 1) ⟶ le (var 5) (var 2) ⟶ radicandsHeight (var 3) (var 0) (var 5) ⟶
      arrayHeight (var 0) (var 4) (var 5) ⟶
        QuadraticTowerSignTable.query (var 0) (var 1) (var 3) (var 4) ≐ QuadraticTowerSignTable.query (var 0) (var 2) (var 3) (var 4)) :=
  closeUniv 6 (.impI (.impI (.impI (.impI (query_cap_independent _ _ _ _ _ (var 5)
    (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)))))))

theorem actual_sign_values_independent_caps_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (le (var 6) (var 1) ⟶ le (var 6) (var 2) ⟶ radicandsHeight (var 3) (var 0) (var 6) ⟶
      arrayHeight (var 0) (var 4) (var 6) ⟶ QuadraticTowerCoefficientArithmetic.equalValues (var 0) (var 4) (var 5) ⟶
        QuadraticTowerSignTable.query (var 0) (var 1) (var 3) (var 4) ≐ QuadraticTowerSignTable.query (var 0) (var 2) (var 3) (var 5)) :=
  closeUniv 7 (.impI (.impI (.impI (.impI (.impI (query_values_independent_caps _ _ _ _ _ _ (var 6)
    (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp))))))))

theorem actual_sign_program_independent_caps_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le (var 5) (var 1) ⟶ le (var 5) (var 2) ⟶ radicandsHeight (var 3) (var 0) (var 5) ⟶
      arrayHeight (var 0) (var 4) (var 5) ⟶ PTm.app QuadraticTowerSignTable.queryF ![var 0,var 1,var 3,var 4] ≐
        PTm.app QuadraticTowerSignTable.queryF ![var 0,var 2,var 3,var 4]) :=
  closeUniv 6 (.impI (.impI (.impI (.impI (query_program_independent_caps _ _ _ _ _ (var 5)
    (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)))))))

theorem actual_returned_sign_independent_caps_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le (var 5) (var 1) ⟶ le (var 5) (var 2) ⟶ radicandsHeight (var 3) (var 0) (var 5) ⟶
      arrayHeight (var 0) (var 4) (var 5) ⟶ fstT (QuadraticTowerSignTable.run (var 0) (var 1) (var 3) (var 4)) ≐
        fstT (QuadraticTowerSignTable.run (var 0) (var 2) (var 3) (var 4))) :=
  closeUniv 6 (.impI (.impI (.impI (.impI (returned_cap_independent _ _ _ _ _ (var 5)
    (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)))))))

end LeanProofs.IPRA.Algebra.QuadraticTowerSignCoherence
