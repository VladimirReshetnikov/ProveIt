import IPRADerivations.Algebra.QuadraticTowerOperandProperness
import IPRADerivations.Algebra.QuadraticTowerMultiplicationHeight

/-!
# Common original operands in independently budgeted tower tables

The compared programs are the original predetermined-demand tables. A
bounded local comparison enumerates common operands at their own numerical
height bound, independently of the two table caps. This permits the actual
computed be operand to be compared at its derived larger bound. The final
construction compares two actual forward states by one bounded Boolean
invariant, with the terminal depths and both caps held fixed.
Original coefficient and radicand height bounds suffice for exact equality
of the resulting query codes. There is no ordering assumption between
the caps and no supplied output or coherence law. Tower ring identities,
radicand representation changes, and sign/order remain separate.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Algebra.QuadraticTowerMultiplicationCoherence

open_ipra
open LeanProofs.IPRA.Analysis
open QuadraticTowerCoefficients (width)
open QuadraticTowerArrayCodec (arrayHeight code horizon)
open QuadraticTowerMultiplicationTable (lookup budget)
open QuadraticTowerMultiplicationHeight (radicandsHeight word)
open LeanProofs.IPRA.Foundations.BoundedSyntax (BFm formula)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (entry_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def rowLaw (h B C D T U b u v : PTm n) : Fm PTm n := radicandsHeight D h b ⟶
  arrayHeight h (word h b u) b ⟶ arrayHeight h (word h b v) b ⟶
    lookup h B T (word h b u) (word h b v) ≐ lookup h C U (word h b u) (word h b v)
def atWord (h B C D T U b u : PTm n) : Fm PTm n := .all
  (lt (var 0) (Syn.shift (horizon h b)) ⟶ rowLaw (Syn.shift h) (Syn.shift B) (Syn.shift C)
    (Syn.shift D) (Syn.shift T) (Syn.shift U) (Syn.shift b) (Syn.shift u) (var 0))
def atHeight (h B C D T U b : PTm n) : Fm PTm n := .all
  (lt (var 0) (Syn.shift (horizon h b)) ⟶ atWord (Syn.shift h) (Syn.shift B) (Syn.shift C)
    (Syn.shift D) (Syn.shift T) (Syn.shift U) (Syn.shift b) (var 0))
def localLaw (h B C D T U : PTm n) : Fm PTm n := .all
  (lt (var 0) (succ (Syn.shift B)) ⟶ le (var 0) (Syn.shift C) ⟶
    atHeight (Syn.shift h) (Syn.shift B) (Syn.shift C) (Syn.shift D) (Syn.shift T) (Syn.shift U) (var 0))

ipra_subst rowLaw
@[simp] theorem subst_atWord {k : ℕ} (σ : Fin n → PTm k) (h B C D T U b u : PTm n) :
    (atWord h B C D T U b u).subst σ = atWord (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ C)
      (Syn.subst σ D) (Syn.subst σ T) (Syn.subst σ U) (Syn.subst σ b) (Syn.subst σ u) := by
  simp [atWord,Syn.subst_shift,Syn.shift_subst]
  simp only [Syn.shift,QuadraticTowerArrayCodec.subst_horizon,Syn.subst_subst]
@[simp] theorem subst_atHeight {k : ℕ} (σ : Fin n → PTm k) (h B C D T U b : PTm n) :
    (atHeight h B C D T U b).subst σ = atHeight (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ C)
      (Syn.subst σ D) (Syn.subst σ T) (Syn.subst σ U) (Syn.subst σ b) := by
  simp [atHeight,Syn.subst_shift,Syn.shift_subst]
  simp only [Syn.shift,QuadraticTowerArrayCodec.subst_horizon,Syn.subst_subst]
ipra_subst localLaw [Syn.subst_shift, Syn.shift_subst]

def rowSyntax (h B C D T U b u v : PTm n) : BFm n :=
  .imp (QuadraticTowerMultiplicationHeight.radicandsSyntax D h b)
    (.imp (QuadraticTowerMultiplicationHeight.heightSyntax h (word h b u) b)
      (.imp (QuadraticTowerMultiplicationHeight.heightSyntax h (word h b v) b)
        (.eq (lookup h B T (word h b u) (word h b v)) (lookup h C U (word h b u) (word h b v)))))
def wordSyntax (h B C D T U b u : PTm n) : BFm n := .all (horizon h b)
  (rowSyntax (Syn.shift h) (Syn.shift B) (Syn.shift C) (Syn.shift D) (Syn.shift T) (Syn.shift U)
    (Syn.shift b) (Syn.shift u) (var 0))
def heightRowsSyntax (h B C D T U b : PTm n) : BFm n := .all (horizon h b)
  (wordSyntax (Syn.shift h) (Syn.shift B) (Syn.shift C) (Syn.shift D) (Syn.shift T) (Syn.shift U)
    (Syn.shift b) (var 0))
def localSyntax (h B C D T U : PTm n) : BFm n := .all (succ B)
  (.imp (.le (var 0) (Syn.shift C)) (heightRowsSyntax (Syn.shift h) (Syn.shift B) (Syn.shift C)
    (Syn.shift D) (Syn.shift T) (Syn.shift U) (var 0)))
theorem row_formula (h B C D T U b u v : PTm n) :
    formula (rowSyntax h B C D T U b u v) = rowLaw h B C D T U b u v := by
  simp [rowSyntax,rowLaw,formula,QuadraticTowerMultiplicationHeight.radicands_formula,
    QuadraticTowerMultiplicationHeight.height_formula]
theorem word_formula (h B C D T U b u : PTm n) :
    formula (wordSyntax h B C D T U b u) = atWord h B C D T U b u := by
  simp [wordSyntax,atWord,formula,row_formula]
theorem height_rows_formula (h B C D T U b : PTm n) :
    formula (heightRowsSyntax h B C D T U b) = atHeight h B C D T U b := by
  simp [heightRowsSyntax,atHeight,formula,word_formula]
theorem local_formula (h B C D T U : PTm n) :
    formula (localSyntax h B C D T U) = localLaw h B C D T U := by
  simp [localSyntax,localLaw,formula,height_rows_formula,BFm.le,le,Syn.shift]

theorem local_at (h B C D T U b u v : PTm n) (hL : Γ ⊢[PRAAx] localLaw h B C D T U)
    (hb : Γ ⊢[PRAAx] le b B) (hc : Γ ⊢[PRAAx] le b C)
    (hu : Γ ⊢[PRAAx] lt u (horizon h b)) (hv : Γ ⊢[PRAAx] lt v (horizon h b))
    (hD : Γ ⊢[PRAAx] radicandsHeight D h b)
    (hA : Γ ⊢[PRAAx] arrayHeight h (word h b u) b)
    (hE : Γ ⊢[PRAAx] arrayHeight h (word h b v) b) : Γ ⊢[PRAAx]
    lookup h B T (word h b u) (word h b v) ≐ lookup h C U (word h b u) (word h b v) := by
  have bg : Γ ⊢[PRAAx] lt b (succ B) ⟶ le b C ⟶ atHeight h B C D T U b := by
    simpa [localLaw] using hL.allE b
  have heightRule := Prf.impE (Prf.impE bg ((succ_monus_succ _ _).eqTrans hb)) hc
  have ug : Γ ⊢[PRAAx] lt u (horizon h b) ⟶ atWord h B C D T U b u := by
    simpa [atHeight] using heightRule.allE u
  have vg : Γ ⊢[PRAAx] lt v (horizon h b) ⟶ rowLaw h B C D T U b u v := by
    simpa [atWord] using (Prf.impE ug hu).allE v
  exact .impE (.impE (.impE (.impE vg hv) hD) hA) hE

theorem restored_values (h A b : PTm n) (ha : Γ ⊢[PRAAx] arrayHeight h A b) : Γ ⊢[PRAAx]
    QuadraticTowerCoefficientArithmetic.equalValues h (QuadraticTowerArrayCodec.restored h A b) A := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] arrayHeight (Syn.shift h) (Syn.shift A) (Syn.shift b) := by
    simpa only [Fm.shift,QuadraticTowerArrayCodec.subst_arrayHeight,Syn.shift] using ha.shift
  refine .allI (.impI ?_)
  simpa only [Syn.shift,QuadraticTowerCoefficients.subst_width,QuadraticTowerArrayCodec.subst_restored] using
    QuadraticTowerArrayCodec.restored_value (Syn.shift h) (Syn.shift A) (Syn.shift b) (var 0) hs.wk Prf.hyp0

theorem lookup_coherent (h B C D T U b A E : PTm n)
    (hL : Γ ⊢[PRAAx] localLaw h B C D T U)
    (hb : Γ ⊢[PRAAx] le b B) (hc : Γ ⊢[PRAAx] le b C)
    (hD : Γ ⊢[PRAAx] radicandsHeight D h b)
    (ha : Γ ⊢[PRAAx] arrayHeight h A b) (he : Γ ⊢[PRAAx] arrayHeight h E b) : Γ ⊢[PRAAx]
    lookup h B T A E ≐ lookup h C U A E := by
  have aw := QuadraticTowerMultiplicationHeight.restored_height h A b b ha (le_refl _)
  have ew := QuadraticTowerMultiplicationHeight.restored_height h E b b he (le_refl _)
  have middle := local_at h B C D T U b (code h A b) (code h E b) hL hb hc
    (QuadraticTowerArrayCodec.code_bound h A b ha) (QuadraticTowerArrayCodec.code_bound h E b he) hD aw ew
  have av := restored_values h A b ha
  have ev := restored_values h E b he
  exact (QuadraticTowerOperandProperness.lookup_proper h B T _ A _ E av ev).eqSymm.eqTrans
    (middle.eqTrans (QuadraticTowerOperandProperness.lookup_proper h C U _ A _ E av ev))

theorem lookup_congr {h h' B B' T T' A A' E E' : PTm n}
    (hh : Γ ⊢[PRAAx] h ≐ h') (hb : Γ ⊢[PRAAx] B ≐ B') (ht : Γ ⊢[PRAAx] T ≐ T')
    (ha : Γ ⊢[PRAAx] A ≐ A') (he : Γ ⊢[PRAAx] E ≐ E') : Γ ⊢[PRAAx]
    lookup h B T A E ≐ lookup h' B' T' A' E' := by
  ipra_congr (lookup (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) with [hh, hb, ht, ha, he]

theorem recipe_coherent (h B C D T U b A E : PTm n)
    (hL : Γ ⊢[PRAAx] localLaw h (budget h B D) (budget h C D) D T U)
    (hT : Γ ⊢[PRAAx] QuadraticTowerMultiplicationHeight.localLaw h (budget h B D) D T)
    (hb : Γ ⊢[PRAAx] le b B) (hc : Γ ⊢[PRAAx] le b C)
    (hD : Γ ⊢[PRAAx] radicandsHeight D (succ h) b)
    (ha : Γ ⊢[PRAAx] arrayHeight (succ h) A b) (he : Γ ⊢[PRAAx] arrayHeight (succ h) E b) : Γ ⊢[PRAAx]
    QuadraticTowerMultiplicationTable.recipe h B T D A E ≐
      QuadraticTowerMultiplicationTable.recipe h C U D A E := by
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
  have e0 := QuadraticTowerMultiplicationHeight.left_height h E b he
  have e1 := QuadraticTowerMultiplicationHeight.right_height h E b he
  have ac := lookup_coherent h K J D T U b _ _ hL bK bJ rh a0 e0
  have be := lookup_coherent h K J D T U b _ _ hL bK bJ rh a1 e1
  have ae := lookup_coherent h K J D T U b _ _ hL bK bJ rh a0 e1
  have bc := lookup_coherent h K J D T U b _ _ hL bK bJ rh a1 e0
  let beT := lookup h K T (QuadraticTowerMultiplicationTable.rightHalf h A)
    (QuadraticTowerMultiplicationTable.rightHalf h E)
  have beH : Γ ⊢[PRAAx] arrayHeight h beT g :=
    QuadraticTowerMultiplicationHeight.lookup_height h K D T _ _ b hT bK rh a1 e1
  have dH : Γ ⊢[PRAAx] arrayHeight h (entry D h) g :=
    QuadraticTowerMultiplicationHeight.array_mono h (entry D h) b g
      (QuadraticTowerMultiplicationHeight.radicand_at D (succ h) b h hD (le_refl _)) bg
  have bed := (lookup_coherent h K J D T U g beT (entry D h) hL gK gJ
    (QuadraticTowerMultiplicationHeight.radicands_mono D h b g rh bg) beH dH).eqTrans
      (lookup_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) be (.eqRefl _))
  exact QuadraticTowerCoefficients.append_congr
    (QuadraticTowerCoefficientArithmetic.added_congr (.eqRefl _) ac bed)
    (QuadraticTowerCoefficientArithmetic.added_congr (.eqRefl _) ae bc)

theorem step_lookup_normalized (h B T D A E : PTm n)
    (ha : Γ ⊢[PRAAx] arrayHeight (succ h) A B) (he : Γ ⊢[PRAAx] arrayHeight (succ h) E B) : Γ ⊢[PRAAx]
    lookup (succ h) B (QuadraticTowerMultiplicationTable.step h B T D) A E ≐
      QuadraticTowerMultiplicationTable.recipe h B T D (QuadraticTowerArrayCodec.normalized (succ h) A)
        (QuadraticTowerArrayCodec.normalized (succ h) E) :=
  (QuadraticTowerMultiplicationTable.step_lookup h B T D _
    (QuadraticTowerMultiplicationTable.address_bound _ _ _ _ ha he)).eqTrans
      ((QuadraticTowerMultiplicationTable.row_at_address h B T D A E he).eqTrans
        (QuadraticTowerMultiplicationTable.recipe_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) (.eqRefl _)
          (QuadraticTowerArrayNormalization.restored_normalized _ _ _ ha)
          (QuadraticTowerArrayNormalization.restored_normalized _ _ _ he)))

theorem step_coherent_at (h B C D T U b A E : PTm n)
    (hL : Γ ⊢[PRAAx] localLaw h (budget h B D) (budget h C D) D T U)
    (hT : Γ ⊢[PRAAx] QuadraticTowerMultiplicationHeight.localLaw h (budget h B D) D T)
    (hb : Γ ⊢[PRAAx] le b B) (hc : Γ ⊢[PRAAx] le b C)
    (hD : Γ ⊢[PRAAx] radicandsHeight D (succ h) b)
    (ha : Γ ⊢[PRAAx] arrayHeight (succ h) A b) (he : Γ ⊢[PRAAx] arrayHeight (succ h) E b) : Γ ⊢[PRAAx]
    lookup (succ h) B (QuadraticTowerMultiplicationTable.step h B T D) A E ≐
      lookup (succ h) C (QuadraticTowerMultiplicationTable.step h C U D) A E := by
  have an := QuadraticTowerMultiplicationHeight.array_congr (.eqRefl _)
    (QuadraticTowerArrayNormalization.restored_normalized (succ h) A b ha) (.eqRefl _)
      (QuadraticTowerMultiplicationHeight.restored_height (succ h) A b b ha (le_refl _))
  have en := QuadraticTowerMultiplicationHeight.array_congr (.eqRefl _)
    (QuadraticTowerArrayNormalization.restored_normalized (succ h) E b he) (.eqRefl _)
      (QuadraticTowerMultiplicationHeight.restored_height (succ h) E b b he (le_refl _))
  exact (step_lookup_normalized h B T D A E
    (QuadraticTowerMultiplicationHeight.array_mono _ _ _ _ ha hb)
    (QuadraticTowerMultiplicationHeight.array_mono _ _ _ _ he hb)).eqTrans
      ((recipe_coherent h B C D T U b _ _ hL hT hb hc hD an en).eqTrans
        (step_lookup_normalized h C U D A E
          (QuadraticTowerMultiplicationHeight.array_mono _ _ _ _ ha hc)
          (QuadraticTowerMultiplicationHeight.array_mono _ _ _ _ he hc)).eqSymm)

theorem local_step (h B C D T U : PTm n)
    (hL : Γ ⊢[PRAAx] localLaw h (budget h B D) (budget h C D) D T U)
    (hT : Γ ⊢[PRAAx] QuadraticTowerMultiplicationHeight.localLaw h (budget h B D) D T) : Γ ⊢[PRAAx]
    localLaw (succ h) B C D (QuadraticTowerMultiplicationTable.step h B T D)
      (QuadraticTowerMultiplicationTable.step h C U D) := by
  have ls : ((Γ.map Fm.shift).map Fm.shift).map Fm.shift ⊢[PRAAx]
      localLaw (Syn.shift (Syn.shift (Syn.shift h)))
        (budget (Syn.shift (Syn.shift (Syn.shift h))) (Syn.shift (Syn.shift (Syn.shift B))) (Syn.shift (Syn.shift (Syn.shift D))))
        (budget (Syn.shift (Syn.shift (Syn.shift h))) (Syn.shift (Syn.shift (Syn.shift C))) (Syn.shift (Syn.shift (Syn.shift D))))
        (Syn.shift (Syn.shift (Syn.shift D))) (Syn.shift (Syn.shift (Syn.shift T))) (Syn.shift (Syn.shift (Syn.shift U))) := by
    simpa only [Fm.shift,subst_localLaw,QuadraticTowerMultiplicationTable.subst_budget,Syn.shift] using hL.shift.shift.shift
  have ts : ((Γ.map Fm.shift).map Fm.shift).map Fm.shift ⊢[PRAAx]
      QuadraticTowerMultiplicationHeight.localLaw (Syn.shift (Syn.shift (Syn.shift h)))
        (budget (Syn.shift (Syn.shift (Syn.shift h))) (Syn.shift (Syn.shift (Syn.shift B))) (Syn.shift (Syn.shift (Syn.shift D))))
        (Syn.shift (Syn.shift (Syn.shift D))) (Syn.shift (Syn.shift (Syn.shift T))) := by
    simpa only [Fm.shift,QuadraticTowerMultiplicationHeight.subst_localLaw,
      QuadraticTowerMultiplicationTable.subst_budget,Syn.shift] using hT.shift.shift.shift
  refine .allI (.impI (.impI (.allI (.impI (.allI (.impI (.impI (.impI (.impI ?_)))))))))
  let h' := Syn.shift (Syn.shift (Syn.shift h))
  let B' := Syn.shift (Syn.shift (Syn.shift B))
  let C' := Syn.shift (Syn.shift (Syn.shift C))
  let D' := Syn.shift (Syn.shift (Syn.shift D))
  let T' := Syn.shift (Syn.shift (Syn.shift T))
  let U' := Syn.shift (Syn.shift (Syn.shift U))
  let b := (var 2 : PTm (n+3))
  let u := (var 1 : PTm (n+3))
  let v := (var 0 : PTm (n+3))
  let R := horizon (succ h') b
  let Δ := arrayHeight (succ h') (word (succ h') b v) b ::
    arrayHeight (succ h') (word (succ h') b u) b :: radicandsHeight D' (succ h') b ::
    lt v R :: lt u R :: le b C' :: lt b (succ B') :: ((Γ.map Fm.shift).map Fm.shift).map Fm.shift
  have ha : Δ ⊢[PRAAx] arrayHeight (succ h') (word (succ h') b u) b := .hyp (by simp [Δ])
  have he : Δ ⊢[PRAAx] arrayHeight (succ h') (word (succ h') b v) b := Prf.hyp0
  have hd : Δ ⊢[PRAAx] radicandsHeight D' (succ h') b := .hyp (by simp [Δ])
  have hbRange : Δ ⊢[PRAAx] lt b (succ B') := .hyp (by simp [Δ])
  have hb : Δ ⊢[PRAAx] le b B' := (succ_monus_succ _ _).eqSymm.eqTrans hbRange
  have hc : Δ ⊢[PRAAx] le b C' := .hyp (by simp [Δ])
  have lower : Δ ⊢[PRAAx] localLaw h' (budget h' B' D') (budget h' C' D') D' T' U' :=
    ls.wk.wk.wk.wk.wk.wk.wk
  have heightLower : Δ ⊢[PRAAx] QuadraticTowerMultiplicationHeight.localLaw h' (budget h' B' D') D' T' :=
    ts.wk.wk.wk.wk.wk.wk.wk
  simpa [Δ,h',B',C',D',T',U',b,u,v,R,Fm.shift,Syn.shift] using
    step_coherent_at (Γ := Δ) h' B' C' D' T' U' b (word (succ h') b u) (word (succ h') b v)
      lower heightLower hb hc hd ha he

theorem base_lookup_original (B A E : PTm n)
    (ha : Γ ⊢[PRAAx] arrayHeight zero A B) (he : Γ ⊢[PRAAx] arrayHeight zero E B) : Γ ⊢[PRAAx]
    lookup zero B (QuadraticTowerMultiplicationTable.base B) A E ≐
      QuadraticTowerCoefficients.singleton (RationalArithmetic.multiply (entry A zero) (entry E zero)) :=
  (lookup_congr (.eqRefl _) (.eqRefl _) (QuadraticTowerMultiplicationTable.table_zero B zero).eqSymm
    (.eqRefl _) (.eqRefl _)).eqTrans (QuadraticTowerOperandProperness.query_zero_original B zero A E ha he)

theorem base_coherent_at (B C b A E : PTm n) (hb : Γ ⊢[PRAAx] le b B) (hc : Γ ⊢[PRAAx] le b C)
    (ha : Γ ⊢[PRAAx] arrayHeight zero A b) (he : Γ ⊢[PRAAx] arrayHeight zero E b) : Γ ⊢[PRAAx]
    lookup zero B (QuadraticTowerMultiplicationTable.base B) A E ≐
      lookup zero C (QuadraticTowerMultiplicationTable.base C) A E :=
  (base_lookup_original B A E (QuadraticTowerMultiplicationHeight.array_mono _ _ _ _ ha hb)
    (QuadraticTowerMultiplicationHeight.array_mono _ _ _ _ he hb)).eqTrans
      (base_lookup_original C A E (QuadraticTowerMultiplicationHeight.array_mono _ _ _ _ ha hc)
        (QuadraticTowerMultiplicationHeight.array_mono _ _ _ _ he hc)).eqSymm

theorem local_base (B C D : PTm n) : Γ ⊢[PRAAx]
    localLaw zero B C D (QuadraticTowerMultiplicationTable.base B) (QuadraticTowerMultiplicationTable.base C) := by
  refine .allI (.impI (.impI (.allI (.impI (.allI (.impI (.impI (.impI (.impI ?_)))))))))
  let B' := Syn.shift (Syn.shift (Syn.shift B))
  let C' := Syn.shift (Syn.shift (Syn.shift C))
  let D' := Syn.shift (Syn.shift (Syn.shift D))
  let b := (var 2 : PTm (n+3))
  let u := (var 1 : PTm (n+3))
  let v := (var 0 : PTm (n+3))
  let R := horizon zero b
  let Δ := arrayHeight zero (word zero b v) b :: arrayHeight zero (word zero b u) b ::
    radicandsHeight D' zero b :: lt v R :: lt u R :: le b C' :: lt b (succ B') ::
      ((Γ.map Fm.shift).map Fm.shift).map Fm.shift
  have hbRange : Δ ⊢[PRAAx] lt b (succ B') := .hyp (by simp [Δ])
  have hb : Δ ⊢[PRAAx] le b B' := (succ_monus_succ _ _).eqSymm.eqTrans hbRange
  have hc : Δ ⊢[PRAAx] le b C' := .hyp (by simp [Δ])
  have ha : Δ ⊢[PRAAx] arrayHeight zero (word zero b u) b := .hyp (by simp [Δ])
  have he : Δ ⊢[PRAAx] arrayHeight zero (word zero b v) b := Prf.hyp0
  simpa [Δ,B',C',D',b,u,v,R,Fm.shift,Syn.shift] using
    base_coherent_at (Γ := Δ) B' C' b (word zero b u) (word zero b v) hb hc ha he

theorem local_congr {h h' B B' C C' D D' T T' U U' : PTm n}
    (hh : Γ ⊢[PRAAx] h ≐ h') (hb : Γ ⊢[PRAAx] B ≐ B') (hc : Γ ⊢[PRAAx] C ≐ C')
    (hd : Γ ⊢[PRAAx] D ≐ D') (ht : Γ ⊢[PRAAx] T ≐ T') (hu : Γ ⊢[PRAAx] U ≐ U')
    (hL : Γ ⊢[PRAAx] localLaw h B C D T U) : Γ ⊢[PRAAx] localLaw h' B' C' D' T' U' := by
  have p := Prf.eqSubst (localLaw (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : Fm PTm 6)
    ![h,B,C,D,T,U] ![h',B',C',D',T',U']
      (fun i => by fin_cases i; exact hh; exact hb; exact hc; exact hd; exact ht; exact hu) (by simpa using hL)
  simpa using p

open QuadraticTowerMultiplicationHeight (cap state)

def forwardLaw (H B C D t : PTm n) : Fm PTm n := le t H ⟶
  localLaw t (cap H B t D) (cap H C t D) D (state H B t D) (state H C t D)
def forwardSyntax (H B C D t : PTm n) : BFm n := .imp (.le t H)
  (localSyntax t (cap H B t D) (cap H C t D) D (state H B t D) (state H C t D))
ipra_subst forwardLaw
theorem forward_formula (H B C D t : PTm n) : formula (forwardSyntax H B C D t) = forwardLaw H B C D t := by
  simp [forwardSyntax,forwardLaw,formula,local_formula,BFm.le,le]

theorem forward_zero (H B C D : PTm n) : Γ ⊢[PRAAx] forwardLaw H B C D zero :=
  .impI (local_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (QuadraticTowerMultiplicationHeight.state_zero H B D).wk.eqSymm
    (QuadraticTowerMultiplicationHeight.state_zero H C D).wk.eqSymm (local_base _ _ D))

theorem forward_step (H B C D t : PTm n) (ih : Γ ⊢[PRAAx] forwardLaw H B C D t) :
    Γ ⊢[PRAAx] forwardLaw H B C D (succ t) := by
  refine .impI ?_
  let Δ := le (succ t) H :: Γ
  have ht : Δ ⊢[PRAAx] lt t H := Prf.hyp0
  have tle : Δ ⊢[PRAAx] le t H := le_trans (le_succ_self t) ht
  have previous : Δ ⊢[PRAAx]
      localLaw t (cap H B t D) (cap H C t D) D (state H B t D) (state H C t D) := .impE ih.wk tle
  have bLink := QuadraticTowerMultiplicationHeight.cap_link H B t D ht
  have cLink := QuadraticTowerMultiplicationHeight.cap_link H C t D ht
  have adjusted : Δ ⊢[PRAAx] localLaw t (budget t (cap H B (succ t) D) D)
      (budget t (cap H C (succ t) D) D) D (state H B t D) (state H C t D) :=
    local_congr (.eqRefl _) bLink cLink (.eqRefl _) (.eqRefl _) (.eqRefl _) previous
  have heightGate : Δ ⊢[PRAAx] QuadraticTowerMultiplicationHeight.forwardLaw H B D t := by
    simpa only [QuadraticTowerMultiplicationHeight.forward_formula,
      QuadraticTowerMultiplicationHeight.subst_forwardLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
        (QuadraticTowerMultiplicationHeight.forward_all (Γ := Δ) H B D).allE t
  have heightPrevious : Δ ⊢[PRAAx]
      QuadraticTowerMultiplicationHeight.localLaw t (cap H B t D) D (state H B t D) := .impE heightGate tle
  have heightAdjusted := QuadraticTowerMultiplicationHeight.local_congr (.eqRefl _) bLink
    (.eqRefl _) (.eqRefl _) heightPrevious
  have next := local_step t (cap H B (succ t) D) (cap H C (succ t) D) D (state H B t D) (state H C t D)
    adjusted heightAdjusted
  exact local_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (QuadraticTowerMultiplicationHeight.state_succ H B t D).eqSymm
    (QuadraticTowerMultiplicationHeight.state_succ H C t D).eqSymm next

/-- One fixed bounded Boolean formula compares two actual forward tables.
Only their shared forward counter is the induction variable. -/
theorem forward_all (H B C D : PTm n) : Γ ⊢[PRAAx] .all
    (formula (forwardSyntax (Syn.shift H) (Syn.shift B) (Syn.shift C) (Syn.shift D) (var 0))) := by
  refine Foundations.BoundedSyntaxInduction.induction_of_formula _ (forward_formula _ _ _ _ _) ?_ ?_
  · simpa only [subst_forwardLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      forward_zero (Γ := Γ) H B C D
  · simpa only [subst_forwardLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift] using
      forward_step (Syn.shift H) (Syn.shift B) (Syn.shift C) (Syn.shift D) (var 0) (Prf.hyp0 (Γ := Γ.map Fm.shift))

theorem table_coherence (h B C D : PTm n) : Γ ⊢[PRAAx] localLaw h B C D
    (QuadraticTowerMultiplicationTable.table h B D) (QuadraticTowerMultiplicationTable.table h C D) := by
  have gate : Γ ⊢[PRAAx] forwardLaw h B C D h := by
    simpa only [forward_formula,subst_forwardLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      (forward_all (Γ := Γ) h B C D).allE h
  have terminal : Γ ⊢[PRAAx] localLaw h (cap h B h D) (cap h C h D) D (state h B h D) (state h C h D) :=
    .impE gate (le_refl h)
  exact local_congr (.eqRefl _)
    (Foundations.BackwardDemand.horizon_final QuadraticTowerMultiplicationTable.demandF h B D)
    (Foundations.BackwardDemand.horizon_final QuadraticTowerMultiplicationTable.demandF h C D)
    (.eqRefl _) (.eqRefl _) (.eqRefl _) terminal

theorem query_cap_independent (h B C D A E b : PTm n)
    (hb : Γ ⊢[PRAAx] le b B) (hc : Γ ⊢[PRAAx] le b C)
    (hD : Γ ⊢[PRAAx] radicandsHeight D h b)
    (ha : Γ ⊢[PRAAx] arrayHeight h A b) (he : Γ ⊢[PRAAx] arrayHeight h E b) : Γ ⊢[PRAAx]
    QuadraticTowerMultiplicationTable.query h B D A E ≐ QuadraticTowerMultiplicationTable.query h C D A E :=
  lookup_coherent h B C D _ _ b A E (table_coherence h B C D) hb hc hD ha he

theorem query_values_independent_caps (h B C D A A' E E' b : PTm n)
    (hb : Γ ⊢[PRAAx] le b B) (hc : Γ ⊢[PRAAx] le b C)
    (hD : Γ ⊢[PRAAx] radicandsHeight D h b)
    (ha : Γ ⊢[PRAAx] arrayHeight h A b) (he : Γ ⊢[PRAAx] arrayHeight h E b)
    (hA : Γ ⊢[PRAAx] QuadraticTowerCoefficientArithmetic.equalValues h A A')
    (hE : Γ ⊢[PRAAx] QuadraticTowerCoefficientArithmetic.equalValues h E E') : Γ ⊢[PRAAx]
    QuadraticTowerMultiplicationTable.query h B D A E ≐ QuadraticTowerMultiplicationTable.query h C D A' E' :=
  (query_cap_independent h B C D A E b hb hc hD ha he).eqTrans
    (QuadraticTowerOperandProperness.query_operands_proper h C D A A' E E' hA hE)

theorem returned_cap_independent (h B C D A E b : PTm n)
    (hb : Γ ⊢[PRAAx] le b B) (hc : Γ ⊢[PRAAx] le b C)
    (hD : Γ ⊢[PRAAx] radicandsHeight D h b)
    (ha : Γ ⊢[PRAAx] arrayHeight h A b) (he : Γ ⊢[PRAAx] arrayHeight h E b) : Γ ⊢[PRAAx]
    PTm.app QuadraticTowerMultiplicationTable.queryF ![h,B,D,A,E] ≐
      PTm.app QuadraticTowerMultiplicationTable.queryF ![h,C,D,A,E] :=
  (QuadraticTowerMultiplicationTable.query_program_at _ _ _ _ _).eqTrans
    ((query_cap_independent h B C D A E b hb hc hD ha he).eqTrans
      (QuadraticTowerMultiplicationTable.query_program_at _ _ _ _ _).eqSymm)

theorem actual_independent_tables_coherent_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (localLaw (var 0) (var 1) (var 2) (var 3)
      (QuadraticTowerMultiplicationTable.table (var 0) (var 1) (var 3))
      (QuadraticTowerMultiplicationTable.table (var 0) (var 2) (var 3))) :=
  closeUniv 4 (table_coherence _ _ _ _)

theorem actual_paired_forward_coherence_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le (var 4) (var 0) ⟶
      localLaw (var 4) (cap (var 0) (var 1) (var 4) (var 3)) (cap (var 0) (var 2) (var 4) (var 3)) (var 3)
        (state (var 0) (var 1) (var 4) (var 3)) (state (var 0) (var 2) (var 4) (var 3))) := by
  apply closeUniv 5
  have proof : ([] : List (Fm PTm 5)) ⊢[PRAAx] forwardLaw (var 0) (var 1) (var 2) (var 3) (var 4) := by
    simpa only [forward_formula,subst_forwardLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      (forward_all (Γ := []) (var 0 : PTm 5) (var 1) (var 2) (var 3)).allE (var 4)
  exact proof

theorem actual_query_cap_independent_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (le (var 6) (var 1) ⟶ le (var 6) (var 2) ⟶ radicandsHeight (var 3) (var 0) (var 6) ⟶
      arrayHeight (var 0) (var 4) (var 6) ⟶ arrayHeight (var 0) (var 5) (var 6) ⟶
        QuadraticTowerMultiplicationTable.query (var 0) (var 1) (var 3) (var 4) (var 5) ≐
          QuadraticTowerMultiplicationTable.query (var 0) (var 2) (var 3) (var 4) (var 5)) :=
  closeUniv 7 (.impI (.impI (.impI (.impI (.impI (query_cap_independent _ _ _ _ _ _ (var 6)
    (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp))))))))

theorem actual_query_values_independent_caps_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (le (var 8) (var 1) ⟶ le (var 8) (var 2) ⟶ radicandsHeight (var 3) (var 0) (var 8) ⟶
      arrayHeight (var 0) (var 4) (var 8) ⟶ arrayHeight (var 0) (var 6) (var 8) ⟶
        QuadraticTowerCoefficientArithmetic.equalValues (var 0) (var 4) (var 5) ⟶
          QuadraticTowerCoefficientArithmetic.equalValues (var 0) (var 6) (var 7) ⟶
            QuadraticTowerMultiplicationTable.query (var 0) (var 1) (var 3) (var 4) (var 6) ≐
              QuadraticTowerMultiplicationTable.query (var 0) (var 2) (var 3) (var 5) (var 7)) :=
  closeUniv 9 (.impI (.impI (.impI (.impI (.impI (.impI (.impI (query_values_independent_caps _ _ _ _ _ _ _ _ (var 8)
    (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp))
      (.hyp (by simp)) (.hyp (by simp))))))))))

theorem actual_returned_query_cap_independent_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (le (var 6) (var 1) ⟶ le (var 6) (var 2) ⟶ radicandsHeight (var 3) (var 0) (var 6) ⟶
      arrayHeight (var 0) (var 4) (var 6) ⟶ arrayHeight (var 0) (var 5) (var 6) ⟶
        PTm.app QuadraticTowerMultiplicationTable.queryF ![var 0,var 1,var 3,var 4,var 5] ≐
          PTm.app QuadraticTowerMultiplicationTable.queryF ![var 0,var 2,var 3,var 4,var 5]) :=
  closeUniv 7 (.impI (.impI (.impI (.impI (.impI (returned_cap_independent _ _ _ _ _ _ (var 6)
    (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp))))))))

end LeanProofs.IPRA.Algebra.QuadraticTowerMultiplicationCoherence
