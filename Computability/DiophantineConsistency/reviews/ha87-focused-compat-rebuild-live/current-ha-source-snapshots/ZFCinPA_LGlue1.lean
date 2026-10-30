import ZFCinPA.LGlueT2

set_option autoImplicit false
noncomputable section

/-!
# The glue, internally: functional matching environments and slots

The glue templates of `LGlueT`, compiled at internal codes, and the first two
internal inductions over the number `j` of matched free variables:

* `fun_MT`: `𝗭𝗙 ⊢ ∀t (M_j t → t is functional)`;
* `slot_MT`: for `a < j`, `𝗭𝗙 ⊢ ∀t (M_j t → ∀n (Num_a n → ∃x (x = &a ∧ ⟨n, x⟩ ∈ t)))`.
-/

namespace LeanProofs.ZFCinPA.LGlue1

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LO.FirstOrder.SetTheory Entailment
open LeanProofs.ZFCinPA LeanProofs.ZFCinPA.SetPlaceholders LeanProofs.ZFCinPA.LTemplate
open LeanProofs.ZFCinPA.LInvariant LeanProofs.ZFCinPA.EnvTransform LeanProofs.ZFCinPA.LDriverBase
open LeanProofs.ZFCinPA.LGlueT LeanProofs.ZFCinPA.LMatch
open scoped LO.FirstOrder.Arithmetic

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- An eight-slot placeholder tuple over `GL`. -/
def K8 (a b c d e f g h : SF V 1) : (i : Fin 8) → SF V (arG i) :=
  fun i ↦ (![a, b, c, d, e, f, g, h] : Fin 8 → SF V 1) i

section Translation

variable (Ks : (i : Fin 8) → SF V (arG i))

@[simp] theorem trG {n : ℕ} (i : Fin 8) (v : Fin 1 → SyntacticSemiterm GL n) :
    translateFormula Ks (@Semiformula.rel GL ℕ n 1 (placeholderRel i) v) =
      (Ks i).subst (fun j ↦ translateTerm (v j)) := rfl

@[simp] theorem trnG {n : ℕ} (i : Fin 8) (v : Fin 1 → SyntacticSemiterm GL n) :
    translateFormula Ks (@Semiformula.nrel GL ℕ n 1 (placeholderRel i) v) =
      ∼(Ks i).subst (fun j ↦ translateTerm (v j)) := rfl

@[simp] theorem tr_liftG {n : ℕ} (σ : SetTheorySemisentence n) :
    translateFormula Ks (Rewriting.emb (lift σ : Semisentence GL n)) = ⌜σ⌝ :=
  translateFormula_emb_liftSet Ks σ

@[simp] theorem tr_liftG_subst {n m : ℕ} (σ : SetTheorySemisentence n)
    (v : Fin n → Semiterm GL Empty m) :
    translateFormula Ks (Rewriting.emb ((lift σ : Semisentence GL n) ⇜ v)) =
      (⌜σ⌝ : SF V n).subst (fun i ↦ translateTerm (Rew.emb (v i))) := by
  rw [Rewriting.emb_subst_eq_subst_emb]
  exact (translateFormula_subst Ks _ _).trans (by rw [tr_liftG])

theorem tr_funM (i : Fin 8) :
    translateFormula Ks (Rewriting.emb (funM i)) = ∀⁰ (∼(Ks i) ⋎ (⌜funcS⌝ : SF V 1)) := by
  simp [funM, G, translateFormula]

/-- The econs piece of the matching clause, as translated. -/
def econsT3 : SF V 3 :=
  (⌜econsS⌝ : SF V 3).subst
    (fun i ↦ translateTerm (V := V) (Rew.emb ((![#2, #0, #1] : Fin 3 → Semiterm GL Empty 3) i)))

/-- The translated successor clause of the matching code. -/
def MpT (M Z : SF V 1) : SF V 1 :=
  ∃⁰ ∃⁰ (Z.subst (fun _ ↦ Bootstrapping.Semiterm.bvar 0) ⋏
    (econsT3 ⋏ M.subst (fun _ ↦ Bootstrapping.Semiterm.bvar 1)))

theorem tr_mpDef :
    translateFormula Ks (Rewriting.emb mpDef) = ∀⁰ (Ks 1 🡘 MpT (Ks 0) (Ks 2)) := by
  simp [mpDef, G, translateFormula, MpT, econsT3, LogicalConnective.iff,
    Bootstrapping.Semiformula.imp_def]

end Translation

section Fun

theorem econsT3_val : (econsT3 (V := V)).val = (eT (V := V)).val := by
  unfold econsT3 eT
  congr 2
  funext i
  match i with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl

theorem mpT_val (j : V) : (MpT (MT j).shift zT).val = mVal (j + 1) := by
  rw [mVal_succ]
  simp only [MpT, Bootstrapping.Semiformula.val_exs, Bootstrapping.Semiformula.val_and,
    econsT3_val]
  congr 3
  · exact LDriver.subst_bvar0_val _ _ rfl
  · simp [MT, Bootstrapping.SemitermVec.val, Matrix.vecHead, Matrix.vecTail]

theorem MT_succ (j : V) : MT (j + 1) = MpT (MT j).shift zT :=
  Bootstrapping.Semiformula.ext (mpT_val j).symm

/-- `∀x (A → A)`, i.e. `∀x (¬A ∨ A)`. -/
theorem all_em (A : SF V 1) : (𝗭𝗙 : SetTheory).internalize V ⊢ ∀⁰ (∼A ⋎ A) := by
  rw [← Bootstrapping.Semiformula.imp_def]
  exact Bootstrapping.TProof.all! (by
    simp only [Bootstrapping.Semiformula.free, Bootstrapping.Semiformula.shift_imp,
      Bootstrapping.Semiformula.substs_imp]
    exact C!_id)

/-- Quotations of semisentences have no free variables. -/
theorem shift_quoteT {n : ℕ} (σ : SetTheorySemisentence n) : (⌜σ⌝ : SF V n).shift = ⌜σ⌝ := by
  apply Bootstrapping.Semiformula.ext
  show shift ℒₛₑₜ (⌜(Rewriting.emb σ : SetTheorySemiproposition n)⌝ : V) = _
  rw [← LO.FirstOrder.Semiformula.quote_shift]
  congr 1
  rw [Rewriting.shift, ← TransitiveRewriting.comp_app, Rew.shift_comp_emb]

theorem funT_shift (M : SF V 1) :
    (∀⁰ (∼M ⋎ (⌜funcS⌝ : SF V 1)) : Bootstrapping.Formula V ℒₛₑₜ).shift =
      ∀⁰ (∼M.shift ⋎ (⌜funcS⌝ : SF V 1)) := by
  simp [shift_quoteT]

theorem tr_andG (Ks : (i : Fin 8) → SF V (arG i)) {n : ℕ} (p q : Semiproposition GL n) :
    translateFormula Ks (p ⋏ q) = translateFormula Ks p ⋏ translateFormula Ks q := rfl

/-- A compiled glue template. -/
theorem compiledG {σ : Sentence GL} (h : templTheory 8 arG ⊢ σ) (Ks : (i : Fin 8) → SF V (arG i)) :
    (𝗭𝗙 : SetTheory).internalize V ⊢ translateFormula Ks (Rewriting.emb σ) :=
  compileT_provable (by decide) Ks h

/-- The statement "matching environments are functional", on codes. -/
def funVal (j : V) : V := ^∀ (neg ℒₛₑₜ (mVal j) ^⋎ (⌜funcS⌝ : SF V 1).val)

theorem funT_val (j : V) : (∀⁰ (∼(MT j) ⋎ (⌜funcS⌝ : SF V 1)) : Bootstrapping.Formula V ℒₛₑₜ).val =
    funVal j := by
  simp [funVal, MT]

/-- **Matching environments are functional**, provably in `𝗭𝗙`, for every `j`. -/
theorem fun_MT (j : V) :
    (𝗭𝗙 : SetTheory).internalize V ⊢ ∀⁰ (∼(MT j) ⋎ (⌜funcS⌝ : SF V 1)) := by
  suffices Provable (𝗭𝗙 : SetTheory) (funVal j) by
    rw [← funT_val] at this
    exact Bootstrapping.tprovable_iff_provable.mpr this
  induction j using ISigma1.sigma1_succ_induction
  · unfold funVal
    definability
  case zero =>
    have h0 : MT (0 : V) = ⌜funcS⌝ := Bootstrapping.Semiformula.ext (by simp [MT, fT])
    rw [← funT_val, h0]
    exact Bootstrapping.tprovable_iff_provable.mp (all_em _)
  case succ j ih =>
    have ih' : (𝗭𝗙 : SetTheory).internalize V ⊢ ∀⁰ (∼(MT j) ⋎ (⌜funcS⌝ : SF V 1)) :=
      Bootstrapping.tprovable_iff_provable.mpr (by rw [funT_val]; exact ih)
    have hsh := Bootstrapping.TProof.shift! ih'
    rw [funT_shift] at hsh
    have hc := compiledG funTemplate_provable (K8 (MT j).shift (MT (j + 1)) zT ⊤ ⊤ ⊤ ⊤ ⊤)
    simp only [funTemplate, LogicalConnective.HomClass.map_imply, LogicalConnective.HomClass.map_and,
      translateFormula_imp, tr_andG, tr_funM, tr_mpDef] at hc
    have hdef : (𝗭𝗙 : SetTheory).internalize V ⊢
        ∀⁰ (MT (j + 1) 🡘 MpT (MT j).shift zT) := by
      rw [← MT_succ]
      exact all_iff_self _
    have := hc ⨀ K!_intro hsh hdef
    rw [← funT_val]
    exact Bootstrapping.tprovable_iff_provable.mp this

end Fun

section Slot

open LeanProofs.ZFCinPA.NumeralOmega (numChainQ numChainQ_zero numChainQ_succ numChainQ_shift numZeroS
  succRelS)

/-- `x = &a`. -/
def xT (a : V) : SF V 1 :=
  Bootstrapping.Semiformula.rel (Language.Eq.eq : (ℒₛₑₜ).Rel 2)
    ![Bootstrapping.Semiterm.bvar 0, Bootstrapping.Semiterm.fvar a]

/-- The translated slot statement. -/
def SlotT (M N X : SF V 1) : Bootstrapping.Formula V ℒₛₑₜ :=
  translateFormula (K8 M N X ⊤ ⊤ ⊤ ⊤ ⊤) (Rewriting.emb (slotS 0 1 2))

theorem tr_slotS (Ks : (i : Fin 8) → SF V (arG i)) (i j k : Fin 8) :
    translateFormula Ks (Rewriting.emb (slotS i j k)) = SlotT (Ks i) (Ks j) (Ks k) := by
  simp [SlotT, slotS, G, translateFormula, K8]

theorem slotT_shift (M N X : SF V 1) : (SlotT M N X).shift = SlotT M.shift N.shift X.shift := by
  simp [SlotT, slotS, G, translateFormula, K8, shift_quoteT, Bootstrapping.Semiformula.shift_substs]
  and_intros
  all_goals
    congr 1
    funext ⟨i, hi⟩
    rcases i with _ | _ | _ | i
    all_goals first
      | rfl
      | simp [Matrix.vecHead, Matrix.vecTail]
      | (exfalso; omega)

theorem xT_shift (a : V) : (xT a).shift = xT (a + 1) := by
  apply Bootstrapping.Semiformula.ext
  simp [xT]

theorem tr_zeroDef (Ks : (i : Fin 8) → SF V (arG i)) (j : Fin 8) :
    translateFormula Ks (Rewriting.emb (zeroDef j)) = ∀⁰ (Ks j 🡘 ⌜numZeroS⌝) := by
  simp [zeroDef, G, translateFormula, LogicalConnective.iff, Bootstrapping.Semiformula.imp_def]

/-- The translated successor-numeral clause. -/
def SuccT (N : SF V 1) : SF V 1 :=
  ∃⁰ (N.subst (fun _ ↦ Bootstrapping.Semiterm.bvar 0) ⋏ (⌜succRelS⌝ : SF V 2).subst
    (fun i ↦ translateTerm (V := V) (Rew.emb ((![#0, #1] : Fin 2 → Semiterm GL Empty 2) i))))

theorem tr_succDef (Ks : (i : Fin 8) → SF V (arG i)) (j j' : Fin 8) :
    translateFormula Ks (Rewriting.emb (succDef j j')) = ∀⁰ (Ks j' 🡘 SuccT (Ks j)) := by
  simp [succDef, G, translateFormula, SuccT, LogicalConnective.iff,
    Bootstrapping.Semiformula.imp_def]

theorem succT_numChain (a : V) : SuccT (numChainQ a) = numChainQ (a + 1) := by
  rw [numChainQ_succ, SuccT]
  congr 2
  apply Bootstrapping.Semiformula.subst_eq_self
  intro i
  match i with
  | 0 => rfl
  | 1 => rfl

theorem tr_natN (Ks : (i : Fin 8) → SF V (arG i)) (j : Fin 8) :
    translateFormula Ks (Rewriting.emb (natN j)) = ∀⁰ (∼Ks j ⋎ ⌜LStepAtom.natP⌝) := by
  simp [natN, G, translateFormula]

theorem numOK_right (a : V) :
    (𝗭𝗙 : SetTheory).internalize V ⊢ ∀⁰ (∼(numChainQ a) ⋎ ⌜LStepAtom.natP⌝) := by
  have h := LNumOK.numOK a
  simp [NumOKT, LStepAtom.numOK₀, LStepAnd.P₀, translateFormula] at h
  exact K!_right h

theorem numChainQ_shiftT (a : V) : (numChainQ a).shift = numChainQ a :=
  Bootstrapping.Semiformula.ext (numChainQ_shift a)

theorem xT_zero : xT (0 : V) = zT := rfl

theorem funShift (j : V) :
    (𝗭𝗙 : SetTheory).internalize V ⊢ ∀⁰ (∼(MT j).shift ⋎ (⌜funcS⌝ : SF V 1)) := by
  have h := Bootstrapping.TProof.shift! (fun_MT j)
  rwa [funT_shift] at h

theorem mpDefT (j : V) :
    (𝗭𝗙 : SetTheory).internalize V ⊢ ∀⁰ (MT (j + 1) 🡘 MpT (MT j).shift zT) := by
  rw [← MT_succ]
  exact all_iff_self _

theorem slot_zero (j : V) :
    (𝗭𝗙 : SetTheory).internalize V ⊢ SlotT (MT (j + 1)) (numChainQ 0) (xT 0) := by
  have hc := compiledG slot0Template_provable
    (K8 (MT j).shift (MT (j + 1)) zT (numChainQ 0) ⊤ ⊤ ⊤ ⊤)
  simp only [slot0Template, LogicalConnective.HomClass.map_imply,
    LogicalConnective.HomClass.map_and, translateFormula_imp, tr_andG, tr_funM, tr_mpDef,
    tr_zeroDef, tr_slotS] at hc
  have hz : (𝗭𝗙 : SetTheory).internalize V ⊢ ∀⁰ (numChainQ (0 : V) 🡘 ⌜numZeroS⌝) := by
    rw [numChainQ_zero]
    exact all_iff_self _
  exact hc ⨀ K!_intro (funShift j) (K!_intro (mpDefT j) hz)

theorem slot_succ (j a : V)
    (h : (𝗭𝗙 : SetTheory).internalize V ⊢ SlotT (MT j) (numChainQ a) (xT a)) :
    (𝗭𝗙 : SetTheory).internalize V ⊢ SlotT (MT (j + 1)) (numChainQ (a + 1)) (xT (a + 1)) := by
  have hc := compiledG slotSTemplate_provable
    (K8 (MT j).shift (MT (j + 1)) zT (numChainQ a) (xT (a + 1)) (numChainQ (a + 1)) ⊤ ⊤)
  simp only [slotSTemplate, LogicalConnective.HomClass.map_imply,
    LogicalConnective.HomClass.map_and, translateFormula_imp, tr_andG, tr_funM, tr_mpDef,
    tr_succDef, tr_natN, tr_slotS] at hc
  have hs := Bootstrapping.TProof.shift! h
  rw [slotT_shift, numChainQ_shiftT, xT_shift] at hs
  have hsd : (𝗭𝗙 : SetTheory).internalize V ⊢
      ∀⁰ (numChainQ (a + 1) 🡘 SuccT (numChainQ a)) := by
    rw [succT_numChain]
    exact all_iff_self _
  exact hc ⨀ K!_intro hs (K!_intro (funShift j) (K!_intro (mpDefT j)
    (K!_intro hsd (numOK_right a))))

/-- The code of `x = &a`: the substitution instance of `x = y` at `#0, &a`. -/
def xVal (a : V) : V := subst ℒₛₑₜ (^#0 ∷ ^&a ∷ 0) (⌜LGlueT2.eq2S⌝ : SF V 2).val

theorem xT_eq (a : V) :
    xT a = (⌜LGlueT2.eq2S⌝ : SF V 2).subst
      ![Bootstrapping.Semiterm.bvar 0, Bootstrapping.Semiterm.fvar a] := by
  simp only [xT, LGlueT2.eq2S, Semiformula.Operator.eq_def]
  apply Bootstrapping.Semiformula.ext
  simp [LO.FirstOrder.Sentence.typed_quote_def, Bootstrapping.SemitermVec.val, Matrix.vecHead,
    Matrix.vecTail]
  done

theorem xT_val (a : V) : (xT a).val = xVal a := by
  rw [xT_eq]
  simp [xVal, Bootstrapping.SemitermVec.val, Matrix.vecHead, Matrix.vecTail]

instance xVal_definable : 𝚺₁-Function₁ (xVal : V → V) := by
  unfold xVal
  definability

/-- The slot statement, on codes. -/
def slotVal (j a : V) : V :=
  LTransVal.transVal (![mVal j, numChainCode a, xVal a, ^⊤, ^⊤, ^⊤, ^⊤, ^⊤] : Fin 8 → V)
    (Rewriting.emb (slotS 0 1 2) : Semiproposition GL 0)

theorem slotT_val (j a : V) : (SlotT (MT j) (numChainQ a) (xT a)).val = slotVal j a := by
  rw [SlotT, LTransVal.val_translateFormula, slotVal]
  congr 1
  funext i
  match i with
  | 0 => rfl
  | 1 => rfl
  | 2 => exact xT_val a
  | 3 => rfl
  | 4 => rfl
  | 5 => rfl
  | 6 => rfl
  | 7 => rfl

instance slotVal_definable : 𝚺₁-Function₂ (slotVal : V → V → V) := by
  have h := LTransVal.transVal_definable (V := V) (k := 8) (arities := arG)
    (Rewriting.emb (slotS 0 1 2) : Semiproposition GL 0)
  refine HierarchySymbol.DefinableFunction.of_eq _ (fun _ ↦ rfl)
    (HierarchySymbol.DefinableFunction.substitution (F := fun vals : Fin 8 → V ↦
      LTransVal.transVal vals (Rewriting.emb (slotS 0 1 2) : Semiproposition GL 0))
    (f := fun i (x : Fin 2 → V) ↦
      (![mVal (x 0), numChainCode (x 1), xVal (x 1), ^⊤, ^⊤, ^⊤, ^⊤, ^⊤] : Fin 8 → V) i) h
    (fun i ↦ ?_))
  match i with
  | 0 => exact HierarchySymbol.DefinableFunction₁.comp (F := mVal) (HierarchySymbol.DefinableFunction.var 0)
  | 1 => exact HierarchySymbol.DefinableFunction₁.comp (F := numChainCode) (HierarchySymbol.DefinableFunction.var 1)
  | 2 => exact HierarchySymbol.DefinableFunction₁.comp (F := xVal) (HierarchySymbol.DefinableFunction.var 1)
  | 3 => exact HierarchySymbol.DefinableFunction.const _
  | 4 => exact HierarchySymbol.DefinableFunction.const _
  | 5 => exact HierarchySymbol.DefinableFunction.const _
  | 6 => exact HierarchySymbol.DefinableFunction.const _
  | 7 => exact HierarchySymbol.DefinableFunction.const _

/-- **A matching environment holds `&a` at the slot of the numeral `a`**, provably in
`𝗭𝗙`, for every `a < j`. -/
theorem slot_MT (j : V) : ∀ a < j,
    (𝗭𝗙 : SetTheory).internalize V ⊢ SlotT (MT j) (numChainQ a) (xT a) := by
  suffices ∀ a < j, Bootstrapping.Provable (𝗭𝗙 : SetTheory) (slotVal j a) by
    intro a ha
    exact Bootstrapping.tprovable_iff_provable.mpr (by rw [slotT_val]; exact this a ha)
  induction j using ISigma1.sigma1_succ_induction
  · apply HierarchySymbol.Definable.ball_lt (HierarchySymbol.DefinableFunction.var 0)
    exact HierarchySymbol.DefinablePred.comp (P := Bootstrapping.Provable (𝗭𝗙 : SetTheory)) (by definability)
      (HierarchySymbol.DefinableFunction₂.comp (F := slotVal)
        (HierarchySymbol.DefinableFunction.var 1) (HierarchySymbol.DefinableFunction.var 0))
  case zero => intro a ha; simp at ha
  case succ j ih =>
    intro a ha
    have key : (𝗭𝗙 : SetTheory).internalize V ⊢ SlotT (MT (j + 1)) (numChainQ a) (xT a) := by
      rcases zero_or_succ a with rfl | ⟨a', rfl⟩
      · exact slot_zero j
      · have ha' : a' < j := by simpa using ha
        exact slot_succ j a' (Bootstrapping.tprovable_iff_provable.mpr
          (by rw [slotT_val]; exact ih a' ha'))
    have := Bootstrapping.tprovable_iff_provable.mp key
    rwa [slotT_val] at this

end Slot

end LeanProofs.ZFCinPA.LGlue1
