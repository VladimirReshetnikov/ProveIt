import ZFCinPA.LGlue1

set_option autoImplicit false
noncomputable section

/-!
# The glue, internally: `relativize` against `envForm`

For every formula code `q` whose free variables lie below `j`,
`𝗭𝗙 ⊢ ∀t (¬M_j t ∨ (q^L ↔ envForm 0 q (t)))` (`glue`), by induction on `q`
through `free`, compiling the step templates of `LGlueT2`.

This file first records that `envForm`'s output has no free variables
(`shift_envForm`): every clause is a translated template body over
shift-fixed placeholders.
-/

namespace LeanProofs.ZFCinPA.LGlue2

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LO.FirstOrder.SetTheory Entailment
open LeanProofs.ZFCinPA LeanProofs.ZFCinPA.SetPlaceholders LeanProofs.ZFCinPA.LTemplate
open LeanProofs.ZFCinPA.LInvariant LeanProofs.ZFCinPA.EnvTransform LeanProofs.ZFCinPA.LDriverBase
open LeanProofs.ZFCinPA.LStepAnd
open LeanProofs.ZFCinPA.LGlueT LeanProofs.ZFCinPA.LMatch LeanProofs.ZFCinPA.LGlue1
open LeanProofs.ZFCinPA.NumeralOmega (numChainQ numChainQ_shift)
open scoped LO.FirstOrder.Arithmetic

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## `envForm` is shift-fixed -/

theorem shiftT_val {n : ℕ} (φ : SF V n) : φ.shift.val = shift ℒₛₑₜ φ.val := rfl

theorem shift_translate6 (Ks : (i : Fin 6) → SF V (ar6 i)) (hKs : ∀ i, (Ks i).shift = Ks i)
    (σ : Sentence LStepAnd.L6) {n : ℕ} :
    (translateFormula Ks (Rewriting.emb σ : Semiproposition LStepAnd.L6 0)).shift =
      translateFormula Ks (Rewriting.emb σ) := by
  rw [← translateFormula_shift Ks hKs]
  congr 1
  rw [Rewriting.shift, ← TransitiveRewriting.comp_app, Rew.shift_comp_emb]

theorem shift_translate6₁ (Ks : (i : Fin 6) → SF V (ar6 i)) (hKs : ∀ i, (Ks i).shift = Ks i)
    (σ : Semisentence LStepAnd.L6 1) :
    (translateFormula Ks (Rewriting.emb σ : Semiproposition LStepAnd.L6 1)).shift =
      translateFormula Ks (Rewriting.emb σ) := by
  rw [← translateFormula_shift Ks hKs]
  congr 1
  rw [Rewriting.shift, ← TransitiveRewriting.comp_app, Rew.shift_comp_emb]

theorem K6_shift (a : SF V 1) (ha : a.shift = a) (b : SF V 1) (hb : b.shift = b) :
    ∀ i, (K6 a ⊤ b ⊤ ⊤ ⊤ i).shift = K6 a ⊤ b ⊤ ⊤ ⊤ i := by
  intro i
  match i with
  | ⟨0, _⟩ => exact ha
  | ⟨1, _⟩ => simp [K6]
  | ⟨2, _⟩ => exact hb
  | ⟨3, _⟩ => simp [K6]
  | ⟨4, _⟩ => simp [K6]
  | ⟨5, _⟩ => simp [K6]

theorem atomT_shift (isEq : Bool) (a b : V) :
    (AtomT isEq (numChainQ a) (numChainQ b)).shift = AtomT isEq (numChainQ a) (numChainQ b) := by
  unfold AtomT
  exact shift_translate6₁ _ (K6_shift _ (numChainQ_shiftT a) _ (numChainQ_shiftT b)) _

theorem allT_shift (P : SF V 1) (hP : P.shift = P) : (AllT P).shift = AllT P := by
  unfold AllT
  exact shift_translate6₁ _ (K6_shift _ hP _ (by simp)) _

theorem exT_shift (P : SF V 1) (hP : P.shift = P) : (ExT P).shift = ExT P := by
  unfold ExT
  exact shift_translate6₁ _ (K6_shift _ hP _ (by simp)) _

/-- **`envForm` has no free variables.** -/
theorem shift_envForm {n p : V} (hp : IsSemiformula ℒₛₑₜ n p) :
    shift ℒₛₑₜ (envForm n p) = envForm n p := by
  refine IsSemiformula.sigma1_structural_induction (L := ℒₛₑₜ)
    (P := fun n p ↦ shift ℒₛₑₜ (envForm n p) = envForm n p) (by definability)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · intro n k R v hR hv
    obtain ⟨rfl, hR01⟩ := LDriver.isRel_set hR
    rw [envForm_rel hR hv.isUTerm, atomOf]
    rcases hR01 with rfl | rfl
    · rw [← LDriver.atomT_val_eq, ← shiftT_val, atomT_shift]
    · rw [← LDriver.atomT_val_mem _ _ 1 _root_.one_ne_zero, ← shiftT_val,
        atomT_shift]
  · intro n k R v hR hv
    obtain ⟨rfl, hR01⟩ := LDriver.isRel_set hR
    rw [envForm_nrel hR hv.isUTerm, atomOf]
    rcases hR01 with rfl | rfl
    · rw [← LDriver.atomT_val_eq, ← Bootstrapping.Semiformula.val_neg,
        ← shiftT_val, Bootstrapping.Semiformula.shift_neg, atomT_shift]
    · rw [← LDriver.atomT_val_mem _ _ 1 _root_.one_ne_zero, ← Bootstrapping.Semiformula.val_neg,
        ← shiftT_val, Bootstrapping.Semiformula.shift_neg, atomT_shift]
  · intro n
    simp
  · intro n
    simp
  · intro n p q hp hq ihp ihq
    rw [envForm_and hp.isUFormula hq.isUFormula,
      shift_and (isSemiformula_envForm hp).isUFormula (isSemiformula_envForm hq).isUFormula, ihp, ihq]
  · intro n p q hp hq ihp ihq
    rw [envForm_or hp.isUFormula hq.isUFormula,
      shift_or (isSemiformula_envForm hp).isUFormula (isSemiformula_envForm hq).isUFormula, ihp, ihq]
  · intro n p hp ih
    let P : SF V 1 := LDriver.envFormT (n + 1) hp
    have hP : P.shift = P := Bootstrapping.Semiformula.ext ih
    have h := congrArg Bootstrapping.Semiformula.val (allT_shift P hP)
    rw [shiftT_val, LDriver.allT_val] at h
    rw [envForm_all hp.isUFormula]
    exact h
  · intro n p hp ih
    let P : SF V 1 := LDriver.envFormT (n + 1) hp
    have hP : P.shift = P := Bootstrapping.Semiformula.ext ih
    have h := congrArg Bootstrapping.Semiformula.val (exT_shift P hP)
    rw [shiftT_val, LDriver.exT_val] at h
    rw [envForm_exs hp.isUFormula]
    exact h

/-! ## Closed forms of the glue steps -/

open LeanProofs.ZFCinPA.LGlueT2

/-- The glue statement for typed `M`, `R`, `E`. -/
def GF (M R E : SF V 1) : Bootstrapping.Formula V ℒₛₑₜ := ∀⁰ (∼M ⋎ (R 🡘 E))

/-- `z = y` inside `∀y ∀t ∃t₁ ∃z`. -/
def eqT4 : SF V 4 :=
  (⌜eq2S⌝ : SF V 2).subst
    (fun i ↦ translateTerm (V := V) (Rew.emb ((![#0, #3] : Fin 2 → Semiterm GL Empty 4) i)))

/-- `t = econs z t₁` inside `∀y ∀t ∃t₁ ∃z`. -/
def econsT4 : SF V 4 :=
  (⌜econsS⌝ : SF V 3).subst
    (fun i ↦ translateTerm (V := V) (Rew.emb ((![#2, #0, #1] : Fin 3 → Semiterm GL Empty 4) i)))

/-- The freed premise's matching clause, at level two (`t = #0`, `y = #1`). -/
def MP2 (M : SF V 1) : SF V 2 :=
  ∃⁰ ∃⁰ (eqT4 ⋏ (econsT4 ⋏ M.subst (fun _ ↦ Bootstrapping.Semiterm.bvar 1)))

/-- The body of the quantifier premise, at level one (`y = #0`). -/
def QX (M R E : SF V 1) : SF V 1 :=
  ∀⁰ (∼MP2 M ⋎ (R.subst (fun _ ↦ Bootstrapping.Semiterm.bvar 1) 🡘
    E.subst (fun _ ↦ Bootstrapping.Semiterm.bvar 0)))

/-- `relativize`'s universal clause. -/
def RAllT (R : SF V 1) : SF V 1 :=
  ∀⁰ (∼(⌜ConstructibleInterpretation.domL⌝ : SF V 1).subst (fun _ ↦ Bootstrapping.Semiterm.bvar 0) ⋎
    R.subst (fun _ ↦ Bootstrapping.Semiterm.bvar 0))

/-- `envForm`'s universal clause. -/
def EAllT (E : SF V 1) : SF V 1 :=
  ∀⁰ ∀⁰ (∼(⌜econsS⌝ : SF V 3) ⋎ (∼(⌜domYS⌝ : SF V 3) ⋎ E.subst (fun _ ↦ Bootstrapping.Semiterm.bvar 0)))

section Tr

variable (Ks : (i : Fin 8) → SF V (arG i))

theorem tr_gS (i r e : Fin 8) :
    translateFormula Ks (Rewriting.emb (gS i r e)) = GF (Ks i) (Ks r) (Ks e) := by
  simp [gS, GF, G, translateFormula, LogicalConnective.iff, Bootstrapping.Semiformula.imp_def]

theorem tr_qHyp : translateFormula Ks (Rewriting.emb qHyp) = ∀⁰ QX (Ks 0) (Ks 1) (Ks 2) := by
  simp [qHyp, mp2, G, translateFormula, QX, MP2, eqT4, econsT4, LogicalConnective.iff,
    Bootstrapping.Semiformula.imp_def]

theorem tr_relAll : translateFormula Ks (Rewriting.emb relAll) = RAllT (Ks 1) := by
  simp [relAll, G, translateFormula, RAllT]

theorem tr_envAll : translateFormula Ks (Rewriting.emb envAll) = EAllT (Ks 2) := by
  simp [envAll, G, translateFormula, EAllT]

end Tr

/-- A formula read at level one (its code does not change). -/
def lift1 (φ : Bootstrapping.Formula V ℒₛₑₜ) : SF V 1 :=
  ⟨φ.val, by simpa using isSemiformula_of_le φ.isSemiformula (show ((0 : ℕ) : V) ≤ ((1 : ℕ) : V) by simp)⟩

abbrev W4 : Bootstrapping.SemitermVec V ℒₛₑₜ 4 3 :=
  (Bootstrapping.SemitermVec.q ![Bootstrapping.Semiterm.fvar 0]).q.q

theorem q_one {k n : ℕ} (w : Bootstrapping.SemitermVec V ℒₛₑₜ (k + 1) n) :
    w.q 1 = (w 0).bShift := rfl

theorem q_two {k n : ℕ} (w : Bootstrapping.SemitermVec V ℒₛₑₜ (k + 2) n) :
    w.q 2 = (w 1).bShift := rfl

theorem W4_0 : (W4 (V := V)) 0 = Bootstrapping.Semiterm.bvar 0 := rfl

theorem W4_1 : (W4 (V := V)) 1 = Bootstrapping.Semiterm.bvar 1 := by
  show Bootstrapping.Semiterm.bShift
    ((Bootstrapping.SemitermVec.q ![Bootstrapping.Semiterm.fvar 0]).q 0) = _
  simp

theorem W4_2 : (W4 (V := V)) 2 = Bootstrapping.Semiterm.bvar 2 := by
  show Bootstrapping.Semiterm.bShift
    ((Bootstrapping.SemitermVec.q ![Bootstrapping.Semiterm.fvar 0]).q (Fin.succ 0)) = _
  simp [q_one]

theorem W4_3 : (W4 (V := V)) 3 = Bootstrapping.Semiterm.fvar 0 := by
  show Bootstrapping.Semiterm.bShift
    ((Bootstrapping.SemitermVec.q ![Bootstrapping.Semiterm.fvar 0]).q (Fin.succ 1)) = _
  simp [q_one, q_two]

theorem eqT4_eq : eqT4 (V := V) =
    Bootstrapping.Semiformula.rel (Language.Eq.eq : (ℒₛₑₜ).Rel 2)
      ![Bootstrapping.Semiterm.bvar 0, Bootstrapping.Semiterm.bvar 3] := by
  apply Bootstrapping.Semiformula.ext
  simp [eqT4, eq2S, Semiformula.Operator.eq_def, LO.FirstOrder.Sentence.typed_quote_def,
    Bootstrapping.SemitermVec.val, Matrix.vecHead, Matrix.vecTail]
  done

theorem leaf_eq :
    (eqT4 (V := V)).shift.subst W4 = zT.subst (fun _ ↦ Bootstrapping.Semiterm.bvar 0) := by
  rw [eqT4_eq]
  simp [zT, W4_0, W4_3]
  done

theorem leaf_econs : (econsT4 (V := V)).shift.subst W4 = econsT3 := by
  simp [econsT4, econsT3, shift_quoteT, Bootstrapping.Semiformula.shift_substs,
    Bootstrapping.Semiformula.substs_substs]
  congr 1
  funext i
  match i with
  | 0 => simp [Matrix.vecHead, Matrix.vecTail, translateTerm, W4_2]
  | 1 => simp [Matrix.vecHead, Matrix.vecTail, translateTerm, W4_0]
  | 2 => simp [Matrix.vecHead, Matrix.vecTail, translateTerm, W4_1]

theorem QX_free (M R E : SF V 1) (hE : E.shift = E) :
    (QX M R E).free = GF (MpT M.shift zT) (lift1 R.free) E := by
  simp [QX, GF, MP2, MpT, Bootstrapping.Semiformula.free, Bootstrapping.Semiformula.shift_substs,
    Bootstrapping.Semiformula.substs_substs, hE, LogicalConnective.iff,
    Bootstrapping.Semiformula.imp_def, leaf_eq, leaf_econs]
  refine ⟨?_, ?_⟩
  · congr 1
    funext i
    match i with
    | 0 => exact W4_1
  · apply Bootstrapping.Semiformula.ext
    simp [lift1, q_one, Bootstrapping.SemitermVec.val, Matrix.vecHead, Matrix.vecTail]

end LeanProofs.ZFCinPA.LGlue2
