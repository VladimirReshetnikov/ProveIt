import ZFCinPA.LSepBase
import ZFCinPA.LFinalRepl

set_option autoImplicit false
noncomputable section

/-!
# The replacement base

For a replacement core `K` (level two) whose free variables lie below `m`,
`𝗭𝗙 ⊢ ∀t (¬(Env t ∧ M_m t) ∨ relativize L (repBodyVal K))` (`repl_base`),
and hence every recognized replacement code has a `𝗭𝗙`-proof of its
relativization (`repl_obligation`).

The core has two bound variables, read by the final replacement template at
`x :: y :: t`. The glue premise is therefore needed at level two:
`∀y ∀x ∀t (¬mp₃(t, x, y) ∨ (R(x, y) ↔ E t))`, where `mp₃` says
`t = x :: y :: t₂` with `t₂` matching. It comes from the glue at `m + 2`
for the core opened twice: `LGlue4.qPremise` at `m + 1` for
`K₁ = subst (openVec 1) (shift K)` (whose free `&0` is `y`), followed by one
more generalization (`QX2_free`).
-/

namespace LeanProofs.ZFCinPA.LReplBase

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA LeanProofs.ZFCinPA.SetPlaceholders LeanProofs.ZFCinPA.LTemplate
open LeanProofs.ZFCinPA.EnvTransform LeanProofs.ZFCinPA.LPieces LeanProofs.ZFCinPA.LInvariant
open LeanProofs.ZFCinPA.LStepAnd LeanProofs.ZFCinPA.LGlueT2 LeanProofs.ZFCinPA.LPeel
open LeanProofs.ZFCinPA.LSepBase
open LeanProofs.ZFCinPA.ConstructibleInterpretation (domL)

local instance : Language.Mem L6 := ⟨Sum.inl Language.Set.Rel.mem⟩

/-- `t = x :: y :: t₂` with `P₀ t₂` (`t = #0`, `x = #1`, `y = #2`). -/
def mp3 : Semisentence L6 3 :=
  ∃⁰ ∃⁰ ((lift eq2S ⇜ ![#0, #3]) ⋏ ((lift econsS ⇜ ![#2, #0, #1]) ⋏
    (∃⁰ ∃⁰ ((lift eq2S ⇜ ![#0, #6]) ⋏ ((lift econsS ⇜ ![#3, #0, #1]) ⋏ (P₀ ⇜ ![#1]))))))

/-- The level-two glue premise: `∀y ∀x ∀t (¬mp₃(t, x, y) ∨ (F₁(x, y) ↔ P₄ t))`. -/
def qHyp2 : Sentence L6 := ∀⁰ ∀⁰ ∀⁰ (∼mp3 ⋎ ((F₁ ⇜ ![#1, #2]) 🡘 (P₄ ⇜ ![#0])))

/-- The relativized hypothesis of replacement over `F₁`:
`∀x (δx → ∃y (δy ∧ F₁(x, y) ∧ ∀y' (δy' → ¬F₁(x, y') ∨ y' = y)))`. -/
def relReplA : Semisentence L6 1 :=
  ∀⁰ (∼(lift domL ⇜ ![#0]) ⋎ (∃⁰ ((lift domL ⇜ ![#0]) ⋏ ((F₁ ⇜ ![#1, #0]) ⋏
    (∀⁰ (∼(lift domL ⇜ ![#0]) ⋎ (∼(F₁ ⇜ ![#2, #0]) ⋎ (lift eq2S ⇜ ![#0, #1]))))))))

/-- The relativized conclusion of replacement over `F₁`:
`∀X (δX → ∃Y (δY ∧ ∀y (δy → (y ∈ Y ↔ ∃x (δx ∧ x ∈ X ∧ F₁(x, y))))))`. -/
def relReplB : Semisentence L6 1 :=
  ∀⁰ (∼(lift domL ⇜ ![#0]) ⋎ (∃⁰ ((lift domL ⇜ ![#0]) ⋏ (∀⁰ (∼(lift domL ⇜ ![#0]) ⋎
    ((lift zyS ⇜ ![#0, #1]) 🡘 (∃⁰ ((lift domL ⇜ ![#0]) ⋏
      ((lift zyS ⇜ ![#0, #3]) ⋏ (F₁ ⇜ ![#0, #1]))))))))))

/-- **The replacement combination.** -/
def replComb : Sentence L6 :=
  ((totS F₅ ⋏ reflS P₄ F₅) ⋏ qHyp2) 🡒 ∀⁰ (∼(lift envS ⋏ P₀) ⋎ (∼relReplA ⋎ relReplB))

theorem replComb_provable : templTheory 6 ar6 ⊢ replComb := by
  apply templ_provable
  intro M _ _ s _ _ hT
  haveI : M↓[ℒₛₑₜ] ⊧* (𝗭𝗙 : SetTheory) := pure_models (k := 6) (arities := ar6)
  have hR := ConstructibleInterpretation.regular_of_modelsZF (V := M)
  set H := ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M)
  set hP := ConstructibleInterpretation.power_of_modelsZF (V := M)
  have hrep := models_of_provable hT LFinalRepl.replTemplate_provable
  simp only [LFinalRepl.replTemplate, Semantics.Imp.models_imply] at hrep
  simp only [replComb, Semantics.Imp.models_imply, Semantics.And.models_and]
  rintro ⟨hinv, hq⟩
  have hS := hrep (Semantics.And.models_and.mpr hinv)
  rw [LFinalRepl.models_replEnvS] at hS
  simp [models_iff, qHyp2, mp3, P₀, F₁, P₄, eq2S, Semiformula.Operator.eq_def] at hq
  simp [models_iff, relReplA, relReplB, envS, zyS, eq2S, P₀, F₁, Semiformula.Operator.eq_def,
    ConstructibleInterpretation.eval_domL H hP, eval_stageP (H := H) (hP := hP),
    eval_envP (H := H)]
  intro t
  by_cases hE : IsEnv H hP t
  · by_cases h0 : Structure.rel (L := setTemplateLanguage 6 ar6) (placeholderRel 0) ![t]
    · right
      obtain ⟨a, U, ha, hU, htU⟩ := hE
      have ft := htU.1.1
      have key : ∀ x y, Structure.rel (L := setTemplateLanguage 6 ar6) (placeholderRel 1) ![x, y] ↔
          Structure.rel (L := setTemplateLanguage 6 ar6) (placeholderRel 4)
            ![LeanProofs.BoundedZFCConsistency.econs H x (LeanProofs.BoundedZFCConsistency.econs H y t)] := by
        intro x y
        have ft1 := LeanProofs.BoundedZFCConsistency.econs_functional H ft y
        rcases hq y x (LeanProofs.BoundedZFCConsistency.econs H x
            (LeanProofs.BoundedZFCConsistency.econs H y t)) with h | h
        · rcases h (LeanProofs.BoundedZFCConsistency.econs H y t) x with h1 | h1 | h1
          · exact absurd rfl h1
          · exact absurd ((LStepExT.eval_econsS _ x _ ft1).2 rfl) h1
          · rcases h1 t y with h2 | h2 | h2
            · exact absurd rfl h2
            · exact absurd ((LStepExT.eval_econsS _ y t ft).2 rfl) h2
            · exact absurd h0 h2
        · exact h
      have happ : ∀ x y, LFinalRepl.appS.Eval ![x, y, t] Empty.elim ↔
          Structure.rel (L := setTemplateLanguage 6 ar6) (placeholderRel 1) ![x, y] := by
        intro x y
        rw [LFinalRepl.eval_appS x y t ft, key]
        simp [P₄]
      by_cases hA : ∀ x, SetTheory.BusyBeaver.ZFC.Constructible.InL H hP x → ∃ y,
          SetTheory.BusyBeaver.ZFC.Constructible.InL H hP y ∧
            Structure.rel (L := setTemplateLanguage 6 ar6) (placeholderRel 1) ![x, y] ∧
            ∀ y', SetTheory.BusyBeaver.ZFC.Constructible.InL H hP y' →
              Structure.rel (L := setTemplateLanguage 6 ar6) (placeholderRel 1) ![x, y'] → y' = y
      · right
        intro X
        by_cases hX : SetTheory.BusyBeaver.ZFC.Constructible.InL H hP X
        · right
          obtain ⟨Y, hY, hYy⟩ := hS t a ha U hU htU (fun x hx => by
            obtain ⟨y, hy, h1, h2⟩ := hA x hx
            exact ⟨y, hy, (happ x y).2 h1, fun y' hy' h' => h2 y' hy' ((happ x y').1 h')⟩) X hX
          refine ⟨Y, hY, fun y => ?_⟩
          by_cases hy : SetTheory.BusyBeaver.ZFC.Constructible.InL H hP y
          · right
            rw [hYy y hy]
            simp only [happ]
            exact Iff.rfl
          · left; exact hy
        · left; exact hX
      · left
        push_neg at hA
        obtain ⟨x, hx, hxy⟩ := hA
        refine ⟨x, hx, fun y => ?_⟩
        by_cases hy : SetTheory.BusyBeaver.ZFC.Constructible.InL H hP y
        · by_cases hF : Structure.rel (L := setTemplateLanguage 6 ar6) (placeholderRel 1) ![x, y]
          · right; right
            exact hxy y hy hF
          · right; left; exact hF
        · left; exact hy
    · left; right; exact h0
  · left; left
    intro a ha U hU htU
    exact hE ⟨a, U, ha, hU, htU⟩

section Typed

open LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping Entailment
open LeanProofs.ZFCinPA.LDriverBase LeanProofs.ZFCinPA.LDriverSteps LeanProofs.ZFCinPA.LMatch
open LeanProofs.ZFCinPA.LGlue1 LeanProofs.ZFCinPA.LGlue2 LeanProofs.ZFCinPA.LGlue4
open LeanProofs.ZFCinPA.LGlueCodes LeanProofs.ZFCinPA.ModelCodedBindFree
open LeanProofs.BoundedPAConsistency.InternalRelativization
open scoped LO.FirstOrder.Arithmetic

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

local notation "bv" i => Bootstrapping.Semiterm.bvar i

/-- The equality atom `a = b`. -/
def eqA {n : ℕ} (a b : Bootstrapping.Semiterm V ℒₛₑₜ n) : SF V n :=
  Bootstrapping.Semiformula.rel (Language.Eq.eq : (ℒₛₑₜ).Rel 2) ![a, b]

theorem eq2S_subst {n : ℕ} (a b : Bootstrapping.Semiterm V ℒₛₑₜ n) :
    (⌜eq2S⌝ : SF V 2).subst ![a, b] = eqA a b := by
  apply Bootstrapping.Semiformula.ext
  simp [eqA, eq2S, Semiformula.Operator.eq_def, LO.FirstOrder.Sentence.typed_quote_def,
    Bootstrapping.SemitermVec.val, Matrix.vecHead, Matrix.vecTail]

section TT

variable {k : ℕ} {ar : Fin k → ℕ}

@[simp] theorem tt1 {n : ℕ} (a : Fin n) :
    (fun i ↦ translateTerm (V := V)
      (Rew.emb ((![#a] : Fin 1 → Semiterm (setTemplateLanguage k ar) Empty n) i))) =
      fun _ ↦ bv a := by
  funext i
  match i with
  | 0 => simp

@[simp] theorem tt2 {n : ℕ} (a b : Fin n) :
    (fun i ↦ translateTerm (V := V)
      (Rew.emb ((![#a, #b] : Fin 2 → Semiterm (setTemplateLanguage k ar) Empty n) i))) =
      ![bv a, bv b] := by
  funext i
  match i with
  | 0 => simp
  | 1 => simp

@[simp] theorem tt3 {n : ℕ} (a b c : Fin n) :
    (fun i ↦ translateTerm (V := V)
      (Rew.emb ((![#a, #b, #c] : Fin 3 → Semiterm (setTemplateLanguage k ar) Empty n) i))) =
      ![bv a, bv b, bv c] := by
  funext i
  match i with
  | 0 => simp
  | 1 => simp
  | 2 => simp

end TT

theorem q_five {k n : ℕ} (w : Bootstrapping.SemitermVec V ℒₛₑₜ (k + 5) n) :
    w.q 5 = (w 4).bShift := rfl

theorem q_six {k n : ℕ} (w : Bootstrapping.SemitermVec V ℒₛₑₜ (k + 6) n) :
    w.q 6 = (w 5).bShift := rfl

theorem vec_one {n : ℕ} (t : Bootstrapping.Semiterm V ℒₛₑₜ n) :
    (![t] : Fin 1 → Bootstrapping.Semiterm V ℒₛₑₜ n) = fun _ ↦ t := by
  funext i
  match i with
  | 0 => rfl

/-- The translated `mp₃` over `M`. -/
def MP3 (M : SF V 1) : SF V 3 :=
  ∃⁰ ∃⁰ (eqA (bv 0) (bv 3) ⋏ ((⌜econsS⌝ : SF V 3).subst ![bv 2, bv 0, bv 1] ⋏
    (∃⁰ ∃⁰ (eqA (bv 0) (bv 6) ⋏ ((⌜econsS⌝ : SF V 3).subst ![bv 3, bv 0, bv 1] ⋏
      M.subst (fun _ ↦ bv 1))))))

/-- The body of the level-two premise, at level one (`y = #0`). -/
def QX2 (M : SF V 1) (R : SF V 2) (E : SF V 1) : SF V 1 :=
  ∀⁰ ∀⁰ (∼MP3 M ⋎ (R.subst ![bv 1, bv 2] 🡘 E.subst (fun _ ↦ bv 0)))

theorem tr_qHyp2 (Ks : (i : Fin 6) → SF V (ar6 i)) :
    translateFormula Ks (Rewriting.emb qHyp2) = ∀⁰ QX2 (Ks 0) (Ks 1) (Ks 4) := by
  simp [qHyp2, mp3, P₀, F₁, P₄, translateFormula, QX2, MP3, LogicalConnective.iff,
    Bootstrapping.Semiformula.imp_def, eq2S_subst]
  refine ⟨⟨rfl, rfl⟩, rfl, rfl⟩

/-- The opened premise is the free form of the generalized one. -/
theorem QX2_free (M : SF V 1) (R : SF V 2) (E : SF V 1) (hE : E.shift = E) :
    (QX2 M R E).free =
      ∀⁰ QX (MpT M.shift zT) (R.shift.subst ![bv 0, Bootstrapping.Semiterm.fvar 0]) E := by
  simp [QX2, QX, MP3, MP2, MpT, Bootstrapping.Semiformula.free,
    Bootstrapping.Semiformula.shift_substs, Bootstrapping.Semiformula.substs_substs, hE,
    shift_quoteT, LogicalConnective.iff, Bootstrapping.Semiformula.imp_def, eqT4_eq, econsT4,
    econsT3, zT, eqA, q_one, q_two, LGlue3.q_three, LGlue3.q_four, q_five, q_six]
  rw [vec_one]

/-- The relativized core, at level two. -/
def R2 {K : V} (hK : IsSemiformula ℒₛₑₜ 2 K) : SF V 2 :=
  ⟨rel K, by simpa using isSemiformula_relativize hdL hK⟩

theorem openVec_one : openVec (1 : V) = ^#0 ∷ ^&0 ∷ 0 := by
  rw [openVec, show (1 : V) = 0 + 1 by simp, ModelCodedSpecialization.qVecIter_succ_left]
  simp [Bootstrapping.qVec]

/-- **The level-two glue premise.** -/
theorem qPremise2 {m K : V} (hK : IsSemiformula ℒₛₑₜ 2 K)
    (hb : IsSemiformula ℒₛₑₜ (m + 2) (bindFreeAt ℒₛₑₜ 2 K)) :
    (𝗭𝗙 : SetTheory).internalize V ⊢ ∀⁰ QX2 (MT m) (R2 hK) (LDriver.envFormT 2 hK) := by
  have h21 : (2 : V) - 1 = 1 := by
    rw [show (2 : V) = 1 + 1 from one_add_one_eq_two.symm, add_tsub_cancel_right]
  have hw : IsSemitermVec ℒₛₑₜ 2 1 (openVec (1 : V)) := by
    simpa [one_add_one_eq_two] using openVec_isSemitermVec (V := V) 1
  have hK1 : IsSemiformula ℒₛₑₜ 1 (subst ℒₛₑₜ (openVec 1) (shift ℒₛₑₜ K)) := hK.shift.subst hw
  have hopen := bindFreeAt_open hK two_ne_zero
  rw [h21] at hopen
  have hfv : FvLt (m + 1 + 1) (free ℒₛₑₜ (subst ℒₛₑₜ (openVec 1) (shift ℒₛₑₜ K))) := by
    rw [LFvBound.fvLt_free_iff hK1, hopen]
    simpa [add_assoc, one_add_one_eq_two] using hb
  have ih := glue (m + 1 + 1 + formulaComplexity ℒₛₑₜ
    (free ℒₛₑₜ (subst ℒₛₑₜ (openVec 1) (shift ℒₛₑₜ K)))) hK1.free (m + 1 + 1) (by simp) le_rfl hfv
  have hQ := qPremise (j := m + 1) hK1 ih
  rw [MT_succ] at hQ
  have eE : LDriver.envFormT 1 hK1 = LDriver.envFormT 2 hK := by
    apply Bootstrapping.Semiformula.ext
    have := envForm_open hK two_ne_zero
    rw [h21] at this
    simpa [LDriver.envFormT] using this
  have eR : RF hK1 le_rfl = (R2 hK).shift.subst ![bv 0, Bootstrapping.Semiterm.fvar 0] := by
    apply Bootstrapping.Semiformula.ext
    have hw' : IsSemitermVec ℒₛₑₜ 2 1 (^#0 ∷ ^&0 ∷ 0 : V) := openVec_one (V := V) ▸ hw
    simp [RF, R2, rel, relativize_shift hdL hdLs hK.isUFormula, openVec_one,
      Bootstrapping.SemitermVec.val, Matrix.vecHead, Matrix.vecTail]
    exact (relativize_subst hdL hK.shift hw').symm
  have hEs : (LDriver.envFormT 2 hK).shift = LDriver.envFormT 2 hK :=
    Bootstrapping.Semiformula.ext (shift_envForm hK)
  rw [eE, eR, ← QX2_free (MT m) (R2 hK) _ hEs] at hQ
  exact Bootstrapping.TProof.all! hQ

theorem relT_imp {n : ℕ} (φ ψ : SF V n) : rel (φ 🡒 ψ).val = neg ℒₛₑₜ (rel φ.val) ^⋎ rel ψ.val := by
  rw [Bootstrapping.Semiformula.imp_def, relT_or, relT_neg]

theorem tr_F1 {n : ℕ} (Ks : (i : Fin 6) → SF V (ar6 i)) (a b : Fin n) :
    translateFormula Ks (@FirstOrder.Semiformula.rel L6 ℕ n 2 (placeholderRel (1 : Fin 6))
      ![#a, #b]) = (Ks 1 : SF V 2).subst ![bv a, bv b] := by
  show (Ks 1 : SF V 2).subst _ = _
  congr 1
  funext (i : Fin 2)
  match i with
  | 0 => simp
  | 1 => simp

section Body

variable {K : V} (hK : IsSemiformula ℒₛₑₜ 2 K)

/-- The hypothesis of the typed replacement body. -/
def TA (Kt : SF V 2) : Bootstrapping.Formula V ℒₛₑₜ :=
  ∀⁰ ∃⁰ ((Kt.subst ![⌜(#1 : SyntacticSemiterm ℒₛₑₜ 2)⌝, ⌜(#0 : SyntacticSemiterm ℒₛₑₜ 2)⌝])
      ⋏ (∀⁰ ((Kt.subst ![⌜(#2 : SyntacticSemiterm ℒₛₑₜ 3)⌝, ⌜(#0 : SyntacticSemiterm ℒₛₑₜ 3)⌝])
          🡒 (⌜repAtomEq⌝ : SF V 3))))

/-- The conclusion of the typed replacement body. -/
def TB (Kt : SF V 2) : Bootstrapping.Formula V ℒₛₑₜ :=
  ∀⁰ ∃⁰ ∀⁰ ((⌜repAtomYY⌝ : SF V 3)
    🡘 (∃⁰ ((⌜repAtomXX⌝ : SF V 4)
        ⋏ Kt.subst ![⌜(#0 : SyntacticSemiterm ℒₛₑₜ 4)⌝, ⌜(#1 : SyntacticSemiterm ℒₛₑₜ 4)⌝])))

theorem repBody_eq (Kt : SF V 2) : repBody Kt = (TA Kt 🡒 TB Kt) := rfl

include hK in
theorem relReplA_val (Ks : (i : Fin 6) → SF V (ar6 i)) (hR : (Ks 1).val = rel K) :
    (translateFormula Ks (Rewriting.emb relReplA)).val = rel (TA ⟨K, by simpa using hK⟩).val := by
  have eD : subst ℒₛₑₜ (^#0 ∷ 0)
      (⌜(Rewriting.emb domL : SetTheorySemiproposition 1)⌝ : SF V 1).val = dL := by
    have h1 : (⌜(Rewriting.emb domL : SetTheorySemiproposition 1)⌝ : SF V 1).val = dL := rfl
    rw [h1]
    exact subst_eq_self hdL (by simp) (fun i hi ↦ by
      have : i = 0 := by simpa using hi
      subst this; simp)
  simp only [TA, repAtomEq, FirstOrder.Semiformula.typed_quote_rel, relT_all, relT_ex, relT_and,
    relT_imp, relT_rel, relT_subst]
  simp [relReplA, translateFormula, F₁, hR, Matrix.vecHead, Matrix.vecTail,
    LO.FirstOrder.Sentence.typed_quote_def, FirstOrder.Semiformula.typed_quote_rel, eD,
    eq2S_subst, eqA]
  refine ⟨?_, ?_, ?_⟩
  · show (Bootstrapping.Semiformula.subst (![bv 1, bv 0] : Bootstrapping.SemitermVec V ℒₛₑₜ 2 2)
      (Ks 1 : SF V 2)).val = _
    simp [hR, Bootstrapping.SemitermVec.val, Matrix.vecHead, Matrix.vecTail]
  · show (∼Bootstrapping.Semiformula.subst (![bv 2, bv 0] : Bootstrapping.SemitermVec V ℒₛₑₜ 2 3)
      (Ks 1 : SF V 2)).val = _
    simp [hR, Bootstrapping.SemitermVec.val, Matrix.vecHead, Matrix.vecTail]
  · have := congrArg Bootstrapping.Semiformula.val (eq2S_subst (V := V) (n := 3) (bv 0) (bv 1))
    simpa [eqA, LO.FirstOrder.Sentence.typed_quote_def, Bootstrapping.SemitermVec.val,
      Matrix.vecHead, Matrix.vecTail] using this

include hK in
theorem relReplB_val (Ks : (i : Fin 6) → SF V (ar6 i)) (hR : (Ks 1).val = rel K) :
    (translateFormula Ks (Rewriting.emb relReplB)).val = rel (TB ⟨K, by simpa using hK⟩).val := by
  have eD : subst ℒₛₑₜ (^#0 ∷ 0)
      (⌜(Rewriting.emb domL : SetTheorySemiproposition 1)⌝ : SF V 1).val = dL := by
    have h1 : (⌜(Rewriting.emb domL : SetTheorySemiproposition 1)⌝ : SF V 1).val = dL := rfl
    rw [h1]
    exact subst_eq_self hdL (by simp) (fun i hi ↦ by
      have : i = 0 := by simpa using hi
      subst this; simp)
  simp only [TB, repAtomYY, repAtomXX, FirstOrder.Semiformula.typed_quote_rel, relT_all, relT_ex,
    relT_and, relT_iff, relT_rel, relT_subst]
  simp [relReplB, translateFormula, F₁, zyS, hR, tr_F1, Matrix.vecHead, Matrix.vecTail,
    LO.FirstOrder.Sentence.typed_quote_def, FirstOrder.Semiformula.typed_quote_rel, eD]
  have hS : IsUFormula ℒₛₑₜ (subst ℒₛₑₜ (^#0 ∷ ^#1 ∷ 0) (rel K)) := by
    have := ((R2 hK).subst (![bv 0, bv 1] : Bootstrapping.SemitermVec V ℒₛₑₜ 2 4)).isUFormula
    simpa [R2, Bootstrapping.SemitermVec.val, Matrix.vecHead, Matrix.vecTail] using this
  have h := (Bootstrapping.Semiformula.nrel (Language.Mem.mem : (ℒₛₑₜ).Rel 2)
    ![Bootstrapping.Semiterm.bvar 0, Bootstrapping.Semiterm.bvar 1] : SF V 2).isSemiformula
  rw [Bootstrapping.Semiformula.nrel_val] at h
  have hmem := (IsSemiformula.nrel.mp h).1
  simp only [Nat.cast_ofNat] at hmem
  simp only [Bootstrapping.iff, Bootstrapping.imp]
  rw [neg_rel hmem (by simp), neg_ex (by simp [hdL.isUFormula, hmem, hS]),
    neg_and hdL.isUFormula (by simp [hmem, hS]), neg_and (by simp [hmem]) hS, neg_rel hmem (by simp)]

end Body

theorem replConcl_val {m K : V} (hK : IsSemiformula ℒₛₑₜ 2 K) (Ks : (i : Fin 6) → SF V (ar6 i))
    (hM : (Ks 0).val = mVal m) (hR : (Ks 1).val = rel K) :
    (translateFormula Ks (Rewriting.emb
      (∀⁰ (∼(lift envS ⋏ P₀) ⋎ (∼relReplA ⋎ relReplB)) : Sentence L6))).val =
      pVal m (rel (repBodyVal K)) := by
  let Kt : SF V 2 := ⟨K, by simpa using hK⟩
  have hrep : repBodyVal K = (TA Kt 🡒 TB Kt).val := by
    rw [← repBody_eq]; exact repBodyVal_eq Kt
  rw [hrep, relT_imp, ← relReplA_val hK Ks hR, ← relReplB_val hK Ks hR, pVal, ← hM]
  simp [translateFormula, P₀]

/-- **The replacement base.** -/
theorem repl_base {m K : V} (hK : IsSemiformula ℒₛₑₜ 2 K)
    (hb : IsSemiformula ℒₛₑₜ (m + 2) (bindFreeAt ℒₛₑₜ 2 K)) :
    Bootstrapping.Provable (𝗭𝗙 : SetTheory) (pVal m (rel (repBodyVal K))) := by
  have hQ := qPremise2 hK hb
  obtain ⟨F, hF⟩ := LDriver.driverT hK
  have hc := compiled replComb_provable (K6 (MT m) (R2 hK) ⊤ ⊤ (LDriver.envFormT 2 hK) F)
  simp only [replComb, LogicalConnective.HomClass.map_imply, LogicalConnective.HomClass.map_and,
    translateFormula_imp, tr_and', tr_tot₅, tr_refl₄₅, tr_qHyp2] at hc
  have hX := Bootstrapping.tprovable_iff_provable.mp (hc ⨀ K!_intro hF hQ)
  rwa [replConcl_val hK _ rfl rfl] at hX

/-- **Every recognized replacement code is relativized-provable in `𝗭𝗙`.** -/
theorem repl_obligation {p : V} (hp : RepR p) :
    Bootstrapping.Provable (𝗭𝗙 : SetTheory) (rel p) := by
  obtain ⟨m, -, b, -, rfl, hbU, hbs, hbv, K, -, hK, hKb⟩ := hp
  have hb : IsSemiformula ℒₛₑₜ m b := by simpa [hbv] using hbU.isSemiformula
  have hK' : IsSemiformula ℒₛₑₜ 2 K := by simpa using hK
  have hfv : FvLt m (repBodyVal K) := hKb ▸ LFvBound.fvLt_subst_fvarVec hb hbs
  have h0 := repl_base (m := m) hK' (LFvBound.repl_core_bound hK' hfv)
  rw [← hKb] at h0
  exact peel_close (isSemiformula_relativize hdL (IsSemiformula.qqAlls (by simpa using hb)))
    (peel hb hbs h0)

end Typed

end LeanProofs.ZFCinPA.LReplBase
