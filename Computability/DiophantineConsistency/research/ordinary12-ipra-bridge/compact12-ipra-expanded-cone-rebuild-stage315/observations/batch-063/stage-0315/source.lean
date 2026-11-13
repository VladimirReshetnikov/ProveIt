import ZFCinPA.LPeel
import ZFCinPA.LFinalSep

set_option autoImplicit false
noncomputable section

/-!
# The separation base

For a separation core `K` (level one) whose free variables lie below `m`,
`𝗭𝗙 ⊢ ∀t (¬(Env t ∧ M_m t) ∨ relativize L (sepBodyVal K))` (`sep_base`).

One template over the driver's language `L6` does the work (`sepComb`): from
the reflection invariant of `P₄` at `F₅` (which, by the final separation
template, cuts every constructible `x` by `P₄` read at `z :: t`) and the glue
premise `∀y ∀t (¬mp(t, y) ∨ (P₂ y ↔ P₄ t))`, every matched environment
satisfies the relativized separation body over `P₂`. Compiled at
`P₀ = M_m`, `P₂ = relativize K`, `P₄ = envForm 1 K` and the driver's code,
its hypotheses are `LDriver.driverT` and `LGlue4.qPremise`.
-/

namespace LeanProofs.ZFCinPA.LSepBase

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA LeanProofs.ZFCinPA.SetPlaceholders LeanProofs.ZFCinPA.LTemplate
open LeanProofs.ZFCinPA.EnvTransform LeanProofs.ZFCinPA.LPieces LeanProofs.ZFCinPA.LInvariant
open LeanProofs.ZFCinPA.LStepAnd LeanProofs.ZFCinPA.LGlueT2 LeanProofs.ZFCinPA.LPeel
open LeanProofs.ZFCinPA.ConstructibleInterpretation (domL)

local instance : Language.Mem L6 := ⟨Sum.inl Language.Set.Rel.mem⟩

/-- `z ∈ y` (`z = #0`, `y = #1`). -/
def zyS : SetTheorySemisentence 2 := FirstOrder.Semiformula.rel Language.Mem.mem ![#0, #1]

/-- The matching clause over `P₀`: `∃t₁ ∃z (z = y ∧ t = econs z t₁ ∧ P₀ t₁)`. -/
def mp6 : Semisentence L6 2 :=
  ∃⁰ ∃⁰ ((lift eq2S ⇜ ![#0, #3]) ⋏ ((lift econsS ⇜ ![#2, #0, #1]) ⋏ (P₀ ⇜ ![#1])))

/-- The glue premise: `∀y ∀t (¬mp(t, y) ∨ (P₂ y ↔ P₄ t))`. -/
def qHyp6 : Sentence L6 := ∀⁰ ∀⁰ (∼mp6 ⋎ ((P₂ ⇜ ![#1]) 🡘 (P₄ ⇜ ![#0])))

/-- The relativized separation body over `P₂`, read at an ignored `t`. -/
def relSep6 : Semisentence L6 1 :=
  ∀⁰ (∼(lift domL ⇜ ![#0]) ⋎ (∃⁰ ((lift domL ⇜ ![#0]) ⋏
    (∀⁰ (∼(lift domL ⇜ ![#0]) ⋎
      ((lift zyS ⇜ ![#0, #1]) 🡘 ((lift zyS ⇜ ![#0, #2]) ⋏ (P₂ ⇜ ![#0]))))))))

/-- **The separation combination.** -/
def sepComb : Sentence L6 :=
  ((totS F₅ ⋏ reflS P₄ F₅) ⋏ qHyp6) 🡒 ∀⁰ (∼(lift envS ⋏ P₀) ⋎ relSep6)

theorem sepComb_provable : templTheory 6 ar6 ⊢ sepComb := by
  apply templ_provable
  intro M _ _ s _ _ hT
  haveI : M↓[ℒₛₑₜ] ⊧* (𝗭𝗙 : SetTheory) := pure_models (k := 6) (arities := ar6)
  have hR := ConstructibleInterpretation.regular_of_modelsZF (V := M)
  set H := ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M)
  set hP := ConstructibleInterpretation.power_of_modelsZF (V := M)
  have hsep := models_of_provable hT LFinalSep.sepTemplate_provable
  simp only [LFinalSep.sepTemplate, Semantics.Imp.models_imply] at hsep
  simp only [sepComb, Semantics.Imp.models_imply, Semantics.And.models_and]
  rintro ⟨hinv, hq⟩
  have hS := hsep (Semantics.And.models_and.mpr hinv)
  rw [LFinalSep.models_sepEnvS] at hS
  simp [models_iff, qHyp6, mp6, P₀, P₂, P₄, eq2S, Semiformula.Operator.eq_def] at hq
  simp [models_iff, relSep6, envS, zyS, P₀, P₂, ConstructibleInterpretation.eval_domL H hP,
    eval_stageP (H := H) (hP := hP), eval_envP (H := H)]
  simp [P₄] at hS
  intro t
  by_cases hE : IsEnv H hP t
  · by_cases h0 : Structure.rel (L := setTemplateLanguage 6 ar6) (placeholderRel 0) ![t]
    · right
      intro x
      by_cases hx : SetTheory.BusyBeaver.ZFC.Constructible.InL H hP x
      · right
        obtain ⟨a, U, ha, hU, htU⟩ := hE
        have ft := htU.1.1
        have key : ∀ z, Structure.rel (L := setTemplateLanguage 6 ar6) (placeholderRel 2) ![z] ↔
            Structure.rel (L := setTemplateLanguage 6 ar6) (placeholderRel 4)
              ![LeanProofs.BoundedZFCConsistency.econs H z t] := by
          intro z
          rcases hq z (LeanProofs.BoundedZFCConsistency.econs H z t) with h | h
          · rcases h t z with h1 | h1 | h1
            · exact absurd rfl h1
            · exact absurd ((LStepExT.eval_econsS _ z t ft).2 rfl) h1
            · exact absurd h0 h1
          · exact h
        obtain ⟨s', hs', hsz⟩ := hS t a ha U hU htU x hx
        refine ⟨s', hs', fun z => ?_⟩
        by_cases hz : SetTheory.BusyBeaver.ZFC.Constructible.InL H hP z
        · right
          rw [hsz z hz]
          refine and_congr_right fun _ => ?_
          constructor
          · rintro ⟨e, he1, he2⟩
            rw [(LStepExT.eval_econsS e z t ft).1 he1] at he2
            exact (key z).2 he2
          · intro h2
            exact ⟨_, (LStepExT.eval_econsS _ z t ft).2 rfl, (key z).1 h2⟩
        · left; exact hz
      · left; exact hx
    · left; right; exact h0
  · left; left
    intro a ha U hU htU
    exact hE ⟨a, U, ha, hU, htU⟩

/-! ## Compiled at internal codes -/

section Typed

open LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping Entailment
open LeanProofs.ZFCinPA.LDriverBase LeanProofs.ZFCinPA.LDriverSteps LeanProofs.ZFCinPA.LMatch
open LeanProofs.ZFCinPA.LGlue1 LeanProofs.ZFCinPA.LGlue2 LeanProofs.ZFCinPA.LGlue4
open LeanProofs.ZFCinPA.LGlueCodes
open LeanProofs.BoundedPAConsistency.InternalRelativization
open scoped LO.FirstOrder.Arithmetic

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem tr_qHyp6 (Ks : (i : Fin 6) → SF V (ar6 i)) :
    translateFormula Ks (Rewriting.emb qHyp6) = ∀⁰ QX (Ks 0) (Ks 2) (Ks 4) := by
  simp [qHyp6, mp6, P₀, P₂, P₄, translateFormula, QX, MP2, eqT4, econsT4, LogicalConnective.iff,
    Bootstrapping.Semiformula.imp_def]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · congr 1
    funext i
    match i with
    | 0 => simp
    | 1 => simp
  · congr 1
    funext i
    match i with
    | 0 => simp
    | 1 => simp
    | 2 => simp
  · rfl

/-! ### Relativization of typed formulas -/

theorem relT_all {n : ℕ} (φ : SF V (n + 1)) :
    rel (∀⁰ φ).val = ^∀ (neg ℒₛₑₜ dL ^⋎ rel φ.val) := relativize_all φ.isUFormula

theorem relT_ex {n : ℕ} (φ : SF V (n + 1)) : rel (∃⁰ φ).val = ^∃ (dL ^⋏ rel φ.val) :=
  relativize_exs φ.isUFormula

theorem relT_and {n : ℕ} (φ ψ : SF V n) : rel (φ ⋏ ψ).val = rel φ.val ^⋏ rel ψ.val :=
  relativize_and φ.isUFormula ψ.isUFormula

theorem relT_or {n : ℕ} (φ ψ : SF V n) : rel (φ ⋎ ψ).val = rel φ.val ^⋎ rel ψ.val :=
  relativize_or φ.isUFormula ψ.isUFormula

theorem relT_neg {n : ℕ} (φ : SF V n) : rel (∼φ).val = neg ℒₛₑₜ (rel φ.val) := by
  rw [Bootstrapping.Semiformula.val_neg]
  exact (relativize_neg hdL.isUFormula φ.isUFormula).symm

theorem relT_iff {n : ℕ} (φ ψ : SF V n) :
    rel (φ 🡘 ψ).val = Bootstrapping.iff ℒₛₑₜ (rel φ.val) (rel ψ.val) := by
  have e : (φ 🡘 ψ) = (∼φ ⋎ ψ) ⋏ (∼ψ ⋎ φ) := by
    simp [LogicalConnective.iff, Bootstrapping.Semiformula.imp_def]
  rw [e, relT_and, relT_or, relT_or, relT_neg, relT_neg]
  rfl

theorem relT_rel {n k : ℕ} (R : (ℒₛₑₜ).Rel k) (v : Bootstrapping.SemitermVec V ℒₛₑₜ k n) :
    rel (Bootstrapping.Semiformula.rel R v).val = (Bootstrapping.Semiformula.rel R v).val := by
  have h := (Bootstrapping.Semiformula.rel R v).isSemiformula
  obtain ⟨hR, hv⟩ := IsSemiformula.rel.mp h
  exact relativize_rel hR hv.isUTerm

theorem relT_subst {n m : ℕ} (φ : SF V n) (w : Bootstrapping.SemitermVec V ℒₛₑₜ n m) :
    rel (φ.subst w).val = subst ℒₛₑₜ w.val (rel φ.val) :=
  (relativize_subst hdL φ.isSemiformula w.isSemitermVec).symm

theorem relSep_val {K : V} (hK : IsSemiformula ℒₛₑₜ 1 K) (Ks : (i : Fin 6) → SF V (ar6 i))
    (hR : (Ks 2).val = rel K) :
    (translateFormula Ks (Rewriting.emb relSep6)).val = rel (sepBodyVal K) := by
  let Kt : SF V 1 := ⟨K, by simpa using hK⟩
  have hS : sepBodyVal K = (sepBody Kt).val := sepBodyVal_eq Kt
  rw [hS]
  simp only [sepBody, sepAtomZY, sepAtomZX, FirstOrder.Semiformula.typed_quote_rel, relT_all,
    relT_ex, relT_iff, relT_and, relT_rel, relT_subst]
  have hRK : IsSemiformula ℒₛₑₜ 1 (rel K) := isSemiformula_relativize hdL hK
  have hid : ∀ {p : V}, IsSemiformula ℒₛₑₜ 1 p → subst ℒₛₑₜ (^#0 ∷ 0) p = p := fun hp ↦
    subst_eq_self hp (by simp) (fun i hi ↦ by
      have : i = 0 := by simpa using hi
      subst this; simp)
  have e1 : subst ℒₛₑₜ (^#0 ∷ 0) (rel K) = rel K := hid hRK
  have eD : subst ℒₛₑₜ (^#0 ∷ 0) (⌜(Rewriting.emb domL : SetTheorySemiproposition 1)⌝ : SF V 1).val = dL := by
    have h1 : (⌜(Rewriting.emb domL : SetTheorySemiproposition 1)⌝ : SF V 1).val = dL := rfl
    rw [h1]; exact hid hdL
  simp [relSep6, translateFormula, P₂, zyS, hR, Matrix.vecHead, Matrix.vecTail,
    LO.FirstOrder.Sentence.typed_quote_def, FirstOrder.Semiformula.typed_quote_rel, e1, eD, Kt]
  have h := (Bootstrapping.Semiformula.nrel (Language.Mem.mem : (ℒₛₑₜ).Rel 2)
    ![Bootstrapping.Semiterm.bvar 0, Bootstrapping.Semiterm.bvar 1] : SF V 2).isSemiformula
  rw [Bootstrapping.Semiformula.nrel_val] at h
  have hmem := (IsSemiformula.nrel.mp h).1
  simp only [Nat.cast_ofNat] at hmem
  simp only [Bootstrapping.iff, Bootstrapping.imp]
  rw [neg_rel hmem (by simp), neg_and (by simp [hmem]) hRK.isUFormula, neg_rel hmem (by simp)]

theorem sepConcl_val {m K : V} (hK : IsSemiformula ℒₛₑₜ 1 K) (Ks : (i : Fin 6) → SF V (ar6 i))
    (hM : (Ks 0).val = mVal m) (hR : (Ks 2).val = rel K) :
    (translateFormula Ks (Rewriting.emb (∀⁰ (∼(lift envS ⋏ P₀) ⋎ relSep6) : Sentence L6))).val =
      pVal m (rel (sepBodyVal K)) := by
  rw [← relSep_val hK Ks hR, pVal, ← hM]
  simp [translateFormula, P₀]

/-- **The separation base.** -/
theorem sep_base {m K : V} (hK : IsSemiformula ℒₛₑₜ 1 K) (hfv : FvLt (m + 1) (free ℒₛₑₜ K)) :
    Bootstrapping.Provable (𝗭𝗙 : SetTheory) (pVal m (rel (sepBodyVal K))) := by
  have ih := glue (m + 1 + formulaComplexity ℒₛₑₜ (free ℒₛₑₜ K)) hK.free (m + 1) (by simp) le_rfl hfv
  have hQ := qPremise hK ih
  obtain ⟨F, hF⟩ := LDriver.driverT hK
  have hc := compiled sepComb_provable
    (K6 (MT m) ⊤ (RF hK le_rfl) ⊤ (LDriver.envFormT 1 hK) F)
  simp only [sepComb, LogicalConnective.HomClass.map_imply, LogicalConnective.HomClass.map_and,
    translateFormula_imp, tr_and', tr_tot₅, tr_refl₄₅, tr_qHyp6] at hc
  have hX := Bootstrapping.tprovable_iff_provable.mp (hc ⨀ K!_intro hF hQ)
  rwa [sepConcl_val hK _ rfl rfl] at hX

/-- **Every recognized separation code is relativized-provable in `𝗭𝗙`.** -/
theorem sep_obligation {p : V} (hp : SepR p) :
    Bootstrapping.Provable (𝗭𝗙 : SetTheory) (rel p) := by
  obtain ⟨m, -, b, -, rfl, hbU, hbs, hbv, K, -, hK, hKb⟩ := hp
  have hb : IsSemiformula ℒₛₑₜ m b := by simpa [hbv] using hbU.isSemiformula
  have hK' : IsSemiformula ℒₛₑₜ 1 K := by simpa using hK
  have hfv : FvLt m (sepBodyVal K) := hKb ▸ LFvBound.fvLt_subst_fvarVec hb hbs
  have h0 := sep_base (m := m) hK' (LFvBound.sep_core_bound hK' hfv)
  rw [← hKb] at h0
  exact peel_close (isSemiformula_relativize hdL (IsSemiformula.qqAlls (by simpa using hb)))
    (peel hb hbs h0)

end Typed

end LeanProofs.ZFCinPA.LSepBase
