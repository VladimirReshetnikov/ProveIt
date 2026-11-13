import ZFCinPA.OpenedClosure
import ZFCinPA.LFvBound
import ZFCinPA.LGlue4

set_option autoImplicit false
noncomputable section

/-!
# The peel: from the opened schema body to its relativized closure

A schema axiom code is `p = qqAlls b m`; the final templates produce, for the
opened body `subst (fvarVec m) b`, the statement

`𝗭𝗙 ⊢ ∀t (¬(Env t ∧ M_m t) ∨ relativize L (subst (fvarVec m) b))`,

where `Env t` says that `t` is an environment over some stage `L_a` and
`M_m` is the matching code of `LMatch`. The peel removes the opened
variables one at a time, outermost first, as the Tait rule for `∀` does:
the freed premise at `m + 1` matched variables is generalized, and the step
template `peelG` turns it into the relativized universal at `m` (an
environment extends by any constructible element: `isEnv_econs`). At zero
matched variables a functional environment exists (`isEnv_base`), and the
closing template `finG`, with a nullary placeholder, discharges the
hypothesis.
-/

namespace LeanProofs.ZFCinPA.LPeel

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA LeanProofs.ZFCinPA.SetPlaceholders LeanProofs.ZFCinPA.LTemplate
open LeanProofs.ZFCinPA.LInvariant LeanProofs.ZFCinPA.EnvTransform LeanProofs.ZFCinPA.LPieces
open LeanProofs.ZFCinPA.LGlueT LeanProofs.ZFCinPA.LGlueT2

/-! ## Environments over a stage -/

section Math

open SetTheory.BusyBeaver.ZFC.InternalOrd SetTheory.BusyBeaver.ZFC.Constructible
  SetTheory.BusyBeaver.ZFC.ConstructibleDef LeanProofs.BoundedZFCConsistency

variable {V : Type*} [SetStructure V] (H : _root_.SetTheory.ZFAxioms (memRel V))
  (hR : Regular (memRel V))
  (hP : ∀ a, ∃ p, ∀ x, memRel V x p ↔ _root_.SetTheory.Sub (memRel V) x a)

/-- `t` is an environment over some stage `L_a`. -/
def IsEnv (t : V) : Prop := ∃ a U, Ord (memRel V) a ∧ IsL H hP a U ∧ IsEnvOn H U t

include hR in
/-- Two stages lie in a common stage. -/
lemma common_stage {a b U T : V} (ha : Ord (memRel V) a) (hb : Ord (memRel V) b)
    (hU : IsL H hP a U) (hT : IsL H hP b T) :
    ∃ c W, Ord (memRel V) c ∧ IsL H hP c W ∧ (∀ x, x ∈ U → x ∈ W) ∧ (∀ x, x ∈ T → x ∈ W) := by
  rcases trichotomy H hR a ha b hb with h | rfl | h
  · exact ⟨b, T, hb, hT, isL_mono H hR hP hb h hU hT, fun _ hx => hx⟩
  · exact ⟨a, U, ha, hU, fun _ hx => hx, fun _ hx => by rwa [isL_unique H hR hP ha hT hU] at hx⟩
  · exact ⟨a, U, ha, hU, fun _ hx => hx, isL_mono H hR hP ha h hT hU⟩

include hR in
/-- An environment extends by any constructible element. -/
lemma isEnv_econs {t y : V} (ht : IsEnv H hP t) (hy : InL H hP y) :
    IsEnv H hP (econs H y t) := by
  obtain ⟨a, U, ha, hU, htU⟩ := ht
  obtain ⟨b, T, hb, hT, hyT⟩ := hy
  obtain ⟨c, W, hc, hW, hUW, hTW⟩ := common_stage H hR hP ha hb hU hT
  exact ⟨c, W, hc, hW, econs_isEnvOn H ⟨htU.1, fun n z h => hUW z (htU.2 n z h)⟩ (hTW y hyT)⟩

include hR in
/-- A functional environment exists. -/
lemma isEnv_base : ∃ t, IsEnv H hP t ∧
    ∀ x y y', _root_.SetTheory.kpair H x y ∈ t → _root_.SetTheory.kpair H x y' ∈ t → y = y' := by
  obtain ⟨a, S, ha, hS, hd⟩ := SetTheory.BusyBeaver.ZFC.ConstructibleAbs.inL_omega H hR hP
  have he := constEnv_isEnvOn H (A := S) hd
  exact ⟨constEnv H (_root_.SetTheory.omegaV H), ⟨a, S, ha, hS, he⟩, he.1.1⟩

end Math

/-- `t` is an environment over some stage. -/
def envS : SetTheorySemisentence 1 := “t. ∃ a, ∃ U, !ordP a ∧ !stageP a U ∧ !envP U t”

/-! ## The step template -/

/-- The freed premise: `∀y ∀t (¬(Env t ∧ mp2(t, y)) ∨ G₁ y)`. -/
def peelHyp : Sentence GL := ∀⁰ ∀⁰ (∼((lift envS ⇜ ![#0]) ⋏ mp2) ⋎ (G 1 ⇜ ![#1]))

/-- **The peel step**: `∀t (¬(Env t ∧ G₀ t) ∨ ∀y (¬δ(y) ∨ G₁ y))`. -/
def peelG : Sentence GL := peelHyp 🡒 ∀⁰ (∼(lift envS ⋏ G 0) ⋎ relAll)

theorem peelG_provable : templTheory 8 arG ⊢ peelG := by
  apply templ_provable
  intro M _ _ s _ _ _
  haveI : M↓[ℒₛₑₜ] ⊧* (𝗭𝗙 : SetTheory) := pure_models (k := 8) (arities := arG)
  have hR := ConstructibleInterpretation.regular_of_modelsZF (V := M)
  set H := ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M)
  set hP := ConstructibleInterpretation.power_of_modelsZF (V := M)
  simp only [peelG, Semantics.Imp.models_imply]
  intro hq
  simp [models_iff, peelHyp, mp2, G, eq2S, envS, Semiformula.Operator.eq_def,
    eval_stageP (H := H) (hP := hP), eval_envP (H := H)] at hq
  simp [models_iff, relAll, G, envS, ConstructibleInterpretation.eval_domL H hP,
    eval_stageP (H := H) (hP := hP), eval_envP (H := H)]
  intro t
  by_cases hE : IsEnv H hP t
  · by_cases h0 : Structure.rel (L := GL) (placeholderRel 0) ![t]
    · right
      intro y
      by_cases hy : SetTheory.BusyBeaver.ZFC.Constructible.InL H hP y
      · right
        have ft := hE.choose_spec.choose_spec.2.2.1.1
        obtain ⟨a', U', ha', hU', ht'⟩ := isEnv_econs H hR hP hE hy
        rcases hq y (LeanProofs.BoundedZFCConsistency.econs H y t) with (h1 | h1) | h1
        · exact absurd ht' (h1 a' ha' U' hU')
        · rcases h1 t y with h2 | h2 | h2
          · exact absurd rfl h2
          · exact absurd ((LStepExT.eval_econsS _ y t ft).2 rfl) h2
          · exact absurd h0 h2
        · exact h1
      · left; exact hy
    · left; right; exact h0
  · left; left
    intro a ha U hU htU
    exact hE ⟨a, U, ha, hU, htU⟩

/-! ## The closing template -/

abbrev arF : Fin 1 → ℕ := fun _ ↦ 0
abbrev FL := setTemplateLanguage 1 arF

/-- The nullary placeholder. -/
def X0 {n : ℕ} : Semisentence FL n := .rel (placeholderRel (arities := arF) 0) ![]

/-- `∀t (¬(Env t ∧ Fun t) ∨ X) → X`. -/
def finG : Sentence FL := (∀⁰ (∼(lift envS ⋏ lift LMatch.funcS) ⋎ X0)) 🡒 X0

theorem finG_provable : templTheory 1 arF ⊢ finG := by
  apply templ_provable
  intro M _ _ s _ _ _
  haveI : M↓[ℒₛₑₜ] ⊧* (𝗭𝗙 : SetTheory) := pure_models (k := 1) (arities := arF)
  have hR := ConstructibleInterpretation.regular_of_modelsZF (V := M)
  set H := ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M)
  set hP := ConstructibleInterpretation.power_of_modelsZF (V := M)
  simp only [finG, Semantics.Imp.models_imply]
  intro h
  simp [models_iff, X0, envS, eval_stageP (H := H) (hP := hP), eval_envP (H := H),
    LGlueT.eval_funcS H] at h ⊢
  obtain ⟨t, ⟨a, U, ha, hU, htU⟩, hft⟩ := isEnv_base H hR hP
  rcases h t with (h1 | ⟨x, y, hy, y', hy', hne⟩) | h1
  · exact absurd htU (h1 a ha U hU)
  · exact absurd (hft x y y' hy hy') hne
  · exact h1

/-! ## Compiled at internal codes -/

section Typed

open LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping Entailment
open LeanProofs.ZFCinPA.LDriverBase LeanProofs.ZFCinPA.LMatch LeanProofs.ZFCinPA.LGlue1
open LeanProofs.ZFCinPA.LGlue2 LeanProofs.ZFCinPA.LGlue4
open LeanProofs.BoundedPAConsistency.InternalRelativization
open scoped LO.FirstOrder.Arithmetic

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The environment predicate, as a typed code. -/
abbrev EnvT : SF V 1 := ⌜envS⌝

/-- The peel statement `∀t (¬(Env t ∧ M t) ∨ X)`. -/
def PF (M X : SF V 1) : Bootstrapping.Formula V ℒₛₑₜ := ∀⁰ (∼(EnvT ⋏ M) ⋎ X)

/-- The peel statement on codes. -/
def pVal (k x : V) : V := ^∀ (neg ℒₛₑₜ ((EnvT (V := V)).val ^⋏ mVal k) ^⋎ x)

instance pVal_definable : 𝚺₁-Function₂ (pVal : V → V → V) := by
  unfold pVal
  definability

theorem PF_val (M X : SF V 1) :
    (PF M X).val = ^∀ (neg ℒₛₑₜ ((EnvT (V := V)).val ^⋏ M.val) ^⋎ X.val) := by
  simp [PF]

theorem pVal_of_PF {k x : V} (X : SF V 1) (hX : X.val = x)
    (h : (𝗭𝗙 : SetTheory).internalize V ⊢ PF (MT k) X) :
    Bootstrapping.Provable (𝗭𝗙 : SetTheory) (pVal k x) := by
  have := Bootstrapping.tprovable_iff_provable.mp h
  rwa [PF_val, hX] at this

theorem PF_of_pVal {k x : V} (X : SF V 1) (hX : X.val = x)
    (h : Bootstrapping.Provable (𝗭𝗙 : SetTheory) (pVal k x)) :
    (𝗭𝗙 : SetTheory).internalize V ⊢ PF (MT k) X :=
  Bootstrapping.tprovable_iff_provable.mpr (by rw [PF_val, hX]; exact h)

/-- The freed premise of a peel step, before generalization. -/
def QXE (M R : SF V 1) : SF V 1 :=
  ∀⁰ (∼(EnvT.subst (fun _ ↦ Bootstrapping.Semiterm.bvar 0) ⋏ MP2 M) ⋎
    R.subst (fun _ ↦ Bootstrapping.Semiterm.bvar 1))

theorem QXE_free (M R : SF V 1) :
    (QXE M R).free = PF (MpT M.shift zT) (lift1 R.free) := by
  simp [QXE, PF, MP2, MpT, Bootstrapping.Semiformula.free, Bootstrapping.Semiformula.shift_substs,
    Bootstrapping.Semiformula.substs_substs, shift_quoteT, Bootstrapping.Semiformula.imp_def,
    leaf_eq, leaf_econs]
  refine ⟨?_, ?_⟩
  · congr 1
    funext i
    match i with
    | 0 => exact W4_1
  · apply Bootstrapping.Semiformula.ext
    simp [lift1, q_one, Bootstrapping.SemitermVec.val, Matrix.vecHead, Matrix.vecTail]

section Tr

variable (Ks : (i : Fin 8) → SF V (arG i))

theorem tr_peelHyp : translateFormula Ks (Rewriting.emb peelHyp) = ∀⁰ QXE (Ks 0) (Ks 1) := by
  simp [peelHyp, mp2, G, translateFormula, QXE, MP2, eqT4, econsT4,
    Bootstrapping.Semiformula.imp_def]

theorem tr_peelConcl :
    translateFormula Ks (Rewriting.emb (∀⁰ (∼(lift envS ⋏ G 0) ⋎ relAll) : Sentence GL)) =
      PF (Ks 0) (RAllT (Ks 1)) := by
  simp [PF, G, translateFormula, relAll, RAllT]

end Tr

lemma shift_qqAlls {body : V} (hb : IsUFormula ℒₛₑₜ body) (count : V) :
    shift ℒₛₑₜ (qqAlls body count) = qqAlls (shift ℒₛₑₜ body) count :=
  OpenedClosure.shift_qqAlls hb count

/-- **One peel step**: the freed statement at `k + 1` matched variables gives
the relativized universal at `k`. -/
theorem peel_step {k p : V} (hp : IsSemiformula ℒₛₑₜ 1 p)
    (ih : Bootstrapping.Provable (𝗭𝗙 : SetTheory) (pVal (k + 1) (rel (free ℒₛₑₜ p)))) :
    Bootstrapping.Provable (𝗭𝗙 : SetTheory) (pVal k (rel (^∀ p))) := by
  have t := PF_of_pVal (k := k + 1) (lift1 (RF hp le_rfl).free)
    (by simp [lift1, RF, rel, relativize_free hdL hdLs hp]) ih
  rw [MT_succ, ← QXE_free] at t
  have hq := Bootstrapping.TProof.all! t
  have hc := compiledG peelG_provable (K8 (MT k) (RF hp le_rfl) ⊤ ⊤ ⊤ ⊤ ⊤ ⊤)
  rw [peelG, LogicalConnective.HomClass.map_imply, translateFormula_imp, tr_peelHyp,
    tr_peelConcl] at hc
  exact pVal_of_PF _ (rAllT_val _ rfl hp.isUFormula) (hc ⨀ hq)

/-- Freeing the first binder of an opened closure opens one more variable. -/
theorem free_subst_qVec_fvarVec {k B : V} (hB : IsSemiformula ℒₛₑₜ (k + 1) B)
    (hs : shift ℒₛₑₜ B = B) :
    free ℒₛₑₜ (subst ℒₛₑₜ (qVec ℒₛₑₜ (fvarVec k)) B) = subst ℒₛₑₜ (fvarVec (k + 1)) B :=
  OpenedClosure.free_subst_qVec_fvarVec hB hs

/-- **The peel**: the statement for the opened body gives the statement for
the closure, at zero matched variables. -/
theorem peel {m b : V} (hb : IsSemiformula ℒₛₑₜ m b) (hs : shift ℒₛₑₜ b = b)
    (base : Bootstrapping.Provable (𝗭𝗙 : SetTheory) (pVal m (rel (subst ℒₛₑₜ (fvarVec m) b)))) :
    Bootstrapping.Provable (𝗭𝗙 : SetTheory) (pVal 0 (rel (qqAlls b m))) := by
  have key : ∀ i : V, i ≤ m → Bootstrapping.Provable (𝗭𝗙 : SetTheory)
      (pVal (m - i) (rel (subst ℒₛₑₜ (fvarVec (m - i)) (qqAlls b i)))) := by
    intro i
    induction i using ISigma1.sigma1_succ_induction
    · definability
    case zero => intro _; simpa using base
    case succ i ih =>
      intro hi
      obtain ⟨k, rfl⟩ : ∃ k, m = k + (i + 1) := ⟨m - (i + 1), (tsub_add_cancel_of_le hi).symm⟩
      have e1 : k + (i + 1) - i = k + 1 := by rw [add_comm i 1, ← add_assoc, add_tsub_cancel_right]
      have ih' := ih (le_trans (by simp) hi)
      rw [e1] at ih'
      rw [add_tsub_cancel_right]
      have hB : IsSemiformula ℒₛₑₜ (k + 1) (qqAlls b i) :=
        IsSemiformula.qqAlls (by rwa [add_assoc, add_comm 1 i])
      have hBs : shift ℒₛₑₜ (qqAlls b i) = qqAlls b i := by
        rw [shift_qqAlls hb.isUFormula, hs]
      have hf := ModelCodedBindFree.fvarVec_isTermVec (L := ℒₛₑₜ) (V := V) k
      have hw : IsSemitermVec ℒₛₑₜ (k + 1) 1 (qVec ℒₛₑₜ (fvarVec k)) := by simpa using hf.qVec
      rw [qqAlls_succ, substs_all hB.isUFormula]
      apply peel_step (hB.subst hw)
      rw [free_subst_qVec_fvarVec hB hBs]
      exact ih'
  have h := key m le_rfl
  rw [tsub_self] at h
  have hc : IsSemiformula ℒₛₑₜ 0 (qqAlls b m) := IsSemiformula.qqAlls (by simpa using hb)
  rwa [subst_eq_self hc (ModelCodedBindFree.fvarVec_isTermVec (L := ℒₛₑₜ) 0) (by simp)] at h

@[simp] theorem tr_liftF (Ks : (i : Fin 1) → SF V (arF i)) {n : ℕ} (σ : SetTheorySemisentence n) :
    translateFormula Ks (Rewriting.emb (lift σ : Semisentence FL n)) = ⌜σ⌝ :=
  translateFormula_emb_liftSet Ks σ

/-- **The close**: a functional environment exists, so the statement at zero
matched variables proves its conclusion. -/
theorem peel_close {x : V} (hx : IsFormula ℒₛₑₜ x)
    (h : Bootstrapping.Provable (𝗭𝗙 : SetTheory) (pVal 0 x)) :
    Bootstrapping.Provable (𝗭𝗙 : SetTheory) x := by
  let X : Bootstrapping.Formula V ℒₛₑₜ := ⟨x, by simpa using hx⟩
  have t := PF_of_pVal (k := 0) (lift1 X) rfl h
  have hc := compileT_provable (fun _ ↦ Nat.zero_le _) (fun _ : Fin 1 ↦ X) finG_provable
  rw [finG, LogicalConnective.HomClass.map_imply, translateFormula_imp] at hc
  have hsub : ∀ {n : ℕ} (w : Bootstrapping.SemitermVec V ℒₛₑₜ 0 n), subst ℒₛₑₜ w.val x = x :=
    fun w ↦ subst_eq_self (by simpa using hx)
      (IsSemitermVec.iff.mpr ⟨by simpa using w.isSemitermVec.lh, fun i hi ↦ by simp at hi⟩) (by simp)
  have e1 : translateFormula (fun _ : Fin 1 ↦ X)
      (Rewriting.emb (∀⁰ (∼(lift envS ⋏ lift LMatch.funcS) ⋎ X0) : Sentence FL)) =
        PF (MT 0) (lift1 X) := by
    apply Bootstrapping.Semiformula.ext
    simp [PF, X0, translateFormula, lift1, MT, fT, X]
    show (Bootstrapping.Semiformula.subst _ X).val = x
    simp only [Bootstrapping.Semiformula.val_substs]
    exact hsub _
  have e2 : translateFormula (fun _ : Fin 1 ↦ X) (Rewriting.emb (X0 : Sentence FL)) = X := by
    change X.subst _ = X
    exact Bootstrapping.Semiformula.subst_nil_eq_self _ _
  rw [e1, e2] at hc
  exact Bootstrapping.tprovable_iff_provable.mp (hc ⨀ t)

end Typed

end LeanProofs.ZFCinPA.LPeel
