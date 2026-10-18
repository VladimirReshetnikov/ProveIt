import ZFCinPA.LFinalSep

set_option autoImplicit false
noncomputable section

/-!
# The final replacement template of the reflection generator

If `F₅` is a total reflection function for `P₄` (`totS F₅ ⋏ reflS P₄ F₅`), then
`L` satisfies replacement for `P₄` read at doubly extended environments
`econs x (econs y t)` (the slot order of a replacement matrix `ψ x y`):

`∀ t (environment over a stage), (∀ x ∈ L ∃! y ∈ L, P₄(x :: y :: t)) →
  ∀ X ∈ L ∃ Y ∈ L ∀ y ∈ L (y ∈ Y ↔ ∃ x ∈ L (x ∈ X ∧ P₄(x :: y :: t)))`.

Proof (`repl_final`): the image `B` exists in `V` (replacement for the
totalized relation, `repl_iff`) and lies in one stage `L_γ` (`stage_bound`).
Choose a limit `β` closed under `F₅` above `γ`, the stage of `t` and the
stage of `X`, and let `c` reflect `P₄` at `β`. The set
`D = {y ∈ L_β | (L_β, ∈) ⊨ ∃x (x ∈ v_m ∧ c)[y :: t']}` is definable over
`L_β`, hence constructible. Here `t'` agrees with `t` below a support bound
`n` of `c` (`SatSupport.sat_support`) and carries `X` at slot `n`
(`env_patch`), and `m = n + 2`, so that the code `c` cannot see the patched
slot. No code-level shift of `c` is needed.
-/

namespace LeanProofs.ZFCinPA.LFinalRepl

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA LeanProofs.ZFCinPA.SetPlaceholders LeanProofs.ZFCinPA.LTemplate
open LeanProofs.ZFCinPA.EnvTransform LeanProofs.ZFCinPA.LPieces LeanProofs.ZFCinPA.LInvariant
open LeanProofs.ZFCinPA.LStepAnd LeanProofs.ZFCinPA.LStepEx LeanProofs.ZFCinPA.LClosure
open LeanProofs.ZFCinPA.ConstructibleInterpretation (domL)

local instance : Language.Mem L6 := ⟨Sum.inl Language.Set.Rel.mem⟩

section Math

open SetTheory.BusyBeaver.ZFC.InternalOrd SetTheory.BusyBeaver.ZFC.Constructible
  SetTheory.BusyBeaver.ZFC.ConstructibleDef SetTheory.BusyBeaver.ZFC.ConstructibleZF
  SetTheory.BusyBeaver.ZFC.NamedZF SetTheory.BusyBeaver.ZFC.InternalRank
  LeanProofs.BoundedZFCConsistency

variable {V : Type*} [SetStructure V] (H : _root_.SetTheory.ZFAxioms (memRel V))
  (hR : Regular (memRel V))
  (hP : ∀ a, ∃ p, ∀ x, memRel V x p ↔ _root_.SetTheory.Sub (memRel V) x a)

include hR hP in
/-- **Patching an environment**: an environment on `S` that agrees with `t`
below `n` and carries `X` at slot `n`. -/
theorem env_patch {S t n X : V} (ht : IsEnvOn H S t) (hn : n ∈ _root_.SetTheory.omegaV H)
    (hX : X ∈ S) :
    ∃ e, IsEnvOn H S e ∧ SetTheory.BusyBeaver.ZFC.SatSupport.AgreeP H n e t ∧
      _root_.SetTheory.kpair H n X ∈ e := by
  obtain ⟨C, hC⟩ := SetTheory.BusyBeaver.ZFC.InternalWO.prod_exists H hP
    (_root_.SetTheory.omegaV H) S
  obtain ⟨e, he⟩ := sep_of H (fun p => ∃ i y, p = _root_.SetTheory.kpair H i y ∧
      ((i ∈ n ∧ p ∈ t) ∨ (i ∉ n ∧ y = X)))
    (.ex 4 (.ex 5 (.and (kpairF 0 4 5) (.or (.and (.mem 4 1) (.mem 0 2))
      (.and (.neg (.mem 4 1)) (.eq 5 3))))))
    (fun i => if i = 1 then n else if i = 2 then t else X) (fun p => by
      simp only [NSat, nsat_neg, nsat_kpairF H]
      simp (disch := omega) only [upd_same, upd_other]
      rfl) C
  have hval : ∀ i y, _root_.SetTheory.kpair H i y ∈ e →
      (i ∈ n ∧ _root_.SetTheory.kpair H i y ∈ t) ∨ (i ∉ n ∧ y = X) := fun i y h => by
    obtain ⟨-, i', y', e', hc⟩ := (he _).1 h
    obtain ⟨rfl, rfl⟩ := _root_.SetTheory.kpair_inj H _ _ _ _ e'
    exact hc
  have hin : ∀ i y, i ∈ _root_.SetTheory.omegaV H → y ∈ S →
      ((i ∈ n ∧ _root_.SetTheory.kpair H i y ∈ t) ∨ (i ∉ n ∧ y = X)) →
      _root_.SetTheory.kpair H i y ∈ e := fun i y hi hy hc =>
    (he _).2 ⟨(hC _).2 ⟨i, y, hi, hy, rfl⟩, i, y, rfl, hc⟩
  refine ⟨e, ⟨⟨fun i y y' h h' => ?_, fun i hi => ?_, fun p hp => ?_⟩, fun i y h => ?_⟩,
    fun i u u' hi hu hu' => ?_, hin n X hn hX (Or.inr ⟨mem_irrefl H hR n, rfl⟩)⟩
  · rcases hval i y h with ⟨hi, h1⟩ | ⟨hi, rfl⟩ <;>
      rcases hval i y' h' with ⟨hi', h2⟩ | ⟨hi', rfl⟩
    · exact ht.1.1 i y y' h1 h2
    · exact absurd hi hi'
    · exact absurd hi' hi
    · rfl
  · by_cases hin' : i ∈ n
    · obtain ⟨u, hu⟩ := ht.1.2.1 i hi
      exact ⟨u, hin i u hi (ht.2 i u hu) (Or.inl ⟨hin', hu⟩)⟩
    · exact ⟨X, hin i X hi hX (Or.inr ⟨hin', rfl⟩)⟩
  · obtain ⟨hpC, -⟩ := (he p).1 hp
    obtain ⟨i, y, hi, -, rfl⟩ := (hC p).1 hpC
    exact ⟨i, y, hi, rfl⟩
  · obtain ⟨hpC, -⟩ := (he _).1 h
    obtain ⟨i', y', -, hy', e'⟩ := (hC _).1 hpC
    rw [(_root_.SetTheory.kpair_inj H _ _ _ _ e').2]; exact hy'
  · rcases hval i u hu with ⟨-, h1⟩ | ⟨h, -⟩
    · exact ht.1.1 i u u' h1 hu'
    · exact absurd hi h

include hR in
/-- **Replacement in `L` for a reflected predicate.** -/
theorem repl_final {P : V → Prop} {F : V → V → Prop} (hrefl : Refl H hP P F)
    (hcp : ∀ α, Ord (memRel V) α →
      ∃ β, IsLim (memRel V) β ∧ α ∈ β ∧ ∀ a, a ∈ β → ∀ g, F a g → g ∈ β)
    (hsepD : ∀ S R c t X : V, (∀ x z z', _root_.SetTheory.kpair H x z ∈ t →
        _root_.SetTheory.kpair H x z' ∈ t → z = z') →
      ∃ D : V, ∀ z, z ∈ D ↔ z ∈ X ∧ SatIn H S R c (econs H z t))
    {t a U X : V} (ha : Ord (memRel V) a) (hU : IsL H hP a U) (ht : IsEnvOn H U t)
    (hX : InL H hP X)
    (hImg : ∃ B : V, ∀ y, y ∈ B ↔ ∃ x, x ∈ X ∧ InL H hP y ∧ P (econs H x (econs H y t))) :
    ∃ Y, InL H hP Y ∧ ∀ y, InL H hP y →
      (y ∈ Y ↔ ∃ x, InL H hP x ∧ x ∈ X ∧ P (econs H x (econs H y t))) := by
  obtain ⟨B, hB⟩ := hImg
  obtain ⟨γ, T, hγ, hT, hBT⟩ := stage_bound H hR hP (A := B) fun y hy => by
    obtain ⟨x, -, h, -⟩ := (hB y).1 hy
    exact h
  have hXL := hX
  obtain ⟨αx, Sx, hαx, hSx, hXSx⟩ := hX
  have hmax : ∀ g₁ g₂ : V, Ord (memRel V) g₁ → Ord (memRel V) g₂ → ∃ g, Ord (memRel V) g ∧
      (∀ z, z ∈ g₁ → z ∈ g) ∧ (∀ z, z ∈ g₂ → z ∈ g) := fun g₁ g₂ h₁ h₂ =>
    ⟨_root_.SetTheory.vcup H g₁ g₂,
      by rcases vcup_ord H hR h₁ h₂ with h | h <;> rw [h] <;> assumption,
      fun z hz => (_root_.SetTheory.vcup_spec H _ _ z).2 (Or.inl hz),
      fun z hz => (_root_.SetTheory.vcup_spec H _ _ z).2 (Or.inr hz)⟩
  obtain ⟨μ₁, hμ₁, h1a, h1x⟩ := hmax a αx ha hαx
  obtain ⟨μ, hμ, h2, h2γ⟩ := hmax μ₁ γ hμ₁ hγ
  obtain ⟨β, hβ, hμβ, hcl⟩ := hcp μ hμ
  have haβ : a ∈ β := mem_of_sub_mem H hR hβ.1 hμβ ha fun z hz => h2 z (h1a z hz)
  have hαxβ : αx ∈ β := mem_of_sub_mem H hR hβ.1 hμβ hαx fun z hz => h2 z (h1x z hz)
  have hγβ : γ ∈ β := mem_of_sub_mem H hR hβ.1 hμβ hγ h2γ
  obtain ⟨S, hS⟩ := isL_exists H hR hP hβ.1
  obtain ⟨R, hR'⟩ := memRel_exists H hP S
  obtain ⟨c, hc, hr⟩ := hrefl
  have hr' := hr β hβ hcl S hS R hR'
  have hSS := isSetStructure_stage H hR hP hβ hS hR'
  have htS : IsEnvOn H S t := envOn_stage H hR hP hβ hS haβ hU ht
  have hXS : X ∈ S := isL_mono H hR hP hβ.1 hαxβ hSx hS X hXSx
  have hXsub : ∀ x, x ∈ X → x ∈ S := fun x hx => isL_trans H hR hP hβ.1 hS X hXS x hx
  have hBS : ∀ y, y ∈ B → y ∈ S := fun y hy => isL_mono H hR hP hβ.1 hγβ hT hS y (hBT y hy)
  obtain ⟨n, hn, hsup⟩ := SetTheory.BusyBeaver.ZFC.SatSupport.sat_support H hSS c hc
  obtain ⟨t', ht'S, hag, hXt'⟩ := env_patch H hR hP htS hn hXS
  -- the code `∃x (x ∈ v_m ∧ c)` with `m = n + 2`
  have hn1 := _root_.SetTheory.omega_succ H n hn
  have hm := _root_.SetTheory.omega_succ H _ hn1
  have h0 := _root_.SetTheory.vempty_in_omega H
  have hatom := isFormCodeSem_memAtom H h0 hm
  have hand := isFormCodeSem_and H hatom hc
  have hc' := isFormCodeSem_ex H hand
  -- reading the code at `y :: t'`
  have hread : ∀ y, y ∈ S → (SatIn H S R (_root_.SetTheory.kpair H (natV H 7)
      (_root_.SetTheory.kpair H (natV H 4) (_root_.SetTheory.kpair H
        (_root_.SetTheory.kpair H (natV H 0) (_root_.SetTheory.kpair H (_root_.SetTheory.vempty H)
          (_root_.SetTheory.vsucc H (_root_.SetTheory.vsucc H n)))) c))) (econs H y t') ↔
      ∃ x, x ∈ S ∧ x ∈ X ∧ SatIn H S R c (econs H x (econs H y t))) := by
    intro y hy
    have hyt' := econs_isEnvOn H ht'S hy
    have hyt := econs_isEnvOn H htS hy
    rw [satIn_ex H hSS hand hyt']
    refine exists_congr fun x => and_congr_right fun hx => ?_
    have hxyt' := econs_isEnvOn H hyt' hx
    have hxyt := econs_isEnvOn H hyt hx
    rw [satIn_and H hSS hatom hc hxyt', satIn_memAtom H hSS h0 hm hxyt']
    have e0 : applyV H (econs H x (econs H y t')) (_root_.SetTheory.vempty H) = x :=
      econs_zero H hyt'.1.1 x
    have em : applyV H (econs H x (econs H y t'))
        (_root_.SetTheory.vsucc H (_root_.SetTheory.vsucc H n)) = X := by
      rw [econs_succ H hyt' x hn1, econs_succ H ht'S y hn]
      exact applyV_eq H ht'S.1.1 hXt'
    rw [e0, em]
    refine and_congr ?_ ?_
    · constructor
      · intro h
        obtain ⟨u, v, -, -, huv, e⟩ := (hR' _).1 h
        obtain ⟨rfl, rfl⟩ := _root_.SetTheory.kpair_inj H _ _ _ _ e
        exact huv
      · intro h
        exact (hR' _).2 ⟨x, X, hx, hXS, h, rfl⟩
    · exact hsup _ _ hxyt' hxyt
        (SetTheory.BusyBeaver.ZFC.SatSupport.agreeP_econs H hn hyt' hyt hx
          (SetTheory.BusyBeaver.ZFC.SatSupport.agreeP_econs H hn ht'S htS hy hag))
  -- reflection at doubly extended environments
  have hPc : ∀ x y, x ∈ S → y ∈ S →
      (P (econs H x (econs H y t)) ↔ SatIn H S R c (econs H x (econs H y t))) := by
    intro x y hx hy
    obtain ⟨a₁, ha₁, U₁, hU₁, ht₁⟩ := econs_earlier H hR hP hβ hS haβ hU ht hy
    obtain ⟨a₂, ha₂, U₂, hU₂, ht₂⟩ := econs_earlier H hR hP hβ hS ha₁ hU₁ ht₁ hx
    exact hr' a₂ ha₂ U₂ hU₂ _ ht₂
  obtain ⟨D, hD⟩ := hsepD S R _ t' S ht'S.1.1
  have hDL : InL H hP D :=
    inL_of_definable H hR hP hβ.1 hS (fun y hy => ((hD y).1 hy).1) ⟨R, _, t', hR', hc', ht'S, hD⟩
  refine ⟨D, hDL, fun y hyL => ?_⟩
  rw [hD y]
  constructor
  · rintro ⟨hyS, h⟩
    obtain ⟨x, hxS, hxX, hsat⟩ := (hread y hyS).1 h
    exact ⟨x, inL_trans H hR hP hXL hxX, hxX, (hPc x y hxS hyS).2 hsat⟩
  · rintro ⟨x, -, hxX, hPx⟩
    have hyS : y ∈ S := hBS y ((hB y).2 ⟨x, hxX, hyL, hPx⟩)
    have hxS := hXsub x hxX
    exact ⟨hyS, (hread y hyS).2 ⟨x, hxS, hxX, (hPc x y hxS hyS).1 hPx⟩⟩

end Math

/-! ## The template -/

/-- Equality, as a closed `ℒₛₑₜ` semisentence. -/
def eqS : SetTheorySemisentence 2 := “x y. x = y”

/-- `P₄` at the doubly extended environment `x :: y :: t`. -/
def appS : Semisentence L6 3 :=
  “x y t. ∃ e₁, ∃ e, !(lift econsS) e₁ y t ∧ !(lift econsS) e x e₁ ∧ !P₄ e”

/-- `L`-replacement for `P₄` at doubly extended environments. -/
def replEnvS : Sentence L6 :=
  “∀ t, (∃ a, ∃ U, !(lift ordP) a ∧ !(lift stageP) a U ∧ !(lift envP) U t) →
    (∀ x, !(lift domL) x → ∃ y, !(lift domL) y ∧ !appS x y t ∧
      ∀ y', !(lift domL) y' → !appS x y' t → !(lift eqS) y' y) →
    ∀ X, !(lift domL) X → ∃ Y, !(lift domL) Y ∧
      ∀ y, !(lift domL) y → (y ∈ Y ↔ ∃ x, !(lift domL) x ∧ x ∈ X ∧ !appS x y t)”

/-- **The final replacement template.** -/
def replTemplate : Sentence L6 := (totS F₅ ⋏ reflS P₄ F₅) 🡒 replEnvS

/-- The relation `appS`, totalized by `∅` off `L`. -/
def totAppS : Semisentence L6 3 :=
  “x y t. (!(lift domL) x ∧ !(lift domL) y ∧ !appS x y t) ∨ (¬!(lift domL) x ∧ ∀ w, w ∉ y)”

section Readings

open SetTheory.BusyBeaver.ZFC.InternalOrd SetTheory.BusyBeaver.ZFC.Constructible
  LeanProofs.BoundedZFCConsistency

variable {M : Type} [Nonempty M] [SetStructure M] [Structure L6 M] [Structure.Eq L6 M]
  [Structure.Mem L6 M] [M↓[ℒₛₑₜ] ⊧* (𝗭𝗙 : SetTheory)]

local notation "HM" => ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M)
local notation "hPM" => ConstructibleInterpretation.power_of_modelsZF (V := M)

theorem eval_appS (x y t : M)
    (hfun : ∀ u v v', _root_.SetTheory.kpair HM u v ∈ t → _root_.SetTheory.kpair HM u v' ∈ t → v = v') :
    appS.Eval ![x, y, t] Empty.elim ↔ P₄.Eval ![econs HM x (econs HM y t)] Empty.elim := by
  have hfun' := econs_functional HM hfun y
  simp [appS, fun e z => LStepExT.eval_econsS e z t hfun,
    fun e z => LStepExT.eval_econsS e z (econs HM y t) hfun']

theorem eval_totAppS (x y t : M) :
    totAppS.Eval ![x, y, t] Empty.elim ↔
      (InL HM hPM x ∧ InL HM hPM y ∧ appS.Eval ![x, y, t] Empty.elim) ∨
        (¬ InL HM hPM x ∧ ∀ w, w ∉ y) := by
  simp [totAppS, ConstructibleInterpretation.eval_domL HM hPM]

theorem models_replEnvS :
    M↓[L6] ⊧ replEnvS ↔ ∀ t a : M, Ord (memRel M) a → ∀ U, IsL HM hPM a U → IsEnvOn HM U t →
      (∀ x, InL HM hPM x → ∃ y, InL HM hPM y ∧ appS.Eval ![x, y, t] Empty.elim ∧
        ∀ y', InL HM hPM y' → appS.Eval ![x, y', t] Empty.elim → y' = y) →
      ∀ X, InL HM hPM X → ∃ Y, InL HM hPM Y ∧ ∀ y, InL HM hPM y →
        (y ∈ Y ↔ ∃ x, InL HM hPM x ∧ x ∈ X ∧ appS.Eval ![x, y, t] Empty.elim) := by
  simp [models_iff, replEnvS, eval_stageP (H := HM) (hP := hPM), eval_envP (H := HM),
    ConstructibleInterpretation.eval_domL HM hPM, eqS]

end Readings

/-- **The final replacement template is a theorem of the template theory.** -/
theorem replTemplate_provable : templTheory 6 ar6 ⊢ replTemplate := by
  apply templ_provable
  intro M _ _ s _ _ _
  haveI : M↓[ℒₛₑₜ] ⊧* (𝗭𝗙 : SetTheory) := pure_models (k := 6) (arities := ar6)
  have hR := ConstructibleInterpretation.regular_of_modelsZF (V := M)
  set H := ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M)
  set hP := ConstructibleInterpretation.power_of_modelsZF (V := M)
  simp only [replTemplate, Semantics.Imp.models_imply, Semantics.And.models_and]
  rintro ⟨htot, hrefl⟩
  rw [models_totS] at htot
  rw [models_reflS] at hrefl
  have hcp := closure_point (M := M) htot
  have hsepD : ∀ S R c t X : M, (∀ x z z', _root_.SetTheory.kpair H x z ∈ t →
      _root_.SetTheory.kpair H x z' ∈ t → z = z') →
      ∃ D : M, ∀ z, z ∈ D ↔ z ∈ X ∧ LeanProofs.BoundedZFCConsistency.SatIn H S R c
        (LeanProofs.BoundedZFCConsistency.econs H z t) := by
    intro S R c t X hfun
    obtain ⟨D, hD⟩ := sep_iff (k := 6) (arities := ar6)
      ((Rewriting.emb LFinalSep.satSepS : Semiproposition L6 5) ⇜ ![#0, &0, &1, &2, &3])
      (fun i => if i = 0 then S else if i = 1 then R else if i = 2 then c else t) X
    refine ⟨D, fun z => (hD z).trans (and_congr_right fun _ => ?_)⟩
    rw [← LFinalSep.eval_satSepS z S R c t hfun]
    simp only [Semiformula.eval_substs, Semiformula.eval_emb]
    apply iff_of_eq
    congr 2
    funext ⟨i, hi⟩
    rcases i with _ | _ | _ | _ | _ | i
    all_goals first | rfl | (exfalso; omega)
  rw [models_replEnvS]
  intro t a ha U hU ht hfun X hX
  have happ : ∀ x y : M, appS.Eval ![x, y, t] Empty.elim ↔
      P₄.Eval ![LeanProofs.BoundedZFCConsistency.econs H x
        (LeanProofs.BoundedZFCConsistency.econs H y t)] Empty.elim :=
    fun x y => eval_appS x y t ht.1.1
  have hImg : ∃ B : M, ∀ y, y ∈ B ↔ ∃ x, x ∈ X ∧
      SetTheory.BusyBeaver.ZFC.Constructible.InL H hP y ∧
      P₄.Eval ![LeanProofs.BoundedZFCConsistency.econs H x
        (LeanProofs.BoundedZFCConsistency.econs H y t)] Empty.elim := by
    have huniq : ∀ x : M, ∃! y, totAppS.Eval ![x, y, t] Empty.elim := by
      intro x
      by_cases hx : SetTheory.BusyBeaver.ZFC.Constructible.InL H hP x
      · obtain ⟨y, hy, hxy, u⟩ := hfun x hx
        refine ⟨y, (eval_totAppS x y t).2 (Or.inl ⟨hx, hy, hxy⟩), fun y' hy' => ?_⟩
        rcases (eval_totAppS x y' t).1 hy' with ⟨-, h1, h2⟩ | ⟨h, -⟩
        · exact u y' h1 h2
        · exact absurd hx h
      · refine ⟨_root_.SetTheory.vempty H, (eval_totAppS x _ t).2
          (Or.inr ⟨hx, fun z => _root_.SetTheory.vempty_spec H z⟩), fun y' hy' => ?_⟩
        rcases (eval_totAppS x y' t).1 hy' with ⟨h, -⟩ | ⟨-, h⟩
        · exact absurd h hx
        · exact (empty_iff y').1 h
    obtain ⟨B, hB⟩ := repl_iff (k := 6) (arities := ar6)
      ((Rewriting.emb totAppS : Semiproposition L6 3) ⇜ ![#0, #1, &0]) (fun _ => t)
      (fun x => by simpa using huniq x) X
    refine ⟨B, fun y => ?_⟩
    have hB' := hB y
    simp only [Rewriting.subst, Semiformula.eval_substs] at hB'
    rw [hB']
    refine exists_congr fun x => ?_
    constructor
    · rintro ⟨hxX, h⟩
      have h' : totAppS.Eval ![x, y, t] Empty.elim := by simpa using h
      rcases (eval_totAppS x y t).1 h' with ⟨-, hy, hxy⟩ | ⟨h, -⟩
      · exact ⟨hxX, hy, (happ x y).1 hxy⟩
      · exact absurd (SetTheory.BusyBeaver.ZFC.Constructible.inL_trans H hR hP hX hxX) h
    · rintro ⟨hxX, hy, hP4⟩
      refine ⟨hxX, ?_⟩
      have h' : totAppS.Eval ![x, y, t] Empty.elim := (eval_totAppS x y t).2
        (Or.inl ⟨SetTheory.BusyBeaver.ZFC.Constructible.inL_trans H hR hP hX hxX, hy,
          (happ x y).2 hP4⟩)
      simpa using h'
  obtain ⟨Y, hYL, hY⟩ := repl_final H hR hP hrefl hcp hsepD ha hU ht hX hImg
  refine ⟨Y, hYL, fun y hy => (hY y hy).trans ?_⟩
  simp only [happ]

end LeanProofs.ZFCinPA.LFinalRepl
