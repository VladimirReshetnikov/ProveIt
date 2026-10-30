import ZFCinPA.LClosure

set_option autoImplicit false
noncomputable section

/-!
# The final separation template of the reflection generator

If `F₅` is a total reflection function for `P₄` (`totS F₅ ⋏ reflS P₄ F₅`), then
`L` satisfies separation for `P₄` read at extended environments:

`∀ t (environment over a stage) ∀ x ∈ L ∃ s ∈ L ∀ z ∈ L (z ∈ s ↔ z ∈ x ∧ P₄ (econs z t))`.

Proof (`sep_final`): choose a limit `β` closed under `F₅` above the stages of
`t` and `x` (`LClosure.closure_point`), let `c` reflect `P₄` at `β`; the set
`D = {z ∈ L_β | (L_β, ∈) ⊨ c[econs z t]}` is definable over `L_β`, hence
constructible (`inL_of_definable`), and `s = x ∩ D` is constructible by
separation in `L` (`inL_sep`). For `z ∈ x ⊆ L_β`, `econs z t` is an
environment over an earlier stage, so `z ∈ D ↔ P₄ (econs z t)`.
-/

namespace LeanProofs.ZFCinPA.LFinalSep

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA LeanProofs.ZFCinPA.SetPlaceholders LeanProofs.ZFCinPA.LTemplate
open LeanProofs.ZFCinPA.EnvTransform LeanProofs.ZFCinPA.LPieces LeanProofs.ZFCinPA.LInvariant
open LeanProofs.ZFCinPA.LStepAnd LeanProofs.ZFCinPA.LStepEx LeanProofs.ZFCinPA.LClosure
open LeanProofs.ZFCinPA.ConstructibleInterpretation (domL)

local instance : Language.Mem L6 := ⟨Sum.inl Language.Set.Rel.mem⟩

section Math

open SetTheory.BusyBeaver.ZFC.InternalOrd SetTheory.BusyBeaver.ZFC.Constructible
  SetTheory.BusyBeaver.ZFC.ConstructibleDef SetTheory.BusyBeaver.ZFC.ConstructibleZF
  LeanProofs.BoundedZFCConsistency

variable {V : Type*} [SetStructure V] (H : _root_.SetTheory.ZFAxioms (memRel V))
  (hR : Regular (memRel V))
  (hP : ∀ a, ∃ p, ∀ x, memRel V x p ↔ _root_.SetTheory.Sub (memRel V) x a)

include hR in
/-- **Separation in `L` for a reflected predicate.** -/
theorem sep_final {P : V → Prop} {F : V → V → Prop} (hrefl : Refl H hP P F)
    (hcp : ∀ α, Ord (memRel V) α →
      ∃ β, IsLim (memRel V) β ∧ α ∈ β ∧ ∀ a, a ∈ β → ∀ g, F a g → g ∈ β)
    (hsepD : ∀ S R c t X : V, (∀ x z z', _root_.SetTheory.kpair H x z ∈ t →
        _root_.SetTheory.kpair H x z' ∈ t → z = z') →
      ∃ D : V, ∀ z, z ∈ D ↔ z ∈ X ∧ SatIn H S R c (econs H z t))
    {t a U : V} (ha : Ord (memRel V) a) (hU : IsL H hP a U) (ht : IsEnvOn H U t)
    {x : V} (hx : InL H hP x) :
    ∃ s, InL H hP s ∧ ∀ z, InL H hP z → (z ∈ s ↔ z ∈ x ∧ P (econs H z t)) := by
  obtain ⟨αx, Sx, hαx, hSx, hxSx⟩ := hx
  have hmo : Ord (memRel V) (_root_.SetTheory.vcup H a αx) := by
    rcases vcup_ord H hR ha hαx with h | h <;> rw [h] <;> assumption
  obtain ⟨β, hβ, hαβ, hcl⟩ := hcp _ hmo
  have haβ : a ∈ β := mem_of_sub_mem H hR hβ.1 hαβ ha
    fun z hz => (_root_.SetTheory.vcup_spec H _ _ z).2 (Or.inl hz)
  have hαxβ : αx ∈ β := mem_of_sub_mem H hR hβ.1 hαβ hαx
    fun z hz => (_root_.SetTheory.vcup_spec H _ _ z).2 (Or.inr hz)
  obtain ⟨S, hS⟩ := isL_exists H hR hP hβ.1
  obtain ⟨R, hR'⟩ := memRel_exists H hP S
  obtain ⟨c, hc, hr⟩ := hrefl
  have hr' := hr β hβ hcl S hS R hR'
  have htS : IsEnvOn H S t := envOn_stage H hR hP hβ hS haβ hU ht
  obtain ⟨D, hD⟩ := hsepD S R c t S ht.1.1
  have hDL : InL H hP D :=
    inL_of_definable H hR hP hβ.1 hS (fun y hy => ((hD y).1 hy).1) ⟨R, c, t, hR', hc, htS, hD⟩
  have hxS : ∀ z, z ∈ x → z ∈ S := fun z hz =>
    isL_trans H hR hP hβ.1 hS x (isL_mono H hR hP hβ.1 hαxβ hSx hS x hxSx) z hz
  obtain ⟨s, hsL, hs⟩ := inL_sep H hR hP (_root_.SetTheory.Form.fMem 0 1) (fun _ => D) (fun _ => hDL)
    ⟨αx, Sx, hαx, hSx, hxSx⟩
  refine ⟨s, hsL, fun z _ => ?_⟩
  refine (hs z).trans ?_
  change z ∈ x ∧ z ∈ D ↔ _
  refine and_congr_right fun hzx => ?_
  obtain ⟨a₂, ha₂, U₂, hU₂, hte⟩ := econs_earlier H hR hP hβ hS haβ hU ht (hxS z hzx)
  rw [hD z, hr' a₂ ha₂ U₂ hU₂ _ hte]
  exact ⟨fun h => h.2, fun h => ⟨hxS z hzx, h⟩⟩

end Math

/-! ## The template -/

/-- `L`-separation for `P₄` at extended environments. -/
def sepEnvS : Sentence L6 :=
  “∀ t, (∃ a, ∃ U, !(lift ordP) a ∧ !(lift stageP) a U ∧ !(lift envP) U t) →
    ∀ x, !(lift domL) x → ∃ s, !(lift domL) s ∧
      ∀ z, !(lift domL) z → (z ∈ s ↔ z ∈ x ∧ ∃ e, !(lift econsS) e z t ∧ !P₄ e)”

/-- **The final separation template.** -/
def sepTemplate : Sentence L6 := (totS F₅ ⋏ reflS P₄ F₅) 🡒 sepEnvS

/-- The matrix of the definable set `D` (`z`, then `S`, `R`, `c`, `t`). -/
def satSepS : Semisentence L6 5 := “z S R c t. ∃ e, !(lift econsS) e z t ∧ !(lift satP) S R c e”

section Readings

open SetTheory.BusyBeaver.ZFC.InternalOrd SetTheory.BusyBeaver.ZFC.Constructible
  LeanProofs.BoundedZFCConsistency

variable {M : Type} [Nonempty M] [SetStructure M] [Structure L6 M] [Structure.Eq L6 M]
  [Structure.Mem L6 M] [M↓[ℒₛₑₜ] ⊧* (𝗭𝗙 : SetTheory)]

local notation "HM" => ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M)
local notation "hPM" => ConstructibleInterpretation.power_of_modelsZF (V := M)

theorem models_sepEnvS :
    M↓[L6] ⊧ sepEnvS ↔ ∀ t a : M, Ord (memRel M) a → ∀ U, IsL HM hPM a U → IsEnvOn HM U t →
      ∀ x, InL HM hPM x → ∃ s, InL HM hPM s ∧ ∀ z, InL HM hPM z →
        (z ∈ s ↔ z ∈ x ∧ ∃ e, econsS.Eval ![e, z, t] Empty.elim ∧ P₄.Eval ![e] Empty.elim) := by
  simp [models_iff, sepEnvS, eval_stageP (H := HM) (hP := hPM), eval_envP (H := HM),
    ConstructibleInterpretation.eval_domL HM hPM]

theorem eval_satSepS (z S R c t : M)
    (hfun : ∀ x y y', _root_.SetTheory.kpair HM x y ∈ t → _root_.SetTheory.kpair HM x y' ∈ t → y = y') :
    satSepS.Eval ![z, S, R, c, t] Empty.elim ↔ SatIn HM S R c (econs HM z t) := by
  simp [satSepS, eval_satP (H := HM), fun e y => LStepExT.eval_econsS e y t hfun]

end Readings

/-- **The final separation template is a theorem of the template theory.** -/
theorem sepTemplate_provable : templTheory 6 ar6 ⊢ sepTemplate := by
  apply templ_provable
  intro M _ _ s _ _ _
  haveI : M↓[ℒₛₑₜ] ⊧* (𝗭𝗙 : SetTheory) := pure_models (k := 6) (arities := ar6)
  have hR := ConstructibleInterpretation.regular_of_modelsZF (V := M)
  set H := ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M)
  set hP := ConstructibleInterpretation.power_of_modelsZF (V := M)
  simp only [sepTemplate, Semantics.Imp.models_imply, Semantics.And.models_and]
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
      ((Rewriting.emb satSepS : Semiproposition L6 5) ⇜ ![#0, &0, &1, &2, &3])
      (fun i => if i = 0 then S else if i = 1 then R else if i = 2 then c else t) X
    refine ⟨D, fun z => (hD z).trans (and_congr_right fun _ => ?_)⟩
    rw [← eval_satSepS z S R c t hfun]
    simp only [Semiformula.eval_substs, Semiformula.eval_emb]
    apply iff_of_eq
    congr 2
    funext ⟨i, hi⟩
    rcases i with _ | _ | _ | _ | _ | i
    all_goals first | rfl | (exfalso; omega)
  rw [models_sepEnvS]
  intro t a ha U hU ht x hx
  obtain ⟨s', hsL, hs⟩ := sep_final H hR hP hrefl hcp hsepD ha hU ht hx
  refine ⟨s', hsL, fun z hz => (hs z hz).trans (and_congr_right fun _ => ?_)⟩
  simp [fun e y => LStepExT.eval_econsS e y t ht.1.1]

end LeanProofs.ZFCinPA.LFinalSep
