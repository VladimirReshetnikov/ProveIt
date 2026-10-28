import ZFCinPA.NativeInterp

set_option autoImplicit false
noncomputable section

/-!
# The fixed axioms of `𝗭𝗙` under the WF interpretation (`R3`)

In every model `M` of the native theory, the well-founded part of the
bisimulation quotient carries the repository's six-field `ZFAxioms` bundle
(`WFModel.domain_zfAxioms`), power sets (`WFModel.domain_power`) and
regularity (`WellFoundedPart.domain_regular`), and is nonempty. From such a
bundle, any set structure satisfies the equality axioms and the seven fixed
axioms of Foundation's `𝗭𝗙` (`fixed_models`, the pattern of
`ConstructibleInterpretation.L_models`). With `NativeInterp.eval_intF` and
completeness:

* `native_proves_intF`: `nativeTheory ⊢ intF σ` for every `σ ∈ 𝗘𝗤 ∪ zfFixed`;
* `native_proves_domain`: `nativeTheory ⊢ ∃x domS(x)`;

and internally, in every model of `𝗜𝚺₁`, `Provable nativeTheory (interp PN ⌜σ⌝)`
and `Provable nativeTheory (∃ domS)`.
-/

namespace LeanProofs.ZFCinPA.NativeFixed

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA LeanProofs.ZFCinPA.NativeInterp
open SetTheory.BusyBeaver.ZFC

/-- **The fixed axioms from a bundle**: equality axioms and the seven fixed
axioms of `𝗭𝗙` hold in any set structure with the six-field bundle, power
sets and regularity. -/
theorem fixed_models {S : Type} [Nonempty S] [SetStructure S]
    (HL : _root_.SetTheory.ZFAxioms (memRel S))
    (hPow : ∀ x : S, ∃ p : S, ∀ z, z ∈ p ↔ ∀ u, u ∈ z → u ∈ x)
    (hReg : ∀ x : S, (∃ z, z ∈ x) → ∃ m, m ∈ x ∧ ¬∃ z, z ∈ m ∧ z ∈ x)
    (σ : SetTheorySentence) (hσ : σ ∈ 𝗘𝗤 ℒₛₑₜ ∪ zfFixed) : S↓[ℒₛₑₜ] ⊧ σ := by
  rcases hσ with hσ | hσ
  · exact models_of_mem (T := (𝗘𝗤 ℒₛₑₜ : SetTheory)) hσ
  · simp only [zfFixed, Set.mem_insert_iff, Set.mem_singleton_iff] at hσ
    rcases hσ with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · suffices ∃ x : S, ∀ y, y ∉ x by simpa [models_iff, Axiom.empty]
      obtain ⟨_, ⟨e0, -, he0⟩, -⟩ := HL.inf
      exact ⟨e0, he0⟩
    · suffices ∀ x y : S, x = y ↔ ∀ z, z ∈ x ↔ z ∈ y by
        simpa [models_iff, Axiom.extentionality]
      intro x y
      exact ⟨fun h => h ▸ fun _ => Iff.rfl, HL.ext x y⟩
    · suffices ∀ x y : S, ∃ z, ∀ v, v ∈ z ↔ v = x ∨ v = y by
        simpa [models_iff, Axiom.pairing]
      exact HL.pair
    · suffices ∀ x : S, ∃ y, ∀ z, z ∈ y ↔ ∃ v ∈ x, z ∈ v by
        simpa [models_iff, Axiom.union]
      intro x
      obtain ⟨w, hw⟩ := HL.union x
      refine ⟨w, fun z => (hw z).trans ?_⟩
      constructor <;> rintro ⟨v, h1, h2⟩ <;> exact ⟨v, h2, h1⟩
    · suffices ∀ x : S, ∃ y : S, ∀ z : S, z ∈ y ↔ ∀ u : S, u ∈ z → u ∈ x by
        simpa [models_iff, Axiom.power, isSubsetOf]
      exact hPow
    · suffices ∃ ω : S, (∀ e, (∀ z, z ∉ e) → e ∈ ω) ∧
          ∀ x ∈ ω, ∀ y, (∀ z, z ∈ y ↔ z = x ∨ z ∈ x) → y ∈ ω by
        simpa [models_iff, Axiom.infinity, isEmpty, isSucc, Rew.q_subst,
          Semiterm.val_substs, Function.comp_def]
      obtain ⟨I, ⟨e0, he0I, he0⟩, hsucc⟩ := HL.inf
      refine ⟨I, fun e he => ?_, fun x hx y hy => ?_⟩
      · have : e = e0 := HL.ext e e0 fun z =>
          ⟨fun h => absurd h (he z), fun h => absurd h (he0 z)⟩
        rw [this]
        exact he0I
      · obtain ⟨sx, hsxI, hsx⟩ := hsucc x hx
        have : y = sx := HL.ext y sx fun t => by
          rw [hsx t]
          exact (hy t).trans or_comm
        rw [this]
        exact hsxI
    · suffices ∀ x : S, (∃ z, z ∈ x) → ∃ y ∈ x, ∀ z ∈ x, z ∉ y by
        simpa [models_iff, Axiom.foundation, isNonempty]
      intro x hx
      obtain ⟨m, hm, hmin⟩ := hReg x hx
      exact ⟨m, hm, fun z hz hzm => hmin ⟨z, hzm, hz⟩⟩

/-! ## The well-founded part of the quotient -/

section Models

variable {M : Type} [Nonempty M] [SetStructure M] [M↓[ℒₛₑₜ] ⊧* NativeSet.nativeTheory]

instance : Nonempty (WQ M) :=
  WellFoundedPart.quotient_domain_nonempty (memRel M) wM hM

theorem wq_zfAxioms : _root_.SetTheory.ZFAxioms (memRel (WQ M)) :=
  WFModel.domain_zfAxioms (QuotientZF0.quotient_zfAxioms (memRel M) wM hM)
    (WellFoundedPart.quotient_wf_closure (memRel M) wM hM)

theorem wq_power (x : WQ M) : ∃ p : WQ M, ∀ z, z ∈ p ↔ ∀ u, u ∈ z → u ∈ x := by
  obtain ⟨p, hp⟩ := WFModel.domain_power (WellFoundedPart.quotient_wf_closure (memRel M) wM hM)
    (QuotientPower.quotient_power (memRel M) wM hM) x
  exact ⟨p, fun z => (hp z).trans Iff.rfl⟩

theorem wq_regular (x : WQ M) (hx : ∃ z, z ∈ x) : ∃ m, m ∈ x ∧ ¬∃ z, z ∈ m ∧ z ∈ x :=
  _root_.SetTheory.bridge_Reg.mp (fun e => WellFoundedPart.domain_regular qm e) x hx

/-- The interpretation of a sentence holds in `M` iff the sentence holds in the
well-founded part of the quotient. -/
theorem models_intF_iff (σ : SetTheorySentence) :
    M↓[ℒₛₑₜ] ⊧ intF σ ↔ (WQ M)↓[ℒₛₑₜ] ⊧ σ := by
  have h := eval_intF (M := M) σ ![] Empty.elim
  have e1 : (Subtype.val ∘ (![] : Fin 0 → {x : M // D x})) = ![] := funext fun i => i.elim0
  have e2 : (Subtype.val ∘ (Empty.elim : Empty → {x : M // D x})) = Empty.elim :=
    funext fun i => i.elim
  have e3 : (cls ∘ (![] : Fin 0 → {x : M // D x})) = ![] := funext fun i => i.elim0
  have e4 : (cls ∘ (Empty.elim : Empty → {x : M // D x})) = Empty.elim := funext fun i => i.elim
  rw [e1, e2, e3, e4] at h
  simpa [models_iff] using h

end Models

/-- **The fixed axioms, interpreted, are theorems of the native theory.** -/
theorem native_proves_intF (σ : SetTheorySentence) (hσ : σ ∈ 𝗘𝗤 ℒₛₑₜ ∪ zfFixed) :
    NativeSet.nativeTheory ⊢ intF σ := by
  refine SetTheory.provable_of_models.{0} NativeSet.nativeTheory (intF σ) ?_
  intro M _ _ _
  exact (models_intF_iff σ).mpr (fixed_models wq_zfAxioms wq_power wq_regular σ hσ)

/-- **The domain is nonempty, provably in the native theory.** -/
theorem native_proves_domain : NativeSet.nativeTheory ⊢ (∃⁰ domS : SetTheorySentence) := by
  refine SetTheory.provable_of_models.{0} NativeSet.nativeTheory _ ?_
  intro M _ _ _
  obtain ⟨⟨q, hq⟩⟩ := (inferInstance : Nonempty (WQ M))
  obtain ⟨x, rfl⟩ := Quotient.exists_rep q
  have hx : D x := (eval_domS x Empty.elim).mpr hq
  simp only [models_iff]
  simpa using ⟨x, hx⟩

/-! ## Internally, in every model of `𝗜𝚺₁` -/

section Embedding

variable {ξ : Type*}

lemma emb_comp_embSubsts {ο : Type*} [IsEmpty ο] {n k : ℕ} (v : Fin k → Semiterm ℒₛₑₜ ο n) :
    ((Rew.emb : Rew ℒₛₑₜ ο n ξ n).comp (Rew.embSubsts v)) = Rew.embSubsts (fun i ↦ Rew.emb (v i)) := by
  ext x
  · simp [Rew.comp_app]
  · exact x.elim

lemma emb_atomI {ο : Type*} [IsEmpty ο] {n k : ℕ} (R : (ℒₛₑₜ).Rel k) (v : Fin k → Semiterm ℒₛₑₜ ο n) :
    (Rew.emb ▹ atomI R v : Semiformula ℒₛₑₜ ξ n) = atomI R (fun i ↦ Rew.emb (v i)) := by
  cases R with
  | eq => rw [atomI, atomI, ← TransitiveRewriting.comp_app, emb_comp_embSubsts]
  | mem => rw [atomI, atomI, ← TransitiveRewriting.comp_app, emb_comp_embSubsts]

lemma emb_domAtS {ο : Type*} [IsEmpty ο] {n : ℕ} :
    (Rew.emb ▹ (domAtS n : Semiformula ℒₛₑₜ ο (n + 1)) : Semiformula ℒₛₑₜ ξ (n + 1)) = domAtS n := by
  rw [domAtS, domAtS, ← TransitiveRewriting.comp_app, emb_comp_embSubsts]
  have e : (fun i : Fin 1 ↦ (Rew.emb ((![#0] : Fin 1 → Semiterm ℒₛₑₜ ο (n + 1)) i) :
      Semiterm ℒₛₑₜ ξ (n + 1))) = ![#0] := by
    funext i
    rw [Fin.fin_one_eq_zero i]
    simp
  rw [e]

/-- The interpretation commutes with embedding sentences into formulas. -/
lemma emb_intF {ο : Type*} [IsEmpty ο] :
    ∀ {n : ℕ} (φ : Semiformula ℒₛₑₜ ο n),
      (Rew.emb ▹ intF φ : Semiformula ℒₛₑₜ ξ n) = intF (Rew.emb ▹ φ)
  | _, .rel R v => by simp [emb_atomI, Function.comp_def]
  | _, .nrel R v => by simp [emb_atomI, Function.comp_def]
  | _, ⊤ => by simp
  | _, ⊥ => by simp
  | _, φ ⋏ ψ => by simp [emb_intF φ, emb_intF ψ]
  | _, φ ⋎ ψ => by simp [emb_intF φ, emb_intF ψ]
  | _, ∀⁰ φ => by
      simp only [intF_all, Rewriting.app_all, Rew.q_emb, LogicalConnective.HomClass.map_or,
        LogicalConnective.HomClass.map_neg]
      rw [emb_domAtS, emb_intF φ]
  | _, ∃⁰ φ => by
      simp only [intF_exs, Rewriting.app_exs, Rew.q_emb, LogicalConnective.HomClass.map_and]
      rw [emb_domAtS, emb_intF φ]

end Embedding

section Internal

open LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.ZFCinPA.InternalInterpretation

variable {W : Type} [ORingStructure W] [W↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem quote_intF_sentence (σ : SetTheorySentence) :
    (⌜intF σ⌝ : W) = interp (PN : W) ⌜σ⌝ := by
  rw [LO.FirstOrder.Sentence.quote_def (intF σ), LO.FirstOrder.Sentence.quote_def σ]
  have h : (Rewriting.emb (intF σ) : SetTheoryProposition) = intF (Rewriting.emb σ) := emb_intF σ
  rw [h]
  exact quote_intF _

/-- Internally, the native theory proves the interpretation of every equality
axiom and fixed axiom of `𝗭𝗙`. -/
theorem provable_interp_fixed (σ : SetTheorySentence) (hσ : σ ∈ 𝗘𝗤 ℒₛₑₜ ∪ zfFixed) :
    Bootstrapping.Provable NativeSet.nativeTheory (interp (PN : W) ⌜σ⌝) := by
  have h := internalize_provability (V := W) (native_proves_intF σ hσ)
  rwa [quote_intF_sentence] at h

/-- Internally, the native theory proves that the domain is nonempty. -/
theorem provable_domain :
    Bootstrapping.Provable NativeSet.nativeTheory (^∃ (dom (PN : W))) := by
  have h := internalize_provability (V := W) native_proves_domain
  simpa [LO.FirstOrder.Sentence.quote_def] using h

end Internal

end LeanProofs.ZFCinPA.NativeFixed
