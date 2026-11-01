import BusyBeaver.ZFC.ZFRank
import ZFCinPA.NativeZFReplacement

set_option autoImplicit false

/-! Ordinary ZF extraction and the fixed power-container theorem. -/
namespace LeanProofs.ZFCinPA.NativeZFContainers254
open LO LO.FirstOrder LO.FirstOrder.SetTheory

section Extraction
variable {V : Type*} [SetStructure V] [Nonempty V]

theorem ext_clause [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (a b : V)
    (h : ∀ x, x ∈ a ↔ x ∈ b) : a = b := by
  have he : ∀ x y : V, x = y ↔ ∀ z, z ∈ x ↔ z ∈ y := by
    simpa [models_iff,Axiom.extentionality] using
      Theory.models V 𝗭𝗙 ZermeloFraenkel.axiom_of_extentionality
  exact (he a b).mpr h

theorem pair_clause [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] :
    ∀ x y : V, ∃ p : V, ∀ z, z ∈ p ↔ z = x ∨ z = y := by
  simpa [models_iff,Axiom.pairing] using
    Theory.models V 𝗭𝗙 ZermeloFraenkel.axiom_of_pairing

theorem union_clause [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (u : V) :
    ∃ w : V, ∀ x, x ∈ w ↔ ∃ v, x ∈ v ∧ v ∈ u := by
  have hh : ∀ X : V, ∃ Y : V, ∀ z, z ∈ Y ↔ ∃ w, w ∈ X ∧ z ∈ w := by
    simpa [models_iff,Axiom.union] using
      Theory.models V 𝗭𝗙 ZermeloFraenkel.axiom_of_union
  obtain ⟨w,hw⟩ := hh u
  exact ⟨w,fun x => (hw x).trans
    ⟨fun ⟨v,hv,hx⟩ => ⟨v,hx,hv⟩,fun ⟨v,hx,hv⟩ => ⟨v,hv,hx⟩⟩⟩

theorem succ_exists [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (x : V) :
    ∃ s : V, ∀ z, z ∈ s ↔ z ∈ x ∨ z = x := by
  obtain ⟨singleton,hs⟩ := pair_clause x x
  obtain ⟨p,hp⟩ := pair_clause x singleton
  obtain ⟨s,hu⟩ := union_clause p
  refine ⟨s,fun z => ?_⟩
  rw [hu z]
  constructor
  · rintro ⟨v,hz,hv⟩
    rcases (hp v).mp hv with rfl | rfl
    · exact Or.inl hz
    · exact Or.inr (((hs z).mp hz).elim id id)
  · rintro (hz | hz)
    · exact ⟨x,hz,(hp x).mpr (Or.inl rfl)⟩
    · subst z
      exact ⟨singleton,(hs x).mpr (Or.inl rfl),(hp singleton).mpr (Or.inr rfl)⟩

theorem inf_clause [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] :
    ∃ I : V, (∃ e0, e0 ∈ I ∧ ∀ z, ¬ z ∈ e0) ∧
      (∀ x, x ∈ I → ∃ sx, sx ∈ I ∧ ∀ t, t ∈ sx ↔ (t ∈ x ∨ t = x)) := by
  have he : ∃ e : V, ∀ z, z ∉ e := by
    simpa [models_iff,Axiom.empty] using
      Theory.models V 𝗭𝗙 ZermeloFraenkel.axiom_of_empty_set
  have hi : ∃ I : V, (∀ e, (∀ z, z ∉ e) → e ∈ I) ∧
      (∀ x, x ∈ I → ∀ s, (∀ z, z ∈ s ↔ z = x ∨ z ∈ x) → s ∈ I) := by
    simpa [models_iff,Axiom.infinity,isEmpty,isSucc,Rew.q_subst,
      Semiterm.val_substs,Function.comp_def] using
      Theory.models V 𝗭𝗙 ZermeloFraenkel.axiom_of_infinity
  obtain ⟨e,he⟩ := he
  obtain ⟨I,hI,hstep⟩ := hi
  refine ⟨I,⟨e,hI e he,he⟩,fun x hx => ?_⟩
  obtain ⟨s,hs⟩ := succ_exists x
  exact ⟨s,hstep x hx s (fun z => (hs z).trans or_comm),hs⟩

theorem pow_clause [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (a : V) :
    ∃ p : V, ∀ z, z ∈ p ↔ SetTheory.Sub (memRel V) z a := by
  have hh : ∀ x : V, ∃ y : V, ∀ z, z ∈ y ↔ ∀ u, u ∈ z → u ∈ x := by
    simpa [models_iff,Axiom.power,isSubsetOf] using
      Theory.models V 𝗭𝗙 ZermeloFraenkel.axiom_of_power_set
  exact hh a

theorem reg_clause [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (a : V) (ha : ∃ x, x ∈ a) :
    ∃ m : V, m ∈ a ∧ ¬ ∃ z, z ∈ m ∧ z ∈ a := by
  have hh : ∀ x : V, (∃ z, z ∈ x) → ∃ y : V, y ∈ x ∧ ∀ z, z ∈ x → z ∉ y := by
    simpa [models_iff,Axiom.foundation,isNonempty,Rew.q_subst,
      Semiterm.val_substs,Function.comp_def] using
      Theory.models V 𝗭𝗙 ZermeloFraenkel.axiom_of_foundation
  obtain ⟨m,hm,hmin⟩ := hh a ha
  exact ⟨m,hm,fun ⟨z,hzm,hza⟩ => hmin z hza hzm⟩

theorem zfAxioms_of_models [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] : SetTheory.ZFAxioms (memRel V) :=
  { ext := ext_clause
    sep := sep_clause
    pair := pair_clause
    union := union_clause
    inf := inf_clause
    repl := repl_clause }

theorem power_containers [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (a : V) :
    ∃ v : V, a ∈ v ∧ ∀ x, x ∈ v →
      (∀ z, z ∈ x → z ∈ v) ∧ ∃ p, p ∈ v ∧ ∀ z, (∀ u, u ∈ z → u ∈ x) → z ∈ p := by
  obtain ⟨v,hav,htrans,hpow⟩ :=
    SetTheory.BusyBeaver.ZFC.ZFRank.containers
      (zfAxioms_of_models (V := V)) reg_clause pow_clause a
  exact ⟨v,hav,fun x hx => ⟨htrans x hx,hpow x hx⟩⟩

end Extraction

/-- One fixed ordinary sentence; all variables are bound. -/
def containerSentence : SetTheorySentence :=
  “∀ a, ∃ v, a ∈ v ∧ ∀ x ∈ v,
    (∀ z ∈ x, z ∈ v) ∧ ∃ p ∈ v, ∀ z, (∀ u ∈ z, u ∈ x) → z ∈ p”

theorem zf_container_sentence : (𝗭𝗙 : SetTheory) ⊢ containerSentence := by
  refine SetTheory.provable_of_models.{0} 𝗭𝗙 containerSentence ?_
  intro V _ _ _
  simpa [models_iff,containerSentence] using (power_containers (V := V))

/-- The same fixed container property in the exact binder/connective order
of Circuit.container. Distinct quotation names give exactly the de Bruijn
structure of the source row, including its repeated-label shadowing. -/
def containerRowSentence : SetTheorySentence :=
  “∀ c, ∃ b,
    (∀ a, a ∈ b →
      ((∃ p, (∀ z, (∀ u, u ∈ z → u ∈ a) → z ∈ p) ∧ p ∈ b) ∧
        (∀ t, t ∈ a → t ∈ b))) ∧ c ∈ b”

theorem zf_containerRow_sentence : (𝗭𝗙 : SetTheory) ⊢ containerRowSentence := by
  refine SetTheory.provable_of_models.{0} 𝗭𝗙 containerRowSentence ?_
  intro V _ _ _
  have hh : ∀ c : V, ∃ b : V,
      (∀ a : V, a ∈ b →
        ((∃ p : V, (∀ z : V, (∀ u : V, u ∈ z → u ∈ a) → z ∈ p) ∧ p ∈ b) ∧
          (∀ z : V, z ∈ a → z ∈ b))) ∧ c ∈ b := by
    intro c
    obtain ⟨b,hcb,hb⟩ := power_containers c
    refine ⟨b,fun a ha => ?_,hcb⟩
    obtain ⟨htrans,p,hpb,hpow⟩ := hb a ha
    exact ⟨⟨p,hpow,hpb⟩,htrans⟩
  simpa [models_iff,containerRowSentence] using hh

end LeanProofs.ZFCinPA.NativeZFContainers254

