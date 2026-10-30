import ZFCinPA.LStepAtom

set_option autoImplicit false
noncomputable section

/-!
# The quantifier steps of the reflection generator

For a predicate `Q` of environments, `Wit Q a g` says that every environment
over `L_a` which has a constructible witness `y` (`Q (econs y t)`) has one in
`L_g`. The **witness-bounding function** of `Q` sends `a` to the least such
`g` above `a` (`WB`); it exists from one bound and separation for `Wit`
(`wb_exists`).

`ex_step`: if `F'` is a total reflection function for `P'`, `G` is the
witness-bounding function of `P'`, `P t ↔ ∃ y ∈ L, P' (econs y t)` and
`F = max(F', G)`, then `F` is a total reflection function for `P`, with code
`⟨7, c'⟩` (`satIn_ex`). At a limit `β` closed under `F`, a member `d` of `L_β`
lies in an earlier stage (`isL_spec`), so `econs d t` stays an environment
over an earlier stage, and a constructible witness for an environment over
`L_α` already lies in `L_{G α} ⊆ L_β`. The universal step is the same with
`¬P'` and the code `⟨6, c'⟩`.
-/

namespace LeanProofs.ZFCinPA.LStepEx

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA LeanProofs.ZFCinPA.LPieces LeanProofs.ZFCinPA.LInvariant
open LeanProofs.ZFCinPA.LStepAnd

section Math

open SetTheory.BusyBeaver.ZFC.InternalOrd SetTheory.BusyBeaver.ZFC.Constructible
  SetTheory.BusyBeaver.ZFC.ConstructibleDef LeanProofs.BoundedZFCConsistency

variable {V : Type*} [SetStructure V] (H : _root_.SetTheory.ZFAxioms (memRel V))
  (hR : Regular (memRel V))
  (hP : ∀ a, ∃ p, ∀ x, memRel V x p ↔ _root_.SetTheory.Sub (memRel V) x a)

/-- Every environment over `L_a` with a constructible witness has one in `L_g`. -/
def Wit (Q : V → Prop) (a g : V) : Prop :=
  ∀ U, IsL H hP a U → ∀ t, IsEnvOn H U t → (∃ y, InL H hP y ∧ Q (econs H y t)) →
    ∃ W, IsL H hP g W ∧ ∃ y, y ∈ W ∧ Q (econs H y t)

/-- `g` is the least ordinal above `a` bounding the witnesses over `L_a`. -/
def WB (Q : V → Prop) (a g : V) : Prop :=
  (Ord (memRel V) g ∧ a ∈ g ∧ Wit H hP Q a g) ∧
    ∀ h, (Ord (memRel V) h ∧ a ∈ h ∧ Wit H hP Q a h) → g ∈ h ∨ g = h

include hR in
/-- **The witness-bounding function is total**, from one bound for each ordinal
and separation for the bounding property. -/
theorem wb_exists {Q : V → Prop}
    (hbound : ∀ a, Ord (memRel V) a → ∃ g, Ord (memRel V) g ∧ a ∈ g ∧ Wit H hP Q a g)
    (hsep : ∀ a X : V, ∃ Z : V, ∀ h, h ∈ Z ↔ h ∈ X ∧ (Ord (memRel V) h ∧ a ∈ h ∧ Wit H hP Q a h)) :
    Tot (WB H hP Q) := by
  intro a ha
  obtain ⟨g₀, hg₀, hag₀, hw₀⟩ := hbound a ha
  obtain ⟨Z, hZ⟩ := hsep a (_root_.SetTheory.vsucc H g₀)
  have hsucc : Ord (memRel V) (_root_.SetTheory.vsucc H g₀) := ord_succ H hg₀
  obtain ⟨m, hmZ, hmin⟩ := hR Z ⟨g₀, (hZ g₀).2 ⟨_root_.SetTheory.vsucc_self H g₀, hg₀, hag₀, hw₀⟩⟩
  obtain ⟨hmX, hmo, ham, hmw⟩ := (hZ m).1 hmZ
  have hleast : ∀ h, (Ord (memRel V) h ∧ a ∈ h ∧ Wit H hP Q a h) → m ∈ h ∨ m = h := by
    intro h hh
    rcases trichotomy H hR m hmo h hh.1 with hmh | rfl | hhm
    · exact Or.inl hmh
    · exact Or.inr rfl
    · exact absurd ⟨h, hhm, (hZ h).2 ⟨hsucc.1 m hmX h hhm, hh⟩⟩ hmin
  refine ⟨m, hmo, ham, ⟨⟨hmo, ham, hmw⟩, hleast⟩, fun h hh => ?_⟩
  rcases hh.2 m ⟨hmo, ham, hmw⟩ with hhm | rfl
  · rcases hleast h hh.1 with hmh | rfl
    · exact absurd (hh.1.1.1 m hmh h hhm) (mem_irrefl H hR h)
    · rfl
  · rfl

include hR in
/-- A member of a limit stage lies in an earlier stage. -/
lemma mem_earlier_stage {b S d : V} (hb : IsLim (memRel V) b) (hS : IsL H hP b S) (hd : d ∈ S) :
    ∃ a, a ∈ b ∧ ∃ U, IsL H hP a U ∧ d ∈ U := by
  obtain ⟨c, T, hc, hT, hdT⟩ := (isL_spec H hR hP hb.1 hS d).1 hd
  obtain ⟨γ, hγ, hcγ⟩ := hb.2.2 c hc
  have hco : Ord (memRel V) c := ord_of_mem hb.1 hc
  have hsc : Ord (memRel V) (_root_.SetTheory.vsucc H c) := ord_succ H hco
  have hscb : _root_.SetTheory.vsucc H c ∈ b :=
    mem_of_sub_mem H hR hb.1 hγ hsc fun z hz => by
      rcases (_root_.SetTheory.vsucc_spec H c z).1 hz with hz | rfl
      · exact (ord_of_mem hb.1 hγ).1 c hcγ z hz
      · exact hcγ
  obtain ⟨U, hU⟩ := isL_exists H hR hP hsc
  exact ⟨_, hscb, U, hU,
    (isL_spec H hR hP hsc hU d).2 ⟨c, T, _root_.SetTheory.vsucc_self H c, hT, hdT⟩⟩

include hR in
/-- Two earlier stages lie in a common earlier stage. -/
lemma common_earlier_stage {b a₁ a₂ U₁ U₂ : V} (hb : IsLim (memRel V) b) (h₁ : a₁ ∈ b) (h₂ : a₂ ∈ b)
    (hU₁ : IsL H hP a₁ U₁) (hU₂ : IsL H hP a₂ U₂) :
    ∃ a, a ∈ b ∧ ∃ U, IsL H hP a U ∧ (∀ x, x ∈ U₁ → x ∈ U) ∧ (∀ x, x ∈ U₂ → x ∈ U) := by
  have ho₁ := ord_of_mem hb.1 h₁
  have ho₂ := ord_of_mem hb.1 h₂
  rcases trichotomy H hR a₁ ho₁ a₂ ho₂ with h | rfl | h
  · exact ⟨a₂, h₂, U₂, hU₂, isL_mono H hR hP ho₂ h hU₁ hU₂, fun _ hx => hx⟩
  · exact ⟨a₁, h₁, U₁, hU₁, fun _ hx => hx, fun _ hx => by rwa [isL_unique H hR hP ho₁ hU₂ hU₁] at hx⟩
  · exact ⟨a₁, h₁, U₁, hU₁, fun _ hx => hx, isL_mono H hR hP ho₁ h hU₂ hU₁⟩

include H hR hP in
/-- The maximum of two total functions is total, and closure under it gives
closure under both. -/
theorem max_props {F₁ F₃ F₅ : V → V → Prop} (htot₁ : Tot F₁) (htot₃ : Tot F₃)
    (hdefF : ∀ a g, F₅ a g ↔ ∃ g₁ g₂, F₁ a g₁ ∧ F₃ a g₂ ∧ ∀ z, z ∈ g ↔ z ∈ g₁ ∨ z ∈ g₂) :
    Tot F₅ ∧ ∀ b, IsLim (memRel V) b → (∀ a, a ∈ b → ∀ g, F₅ a g → g ∈ b) →
      (∀ a, a ∈ b → ∀ g, F₁ a g → g ∈ b) ∧ (∀ a, a ∈ b → ∀ g, F₃ a g → g ∈ b) := by
  obtain ⟨htot, -⟩ := and_step H hR hP (P₀ := fun _ => False) (P₂ := fun _ => False)
    (P₄ := fun _ => False) htot₁ (LStepBasic.bot_refl H hP) htot₃ (LStepBasic.bot_refl H hP)
    (fun _ => by simp) hdefF
  refine ⟨htot, fun b hb hcl => ⟨fun a ha g hg => ?_, fun a ha g hg => ?_⟩⟩
  · have hao := ord_of_mem hb.1 ha
    obtain ⟨g₁, ho₁, -, hF₁, u₁⟩ := htot₁ a hao
    obtain ⟨g₂, -, -, hF₃, -⟩ := htot₃ a hao
    have hF₅ := (hdefF a _).2 ⟨g₁, g₂, hF₁, hF₃, fun z => _root_.SetTheory.vcup_spec H g₁ g₂ z⟩
    rw [u₁ g hg]
    exact mem_of_sub_mem H hR hb.1 (hcl a ha _ hF₅) ho₁
      fun z hz => (_root_.SetTheory.vcup_spec H _ _ z).2 (Or.inl hz)
  · have hao := ord_of_mem hb.1 ha
    obtain ⟨g₁, -, -, hF₁, -⟩ := htot₁ a hao
    obtain ⟨g₂, ho₂, -, hF₃, u₃⟩ := htot₃ a hao
    have hF₅ := (hdefF a _).2 ⟨g₁, g₂, hF₁, hF₃, fun z => _root_.SetTheory.vcup_spec H g₁ g₂ z⟩
    rw [u₃ g hg]
    exact mem_of_sub_mem H hR hb.1 (hcl a ha _ hF₅) ho₂
      fun z hz => (_root_.SetTheory.vcup_spec H _ _ z).2 (Or.inr hz)

include hR in
/-- Extending an environment over an earlier stage by a member of the limit
stage gives an environment over an earlier stage. -/
lemma econs_earlier {b S a U t d : V} (hb : IsLim (memRel V) b) (hS : IsL H hP b S) (ha : a ∈ b)
    (hU : IsL H hP a U) (ht : IsEnvOn H U t) (hd : d ∈ S) :
    ∃ a', a' ∈ b ∧ ∃ U', IsL H hP a' U' ∧ IsEnvOn H U' (econs H d t) := by
  obtain ⟨a₁, ha₁, U₁, hU₁, hdU₁⟩ := mem_earlier_stage H hR hP hb hS hd
  obtain ⟨a₂, ha₂, U₂, hU₂, hsub₁, hsub₂⟩ := common_earlier_stage H hR hP hb ha ha₁ hU hU₁
  exact ⟨a₂, ha₂, U₂, hU₂,
    econs_isEnvOn H ⟨ht.1, fun n z h => hsub₁ z (ht.2 n z h)⟩ (hsub₂ d hdU₁)⟩

include hR in
/-- **The existential step.** -/
theorem ex_step {P' P : V → Prop} {F' G F : V → V → Prop}
    (htot' : Tot F') (hrefl' : Refl H hP P' F') (htotG : Tot G)
    (hG : ∀ a g, G a g → Wit H hP P' a g)
    (hdefP : ∀ U t, IsEnvOn H U t → (P t ↔ ∃ y, InL H hP y ∧ P' (econs H y t)))
    (hdefF : ∀ a g, F a g ↔ ∃ g₁ g₂, F' a g₁ ∧ G a g₂ ∧ ∀ z, z ∈ g ↔ z ∈ g₁ ∨ z ∈ g₂) :
    Tot F ∧ Refl H hP P F := by
  obtain ⟨htot, hcl⟩ := max_props H hR hP htot' htotG hdefF
  refine ⟨htot, ?_⟩
  obtain ⟨c', hc', hr'⟩ := hrefl'
  refine ⟨_, isFormCodeSem_ex H hc', fun b hb hclF S hS R hR' a ha U hU t ht => ?_⟩
  obtain ⟨hcl', hclG⟩ := hcl b hb hclF
  have htS := envOn_stage H hR hP hb hS ha hU ht
  rw [hdefP U t ht, satIn_ex H (isSetStructure_stage H hR hP hb hS hR') hc' htS]
  constructor
  · rintro ⟨y, hy, hQ⟩
    obtain ⟨g, -, -, hGag, -⟩ := htotG a (ord_of_mem hb.1 ha)
    obtain ⟨W, hW, y', hy'W, hQ'⟩ := hG a g hGag U hU t ht ⟨y, hy, hQ⟩
    have hy'S : y' ∈ S := isL_mono H hR hP hb.1 (hclG a ha g hGag) hW hS y' hy'W
    obtain ⟨a₂, ha₂, U₂, hU₂, hte⟩ := econs_earlier H hR hP hb hS ha hU ht hy'S
    exact ⟨y', hy'S, (hr' b hb hcl' S hS R hR' a₂ ha₂ U₂ hU₂ _ hte).1 hQ'⟩
  · rintro ⟨d, hdS, hsat⟩
    obtain ⟨a₂, ha₂, U₂, hU₂, hte⟩ := econs_earlier H hR hP hb hS ha hU ht hdS
    exact ⟨d, ⟨b, S, hb.1, hS, hdS⟩, (hr' b hb hcl' S hS R hR' a₂ ha₂ U₂ hU₂ _ hte).2 hsat⟩

include hR in
/-- **The universal step**, with the witness-bounding function of `¬P'`. -/
theorem all_step {P' P : V → Prop} {F' G F : V → V → Prop}
    (htot' : Tot F') (hrefl' : Refl H hP P' F') (htotG : Tot G)
    (hG : ∀ a g, G a g → Wit H hP (fun x => ¬ P' x) a g)
    (hdefP : ∀ U t, IsEnvOn H U t → (P t ↔ ∀ y, InL H hP y → P' (econs H y t)))
    (hdefF : ∀ a g, F a g ↔ ∃ g₁ g₂, F' a g₁ ∧ G a g₂ ∧ ∀ z, z ∈ g ↔ z ∈ g₁ ∨ z ∈ g₂) :
    Tot F ∧ Refl H hP P F := by
  obtain ⟨htot, hcl⟩ := max_props H hR hP htot' htotG hdefF
  refine ⟨htot, ?_⟩
  obtain ⟨c', hc', hr'⟩ := hrefl'
  refine ⟨_, isFormCodeSem_all H hc', fun b hb hclF S hS R hR' a ha U hU t ht => ?_⟩
  obtain ⟨hcl', hclG⟩ := hcl b hb hclF
  have htS := envOn_stage H hR hP hb hS ha hU ht
  rw [hdefP U t ht, satIn_all H (isSetStructure_stage H hR hP hb hS hR') hc' htS]
  constructor
  · intro h d hdS
    obtain ⟨a₂, ha₂, U₂, hU₂, hte⟩ := econs_earlier H hR hP hb hS ha hU ht hdS
    exact (hr' b hb hcl' S hS R hR' a₂ ha₂ U₂ hU₂ _ hte).1 (h d ⟨b, S, hb.1, hS, hdS⟩)
  · intro h y hy
    by_contra hQ
    obtain ⟨g, -, -, hGag, -⟩ := htotG a (ord_of_mem hb.1 ha)
    obtain ⟨W, hW, y', hy'W, hQ'⟩ := hG a g hGag U hU t ht ⟨y, hy, hQ⟩
    have hy'S : y' ∈ S := isL_mono H hR hP hb.1 (hclG a ha g hGag) hW hS y' hy'W
    obtain ⟨a₂, ha₂, U₂, hU₂, hte⟩ := econs_earlier H hR hP hb hS ha hU ht hy'S
    exact hQ' ((hr' b hb hcl' S hS R hR' a₂ ha₂ U₂ hU₂ _ hte).2 (h y' hy'S))

end Math

end LeanProofs.ZFCinPA.LStepEx
