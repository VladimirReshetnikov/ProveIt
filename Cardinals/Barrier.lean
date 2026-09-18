/-
  THE COMPLETENESS BARRIER (synthesis §4–§5).

  * `trace_reconstruction` (Lemma 4.3): a complete ultrafilter is ordinal definable
    from any small elementary hull that contains it.  Fully proved, including the
    explicit defining formula and its satisfaction analysis.
  * `barrier` (Theorem 5.1(2)): if `lam` is `γ`-cover exacting, no short cofinal
    subset of `lam` lies in `CD(γ⁺)`.
  * `absorption` (Theorem 5.1(1)), `regular_in_HCD` (Theorem 5.1(3)),
    `cover_gap` (Theorem 5.1(4)), `cofinal_sequence_escapes` (Corollary 5.3).

  The proofs use only the admitted published results of `Cardinals.Published`.
-/
import Cardinals.Published

universe u

namespace Cardinals

open ZFSet Ordinal Cardinal
open SetTheory (Form Sat scons)
open SetTheory.Form

/-! ### Elementary hulls: two consequences of elementarity -/

section Hull

variable {σ : ZFSet.{u}} {α : Ordinal.{u}}

/-- Lift an environment of `σ` to `V_ α`. -/
def liftEnv (h : σ ⊆ V_ α) (e : ℕ → Carrier σ) : ℕ → Carrier (V_ α) :=
  fun n => ⟨(e n).1, h (e n).2⟩

theorem liftEnv_scons (h : σ ⊆ V_ α) (d : Carrier σ) (e : ℕ → Carrier σ) (n : ℕ) :
    liftEnv h (scons d e) n = scons (⟨d.1, h d.2⟩ : Carrier (V_ α)) (liftEnv h e) n := by
  cases n <;> rfl

/-- The formula `∃ z ∀ w (w ∈ z ↔ w ∈ T ∧ w ∉ A)` with `A = v₀`, `T = v₁`. -/
def diffBody : Form :=
  fAll (SetTheory.fIff (fMem 0 1) (fAnd (fMem 0 3) (fImp (fMem 0 2) fBot)))

def diffForm : Form := fEx diffBody

/-- An elementary hull of `V_ α` is closed under relative complements. -/
theorem ElemSub.diff_mem (hσ : ElemSub σ (V_ α)) {A T : ZFSet.{u}} (hA : A ∈ σ) (hT : T ∈ σ) :
    T \ A ∈ σ := by
  obtain ⟨hsub, helem⟩ := hσ
  let e : ℕ → Carrier σ := fun n => if n = 0 then ⟨A, hA⟩ else ⟨T, hT⟩
  have hTα : T ∈ V_ α := hsub hT
  have hdiffα : T \ A ∈ V_ α := mem_vonNeumann_of_subset (fun x hx => (mem_sdiff.mp hx).1) hTα
  -- `V_ α` satisfies the existential statement
  have hV : Sat (memOn (V_ α)) (liftEnv hsub e) diffForm := by
    refine ⟨⟨T \ A, hdiffα⟩, ?_⟩
    intro w
    rw [SetTheory.Sat_fIff]
    simp only [Sat, scons, liftEnv, memOn, e]
    simp [mem_sdiff]
  -- so does `σ`
  obtain ⟨d, hd⟩ := (helem diffForm e).mpr hV
  -- and the witness satisfies the body in `V_ α`
  have hd' := (helem diffBody (scons d e)).mp hd
  have : d.1 = T \ A := by
    ext w
    constructor
    · intro hw
      have hwα : w ∈ V_ α := (isTransitive_vonNeumann α).subset_of_mem (hsub d.2) hw
      have := hd' ⟨w, hwα⟩
      rw [SetTheory.Sat_fIff] at this
      simp only [Sat, scons, memOn, e] at this
      have h2 := this.mp hw
      rw [mem_sdiff]
      exact ⟨by simpa using h2.1, by simpa using h2.2⟩
    · intro hw
      have hwα : w ∈ V_ α := (isTransitive_vonNeumann α).subset_of_mem hdiffα hw
      have := hd' ⟨w, hwα⟩
      rw [SetTheory.Sat_fIff] at this
      simp only [Sat, scons, memOn, e] at this
      rw [mem_sdiff] at hw
      exact this.mpr ⟨by simpa using hw.1, by simpa using hw.2⟩
  exact this ▸ d.2

/-- The formula `∃ A ¬ (A ∈ U ↔ A ∈ W)` with `U = v₀`, `W = v₁`. -/
def sepForm : Form := fEx (fImp (SetTheory.fIff (fMem 0 1) (fMem 0 2)) fBot)

/-- Two distinct members of an elementary hull of `V_ α` are separated by a member
of the hull. -/
theorem ElemSub.separate (hσ : ElemSub σ (V_ α)) {U W : ZFSet.{u}} (hU : U ∈ σ) (hW : W ∈ σ)
    (hne : U ≠ W) : ∃ A ∈ σ, ¬ (A ∈ U ↔ A ∈ W) := by
  obtain ⟨hsub, helem⟩ := hσ
  let e : ℕ → Carrier σ := fun n => if n = 0 then ⟨U, hU⟩ else ⟨W, hW⟩
  have hV : Sat (memOn (V_ α)) (liftEnv hsub e) sepForm := by
    have : ∃ A, ¬ (A ∈ U ↔ A ∈ W) := by
      by_contra hcon
      push Not at hcon
      exact hne (ZFSet.ext hcon)
    obtain ⟨A, hA⟩ := this
    have hAα : A ∈ V_ α := by
      by_cases hAU : A ∈ U
      · exact (isTransitive_vonNeumann α).subset_of_mem (hsub hU) hAU
      · have hAW : A ∈ W := by
          by_contra hAW
          exact hA ⟨fun h => absurd h hAU, fun h => absurd h hAW⟩
        exact (isTransitive_vonNeumann α).subset_of_mem (hsub hW) hAW
    refine ⟨⟨A, hAα⟩, ?_⟩
    intro hiff
    rw [SetTheory.Sat_fIff] at hiff
    simp only [Sat, scons, liftEnv, memOn, e] at hiff
    exact hA (by simpa using hiff)
  obtain ⟨A, hA⟩ := (helem sepForm e).mpr hV
  refine ⟨A.1, A.2, fun hiff => hA ?_⟩
  rw [SetTheory.Sat_fIff]
  simp only [Sat, scons, memOn, e]
  simpa using hiff

end Hull

/-! ### Trace reconstruction -/

/-- `v_i ⊆ v_j`, under one further binder. -/
def subF (i j : ℕ) : Form := fAll (fImp (fMem 0 (i + 1)) (fMem 0 (j + 1)))

/-- The defining formula of the trace reconstruction.  Free variables:
`v₀ = W` (the candidate), `v₁ = σ`, `v₂ = τ`, `v₃ = β`.  It says:
`W ∈ σ`, every member of `W` is a subset of `τ`, and for every `A ∈ σ` with
`A ⊆ τ`: `A ∈ W ↔ β ∈ A`. -/
def traceForm : Form :=
  fAnd (fMem 0 1)
    (fAnd (fAll (fImp (fMem 0 1) (subF 0 3)))
      (fAll (fImp (fMem 0 2) (fImp (subF 0 3) (SetTheory.fIff (fMem 0 1) (fMem 4 0))))))

/-- **Trace reconstruction (synthesis Lemma 4.3).**  Let `U` be an `η`-complete
ultrafilter on the ordinal `τ`, and let `σ ≺ V_ α` contain `U` and `τ` and have
cardinality below `η`.  Then `U` is ordinal definable from the single set
parameter `σ`. -/
theorem trace_reconstruction (η : Cardinal.{u}) (U : ZFSet.{u}) (τ : Ordinal.{u})
    (hτ : IsUltrafilterOn τ U)
    (hcomp : ∀ S : ZFSet.{u}, S ⊆ U → S.Nonempty → ZFSet.card S < η → ⋂₀ S ∈ U)
    (α : Ordinal.{u}) (σ : ZFSet.{u}) (hσ : ElemSub σ (V_ α))
    (hUσ : U ∈ σ) (hτσ : ordZ τ ∈ σ) (hcard : ZFSet.card σ < η) :
    ODfrom (fun p => p = σ) U := by
  have hsub : σ ⊆ V_ α := hσ.1
  -- the seed
  let S : ZFSet.{u} := σ ∩ U
  have hSU : S ⊆ U := fun x hx => (mem_inter.mp hx).2
  have hSne : S.Nonempty := ⟨ordZ τ, mem_inter.mpr ⟨hτσ, hτ.univ_mem⟩⟩
  have hScard : ZFSet.card S < η :=
    lt_of_le_of_lt (card_mono (fun x hx => (mem_inter.mp hx).1)) hcard
  have hI : ⋂₀ S ∈ U := hcomp S hSU hSne hScard
  have hIne : (⋂₀ S).Nonempty := by
    rcases ZFSet.eq_empty_or_nonempty (⋂₀ S) with h0 | hne
    · exact absurd (h0 ▸ hI) hτ.empty_notMem
    · exact hne
  obtain ⟨b, hb⟩ := hIne
  have hbτ : b ∈ ordZ τ := (mem_powerset.mp (hτ.sub hI)) hb
  obtain ⟨β, -, rfl⟩ := Ordinal.mem_toZFSet_iff.mp hbτ
  -- the trace identity
  have htrace : ∀ A ∈ σ, A ⊆ ordZ τ → (A ∈ U ↔ ordZ β ∈ A) := by
    intro A hA hAτ
    constructor
    · intro hAU
      exact mem_of_mem_sInter hb (mem_inter.mpr ⟨hA, hAU⟩)
    · intro hβA
      by_contra hAU
      have hc : ordZ τ \ A ∈ U := (hτ.ultra A hAτ).resolve_left hAU
      have hcσ : ordZ τ \ A ∈ σ := hσ.diff_mem hA hτσ
      have := mem_of_mem_sInter hb (mem_inter.mpr ⟨hcσ, hc⟩)
      exact (mem_sdiff.mp this).2 hβA
  -- the definition over `V_ (α + 1)`
  have hVsub : V_ α ⊆ V_ (α + 1) := vonNeumann_subset_vonNeumann_iff.mpr (le_self_add)
  have hσθ : σ ∈ V_ (α + 1) := by
    rw [vonNeumann_add_one, mem_powerset]; exact hsub
  have hτθ : ordZ τ ∈ V_ (α + 1) := hVsub (hsub hτσ)
  have hβθ : ordZ β ∈ V_ (α + 1) :=
    (isTransitive_vonNeumann _).subset_of_mem hτθ hbτ
  have hUθ : U ∈ V_ (α + 1) := hVsub (hsub hUσ)
  have h0θ : (∅ : ZFSet.{u}) ∈ V_ (α + 1) := by
    rw [mem_vonNeumann, rank_empty]
    exact lt_of_le_of_lt bot_le (Order.lt_add_one_iff.mpr le_rfl)
  refine ⟨α + 1, traceForm, ⟨∅, h0θ⟩, [⟨σ, hσθ⟩, ⟨ordZ τ, hτθ⟩, ⟨ordZ β, hβθ⟩], hUθ,
    isOrdinal_empty, ?_, ?_⟩
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl (isOrdinal_toZFSet τ)
    · exact Or.inl (isOrdinal_toZFSet β)
  · intro y
    have htrans := isTransitive_vonNeumann (α + 1)
    -- unfold satisfaction of the defining formula
    have hsat : Sat (memOn (V_ (α + 1)))
        (scons y (envOf ⟨∅, h0θ⟩ [⟨σ, hσθ⟩, ⟨ordZ τ, hτθ⟩, ⟨ordZ β, hβθ⟩])) traceForm ↔
        (y.1 ∈ σ ∧ (∀ A : Carrier (V_ (α + 1)), A.1 ∈ y.1 →
            ∀ z : Carrier (V_ (α + 1)), z.1 ∈ A.1 → z.1 ∈ ordZ τ) ∧
          (∀ A : Carrier (V_ (α + 1)), A.1 ∈ σ →
            (∀ z : Carrier (V_ (α + 1)), z.1 ∈ A.1 → z.1 ∈ ordZ τ) →
            (A.1 ∈ y.1 ↔ ordZ β ∈ A.1))) := by
      simp only [traceForm, subF, Sat, SetTheory.Sat_fIff, scons, envOf, memOn,
        List.getD_cons_zero, List.getD_cons_succ]
    rw [hsat]
    -- bounded quantifiers over `V_ (α+1)` are genuine
    have hsubset : ∀ A : ZFSet.{u}, A ∈ V_ (α + 1) →
        ((∀ z : Carrier (V_ (α + 1)), z.1 ∈ A → z.1 ∈ ordZ τ) ↔ A ⊆ ordZ τ) := by
      intro A hA
      constructor
      · intro h z hz
        exact h ⟨z, htrans.subset_of_mem hA hz⟩ hz
      · intro h z hz
        exact h hz
    constructor
    · rintro ⟨hyσ, hy2, hy3⟩
      by_contra hne
      have hne' : U ≠ y.1 := fun h => hne (Subtype.ext h.symm)
      obtain ⟨A, hAσ, hA⟩ := hσ.separate hUσ hyσ hne'
      have hAθ : A ∈ V_ (α + 1) := htrans.subset_of_mem hσθ hAσ
      by_cases hAU : A ∈ U
      · have hAτ : A ⊆ ordZ τ := mem_powerset.mp (hτ.sub hAU)
        have hβA := (htrace A hAσ hAτ).mp hAU
        have := (hy3 ⟨A, hAθ⟩ hAσ ((hsubset A hAθ).mpr hAτ)).mpr hβA
        exact hA ⟨fun _ => this, fun _ => hAU⟩
      · have hAy : A ∈ y.1 := by
          by_contra hAy
          exact hA ⟨fun h => absurd h hAU, fun h => absurd h hAy⟩
        have hAτ : A ⊆ ordZ τ := (hsubset A hAθ).mp (hy2 ⟨A, hAθ⟩ hAy)
        have hβA := (hy3 ⟨A, hAθ⟩ hAσ ((hsubset A hAθ).mpr hAτ)).mp hAy
        exact hAU ((htrace A hAσ hAτ).mpr hβA)
    · intro hy
      have hyU : y.1 = U := congrArg Subtype.val hy
      rw [hyU]
      refine ⟨hUσ, ?_, ?_⟩
      · intro A hAU z hz
        exact (mem_powerset.mp (hτ.sub hAU)) hz
      · intro A hAσ hAτ
        exact htrace A.1 hAσ ((hsubset A.1 A.2).mp hAτ)

/-! ### Finitely many parameters -/

/-- Only finitely many `P`-parameters occur in an ordinal definition. -/
theorem ODfrom.exists_finite {P : ZFSet.{u} → Prop} {x : ZFSet.{u}} (hx : ODfrom P x) :
    ∃ ps : List ZFSet.{u}, (∀ p ∈ ps, P p) ∧ ODfrom (fun p => p ∈ ps) x := by
  classical
  obtain ⟨θ, φ, d, qs, hxθ, hd, hqs, hdef⟩ := hx
  refine ⟨(qs.map Subtype.val).filter (fun p => P p), ?_, θ, φ, d, qs, hxθ, hd, ?_, hdef⟩
  · intro p hp
    simpa using (List.mem_filter.mp hp).2
  · intro q hq
    rcases hqs q hq with h | h
    · exact Or.inl h
    · right
      show q.1 ∈ List.filter (fun p => decide (P p)) (List.map Subtype.val qs)
      rw [List.mem_filter]
      exact ⟨List.mem_map.mpr ⟨q, hq, rfl⟩, by simpa using h⟩

/-- A rank containing a finite list of sets, above a prescribed height. -/
theorem exists_rank_ge (α₀ : Ordinal.{u}) (F : List ZFSet.{u}) :
    ∃ α ≥ α₀, ∀ x ∈ F, x ∈ V_ α := by
  induction F with
  | nil => exact ⟨α₀, le_rfl, by simp⟩
  | cons x F ih =>
    obtain ⟨α, hα, hF⟩ := ih
    refine ⟨max α (Order.succ (rank x)), le_trans hα (le_max_left _ _), ?_⟩
    intro y hy
    rw [List.mem_cons] at hy
    rcases hy with rfl | hy
    · rw [mem_vonNeumann]
      exact lt_of_lt_of_le (Order.lt_succ _) (le_max_right _ _)
    · exact vonNeumann_subset_vonNeumann_iff.mpr (le_max_left _ _) (hF y hy)

/-! ### The barrier -/

/-- **Absorption (synthesis Theorem 5.1(1)).**  If `lam = c.ord` is `γ`-cover
exacting, then `lam` is exacting relative to every set in `CD(γ⁺)`. -/
theorem absorption (c γ : Cardinal.{u}) (hc : ℵ₀ ≤ c) (h : CEx γ c.ord)
    (x : ZFSet.{u}) (hx : CD (Order.succ γ) x) : REx c.ord x := by
  classical
  have hcγ : c ≤ γ := Published.le_of_CEx c γ hc h
  have hγ : ℵ₀ ≤ γ := hc.trans hcγ
  -- finitely many complete ultrafilters define `x`
  obtain ⟨ps, hps, hxps⟩ := ODfrom.exists_finite hx
  -- choose the underlying ordinals
  let τof : ZFSet.{u} → Ordinal.{u} := fun U =>
    if hU : IsCompleteUF (Order.succ γ) U then hU.choose else 0
  have hτof : ∀ U ∈ ps, IsUltrafilterOn (τof U) U ∧
      ∀ S : ZFSet.{u}, S ⊆ U → S.Nonempty → ZFSet.card S < Order.succ γ → ⋂₀ S ∈ U := by
    intro U hU
    have hU' := hps U hU
    simp only [τof, dif_pos hU']
    exact hU'.choose_spec
  -- a large rank, a club of hulls, and a stationary set of exacting predicates
  obtain ⟨α₀, hstat⟩ := Published.stationary_of_CEx c γ hc h
  let F : List ZFSet.{u} := ps ++ ps.map (fun U => ordZ (τof U))
  obtain ⟨α, hα, hFα⟩ := exists_rank_ge α₀ F
  have hclub := Published.isClub_elemSub (Order.succ γ) (isRegular_succ hγ)
    (lt_of_le_of_lt hγ (Order.lt_succ γ)) α F hFα
  obtain ⟨σ, ⟨hσP, hσelem, hσF⟩, hσex⟩ := hstat α hα _ hclub
  -- every parameter is ordinal definable from `σ`
  have hparams : ∀ p, p ∈ ps → ODfrom (fun q => q = σ) p := by
    intro U hU
    obtain ⟨hτ, hcomp⟩ := hτof U hU
    refine trace_reconstruction (Order.succ γ) U (τof U) hτ hcomp α σ hσelem
      (hσF U (List.mem_append_left _ hU)) (hσF _ (List.mem_append_right _ ?_)) hσP.2
    exact List.mem_map.mpr ⟨U, hU, rfl⟩
  have hxσ : ODfrom (fun q => q = σ) x :=
    Published.ODfrom_trans (fun p => p ∈ ps) (fun q => q = σ) x hxps hparams
  exact Published.REx_transfer c hc σ x hσex hxσ

/-- **The completeness barrier (synthesis Theorem 5.1(2)).**  If `lam = c.ord` is
`γ`-cover exacting, no short cofinal subset of `lam` belongs to `CD(γ⁺)`. -/
theorem barrier (c γ : Cardinal.{u}) (hc : ℵ₀ ≤ c) (h : CEx γ c.ord)
    (a : ZFSet.{u}) (ha : ShortCofinal a c.ord) : ¬ CD (Order.succ γ) a :=
  fun hcd => Published.not_REx_shortCofinal c hc a ha (absorption c γ hc h a hcd)

/-- The barrier at every completeness level `η > γ`. -/
theorem barrier_above (c γ η : Cardinal.{u}) (hc : ℵ₀ ≤ c) (h : CEx γ c.ord) (hη : γ < η)
    (a : ZFSet.{u}) (ha : ShortCofinal a c.ord) : ¬ CD η a :=
  fun hcd => barrier c γ hc h a ha (hcd.mono (Order.succ_le_of_lt hη))

/-- **Regularity in the high-completeness models (synthesis Theorem 5.1(3)).** -/
theorem regular_in_HCD (c γ η : Cardinal.{u}) (hc : ℵ₀ ≤ c) (h : CEx γ c.ord) (hη : γ < η) :
    RegularIn (HCD η) c.ord :=
  fun a haN ha => barrier_above c γ η hc h hη a ha haN.cd

/-- ... while `lam` has cofinality `ω` in `V`. -/
theorem cof_omega (c γ : Cardinal.{u}) (hc : ℵ₀ ≤ c) (h : CEx γ c.ord) :
    ∃ s : ℕ → Ordinal.{u}, StrictMono s ∧ (∀ n, s n < c.ord) ∧ ∀ ξ < c.ord, ∃ n, ξ ≤ s n :=
  Published.cof_omega_of_witness c hc (fun _ hα => h.nonempty_witness hα)

/-- **Cover gap (synthesis Theorem 5.1(4)).**  Every cofinal subset of `lam` in a
class contained in `CD(η)`, `η > γ`, has full cardinality `|lam|`. -/
theorem cover_gap (c γ η : Cardinal.{u}) (hc : ℵ₀ ≤ c) (h : CEx γ c.ord) (hη : γ < η)
    (b : ZFSet.{u}) (hb : CD η b) (hcof : CofinalIn b c.ord) : c ≤ ZFSet.card b := by
  by_contra hlt
  rw [not_le] at hlt
  exact barrier_above c γ η hc h hη b ⟨hcof, by rwa [card_ord]⟩ hb

end Cardinals
