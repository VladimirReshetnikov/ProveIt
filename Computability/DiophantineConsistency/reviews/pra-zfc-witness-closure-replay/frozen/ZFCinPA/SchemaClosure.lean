import Foundation.FirstOrder.Incompleteness.InductionSchemeDelta1

/-!
# Language-generic recognizer for universally closed axiom schemata

Foundation's `Δ₁`-definability proof for the induction schemata
(`Foundation.FirstOrder.Incompleteness.InductionSchemeDelta1`) factors through
a recognizer of universal closures: a code `p` is accepted iff it is the
`m`-fold universal closure of a free-variable-free body `b` with `bv b = m`,
whose `fvarVec`-substitution instance is the value of a fixed code-level
"schema body" function at some well-formed core code `K`.  Most of the closure
bookkeeping in that file (`qqAlls`, `bv_quote_fixitr`, `quote_univCl'`,
`quote_castLE`, …) is already generic in an encodable, LOR-definable language
`L`; three pieces are stated there for `ℒₒᵣ` only.  This module restates those
three pieces for an arbitrary such `L` and packages the whole recognizer
correctness argument once, parameterized by

* the meta-level schema body `F : Semiproposition L a → Proposition L`, and
* its code-level counterpart `Fval : ℕ → ℕ` with `Fval ⌜γ⌝ = ⌜F γ⌝`.

`schemaRecognizer_quote_iff` then characterizes the accepted codes of
propositions as exactly the universal closures `(F ψ).univCl'`, which is the
`mem_iff` obligation of `Theory.Δ₁` for the schema `{univCl (F ψ) | ψ}`.
-/

namespace LeanProofs.ZFCinPA

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping

variable {L : Language} [L.Encodable] [L.LORDefinable]

/-! ## `fvarVec` versus the typed free-variable vector, for any language

`fvarVec` builds codes of free variables, which are language-independent pair
codes; only the typed-vector reading below mentions `L`. -/

section fvarVec

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- `fvarVec` is the code of the typed substitution vector `fun i ↦ ^&i`
(over a standard length), for any encodable LOR-definable language. -/
lemma fvarVec_val_eq_lang (m : ℕ) :
    fvarVec ((m : ℕ) : V)
      = Bootstrapping.SemitermVec.val
          (fun i : Fin m ↦ (Bootstrapping.Semiterm.fvar (↑(i : ℕ)) : Bootstrapping.Semiterm V L 0)) := by
  apply nth_ext (by simp)
  intro i hi
  rw [len_fvarVec] at hi
  obtain ⟨j, rfl⟩ := eq_nat_of_lt_nat hi
  have hj : j < m := by exact_mod_cast hi
  rw [nth_fvarVec _ _ hi, show ((j : ℕ) : V) = ((⟨j, hj⟩ : Fin m) : ℕ) from rfl]
  rw [Bootstrapping.SemitermVec.val_nth_eq
    (fun i : Fin m ↦ (Bootstrapping.Semiterm.fvar (↑(i : ℕ)) : Bootstrapping.Semiterm V L 0)) ⟨j, hj⟩]
  simp

/-- **Generalized free-ization** for any language: substituting the
free-variable atoms `&0 … &(m-1)` for the `m` bound slots of `β` at the code
level computes `⌜β ⇜ (&·)⌝`. -/
lemma subst_fvarVec_quote_lang {m : ℕ} (β : Semiproposition L m) :
    Bootstrapping.subst L (fvarVec ((m : ℕ) : V)) (⌜β⌝ : V)
      = (⌜(β ⇜ (fun i : Fin m ↦ (&↑i : SyntacticTerm L)))⌝ : V) := by
  set Kt : Bootstrapping.Semiformula V L m := ⌜β⌝ with hKt
  set w : Bootstrapping.SemitermVec V L m 0 :=
    (fun i : Fin m ↦ (Bootstrapping.Semiterm.fvar (↑(i : ℕ)) : Bootstrapping.Semiterm V L 0)) with hw
  rw [fvarVec_val_eq_lang (L := L),
    show (⌜β⌝ : V) = Kt.val from rfl,
    show Bootstrapping.subst L (Bootstrapping.SemitermVec.val w) Kt.val = (Kt.subst w).val from rfl]
  rw [show (⌜(β ⇜ (fun i : Fin m ↦ (&↑i : SyntacticTerm L)))⌝ : V)
      = (⌜(β ⇜ (fun i : Fin m ↦ (&↑i : SyntacticTerm L)))⌝ : Bootstrapping.Semiformula V L 0).val from rfl]
  congr 1
  rw [hKt]
  simp only [FirstOrder.Semiformula.typed_quote_substs, hw, Semiterm.typed_quote_fvar]

end fvarVec

/-! ## Free-variable-freeness from shift-fixedness -/

/-- A syntactic formula whose code is fixed by the internal `shift` has no free
variables: every free variable of `shift β` has a free predecessor, so the
minimum would descend. -/
lemma freeVariables_empty_of_shift_fixed {m : ℕ} (β : Semiproposition L m)
    (hsh : Bootstrapping.shift L (⌜β⌝ : ℕ) = ⌜β⌝) : β.freeVariables = ∅ := by
  have hsβ : Rewriting.shift β = β :=
    (FirstOrder.Semiformula.quote_inj_iff (V := ℕ)).mp
      (by rw [FirstOrder.Semiformula.quote_shift (V := ℕ) β]; exact hsh)
  have step : ∀ x, β.FVar? x → 1 ≤ x ∧ β.FVar? (x - 1) := by
    intro x hx
    rw [← hsβ] at hx
    rcases FirstOrder.Semiformula.fvar?_rew hx with (⟨i, hi⟩ | ⟨z, hz, hi⟩)
    · simp [Rew.shift_bvar, Semiterm.FVar?] at hi
    · have hxz : x = z + 1 := by
        simpa [Rew.shift_fvar, Semiterm.FVar?, Semiterm.freeVariables_fvar] using hi
      exact ⟨by omega, by rw [hxz]; simpa using hz⟩
  by_contra hne
  classical
  have hnem := Finset.nonempty_of_ne_empty hne
  obtain ⟨hge, hpred⟩ := step (β.freeVariables.min' hnem) (β.freeVariables.min'_mem hnem)
  exact absurd (β.freeVariables.min'_le _ hpred) (by omega)

/-! ## Closure inversion, for any language and any closure target -/

/-- **Closure inversion.** A free-variable-free level-`m` formula `β` whose
internal `bv` is `m` and which substitutes back to `χ` is exactly the
`fixitr`-image of `χ`, so its `m`-fold universal closure is `χ.univCl'`.
Language-generic version of the keystone in Foundation's induction-schema
recognizer; the closure target `χ` is arbitrary. -/
theorem closure_inversion_lang {m : ℕ} (β : Semiproposition L m) (χ : Proposition L)
    (hfree : β.freeVariables = ∅) (hbv : Bootstrapping.bv (V := ℕ) L (⌜β⌝ : ℕ) = m)
    (hβχ : β ⇜ (fun i : Fin m ↦ (&↑i : SyntacticTerm L)) = χ) :
    (∀⁰* β : Proposition L) = χ.univCl' := by
  -- (*) code-level: `⌜fixitr 0 m ▹ χ⌝ = ⌜β⌝` (rebind composite = castLE on freevar-free β; codes
  -- erase the level index, sidestepping the `0 + m` vs `m` cast)
  have hcodeβ : (⌜(Rew.fixitr 0 m ▹ χ : Semiproposition L (0 + m))⌝ : ℕ) = ⌜β⌝ := by
    have hcompcast :
        ((Rew.fixitr 0 m).comp (Rew.subst (fun i : Fin m ↦ (&↑i : SyntacticTerm L)))) ▹ β
          = (Rew.castLE (Nat.le_add_left m 0) ▹ β : Semiproposition L (0 + m)) := by
      apply FirstOrder.Semiformula.rew_eq_of_funEqOn
      · intro x; simp [Rew.comp_app, Rew.fixitr_fvar, Fin.ext_iff]
      · intro x hx; rw [FirstOrder.Semiformula.FVar?, hfree] at hx; simp at hx
    have heq : (Rew.fixitr 0 m ▹ χ : Semiproposition L (0 + m))
        = (Rew.castLE (Nat.le_add_left m 0) ▹ β : Semiproposition L (0 + m)) := by
      rw [← hcompcast, TransitiveRewriting.comp_app,
        show (Rew.subst (fun i : Fin m ↦ (&↑i : SyntacticTerm L)) ▹ β) = χ from hβχ]
    rw [heq, FirstOrder.Semiformula.quote_castLE (V := ℕ) β (Nat.le_add_left m 0)]
  -- free vars of `χ = β ⇜ (&·)` are all `< m`, so `χ.fvSup ≤ m`
  have hfvbound : ∀ x, χ.FVar? x → x < m := by
    intro x hx
    rw [show χ = β ⇜ (fun i : Fin m ↦ (&↑i : SyntacticTerm L)) from hβχ.symm] at hx
    rcases FirstOrder.Semiformula.fvar?_rew hx with (⟨i, hi⟩ | ⟨z, hz, _⟩)
    · have : x = (↑i : ℕ) := by
        simpa [Rew.subst_bvar, Semiterm.FVar?, Semiterm.freeVariables_fvar] using hi
      rw [this]; exact i.isLt
    · rw [FirstOrder.Semiformula.FVar?, hfree] at hz; simp at hz
  have hfvle : χ.fvSup ≤ m := by
    rcases Nat.eq_zero_or_pos χ.fvSup with h0 | hpos
    · omega
    · have := hfvbound (χ.fvSup - 1) (FirstOrder.Semiformula.fvar?_fvSup_pred χ hpos); omega
  -- (A) `m = χ.fvSup`: `fixitr 0 m ▹ χ` shares the *code* of `fixitr 0 χ.fvSup ▹ χ` (castLE), whose
  -- `bv` is `χ.fvSup` (`bv_quote_fixitr`); but `bv ⌜β⌝ = m` (hbv), and `⌜β⌝ = ⌜fixitr 0 m ▹ χ⌝`.
  have hcast_eq : (Rew.fixitr 0 m ▹ χ : Semiproposition L (0 + m))
      = (Rew.castLE (by omega : (0 + χ.fvSup) ≤ (0 + m))
          ▹ (Rew.fixitr 0 χ.fvSup ▹ χ : Semiproposition L (0 + χ.fvSup))) := by
    rw [← TransitiveRewriting.comp_app]
    apply FirstOrder.Semiformula.rew_eq_of_funEqOn₀
    intro x hx
    have hxlt : x < χ.fvSup := FirstOrder.Semiformula.lt_fvSup_of_fvar? hx
    simp [Rew.comp_app, Rew.fixitr_fvar, hxlt, show x < m from by omega]
  have hcode : (⌜(Rew.fixitr 0 m ▹ χ : Semiproposition L (0 + m))⌝ : ℕ)
      = ⌜(Rew.fixitr 0 χ.fvSup ▹ χ : Semiproposition L (0 + χ.fvSup))⌝ := by
    rw [hcast_eq, FirstOrder.Semiformula.quote_castLE (V := ℕ)
      (Rew.fixitr 0 χ.fvSup ▹ χ : Semiproposition L (0 + χ.fvSup)) (by omega)]
  have hm : m = χ.fvSup := by
    rw [← hbv, ← hcodeβ, hcode]; exact Bootstrapping.bv_quote_fixitr χ
  -- conclude via codes: `⌜∀⁰* β⌝ = qqAlls ⌜β⌝ m = qqAlls ⌜fixitr 0 χ.fvSup ▹ χ⌝ (0+χ.fvSup) = ⌜χ.univCl'⌝`
  apply (FirstOrder.Semiformula.quote_inj_iff (L := L) (V := ℕ)).mp
  rw [Bootstrapping.quote_allClosure (V := ℕ) β, FirstOrder.Semiformula.univCl',
    Bootstrapping.quote_allClosure (V := ℕ) (Rew.fixitr 0 χ.fvSup ▹ χ), ← hcodeβ, hcode, hm]
  simp

/-! ## The generic schema recognizer -/

/-- Recognizer for the codes of universal closures of a schema with a fixed
code-level body function `Fval` over cores of arity `a`: `p` is the `m`-fold
closure of a shift-fixed body `b` with `bv b = m`, whose free-ized instance
`subst (fvarVec m) b` is `Fval K` for a well-formed level-`a` core `K`. -/
def SchemaRecognizer (L : Language) [L.Encodable] [L.LORDefinable]
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (a : ℕ) (Fval : V → V) (p : V) : Prop :=
  ∃ m ≤ p, ∃ b ≤ p,
    p = qqAlls b m ∧ IsUFormula L b ∧ Bootstrapping.shift L b = b ∧ Bootstrapping.bv L b = m
    ∧ ∃ K ≤ Bootstrapping.subst L (fvarVec m) b,
        IsSemiformula L (↑a) K ∧ Bootstrapping.subst L (fvarVec m) b = Fval K

/-- **Schema recognizer correctness** (over `ℕ`).  Given the meta schema body
`F` and a code-level function `Fval` that computes it on quotes and does not
shrink codes on quotes, the recognizer fires on `⌜φ⌝` exactly when `φ` is the
universal closure `(F ψ).univCl'` of some instance. -/
theorem schemaRecognizer_quote_iff {a : ℕ}
    (F : Semiproposition L a → Proposition L) (Fval : ℕ → ℕ)
    (hquote : ∀ γ : Semiproposition L a, Fval (⌜γ⌝ : ℕ) = (⌜F γ⌝ : ℕ))
    (hle : ∀ γ : Semiproposition L a, (⌜γ⌝ : ℕ) ≤ Fval (⌜γ⌝ : ℕ))
    (φ : Proposition L) :
    SchemaRecognizer L a Fval (⌜φ⌝ : ℕ) ↔ ∃ ψ : Semiproposition L a, φ = (F ψ).univCl' := by
  constructor
  · -- forward: recognizer fires ⟹ φ is a closed schema instance
    rintro ⟨m, -, b, -, hp, hU, hsh, hbv, K, -, hKsemi, hsubst⟩
    obtain ⟨γ, rfl⟩ := Bootstrapping.IsSemiformula.sound (by simpa using hKsemi)
    have hbsemi : IsSemiformula L m b := hbv ▸ hU.isSemiformula
    obtain ⟨β, rfl⟩ := Bootstrapping.IsSemiformula.sound hbsemi
    refine ⟨γ, ?_⟩
    -- (1) `β ⇜ (&·) = F γ`
    have hβγ : β ⇜ (fun i : Fin m ↦ (&↑i : SyntacticTerm L)) = F γ := by
      apply (FirstOrder.Semiformula.quote_inj_iff (L := L) (V := ℕ)).mp
      have e := subst_fvarVec_quote_lang (V := ℕ) β
      simp only [natCast_nat] at e
      rw [← e, hsubst, hquote]
    -- (2) `β` is free-variable-free (from `shift ⌜β⌝ = ⌜β⌝`)
    have hβfree : β.freeVariables = ∅ := freeVariables_empty_of_shift_fixed β hsh
    -- (3) `φ = ∀⁰* β`
    have hφ : φ = (∀⁰* β : Proposition L) := by
      apply (FirstOrder.Semiformula.quote_inj_iff (L := L) (V := ℕ)).mp
      rw [hp, Bootstrapping.quote_allClosure (V := ℕ) β]; simp
    rw [hφ]
    exact closure_inversion_lang β (F γ) hβfree hbv hβγ
  · -- backward: φ = univCl'(F ψ) ⟹ recognizer fires
    rintro ⟨ψ, rfl⟩
    set χ : Proposition L := F ψ with hχ
    set b : ℕ := (⌜(Rew.fixitr 0 χ.fvSup ▹ χ : Semiproposition L (0 + χ.fvSup))⌝ : ℕ) with hb
    have hcode : (⌜χ.univCl'⌝ : ℕ) = qqAlls b ((0 + χ.fvSup : ℕ)) := by
      rw [hb, Bootstrapping.quote_univCl' (V := ℕ) χ]; simp
    -- `s := subst (fvarVec m) b = Fval ⌜ψ⌝`, computed once and reused.
    have hs : Bootstrapping.subst L (fvarVec (0 + χ.fvSup : ℕ)) b = Fval (⌜ψ⌝ : ℕ) := by
      rw [hb]
      have hsub := subst_fvarVec_quote_lang (V := ℕ)
        (Rew.fixitr 0 χ.fvSup ▹ χ : Semiproposition L (0 + χ.fvSup))
      simp only [natCast_nat] at hsub
      rw [hsub, Bootstrapping.quote_subst_fvar_fixitr χ, hχ, hquote]
    refine ⟨(0 + χ.fvSup : ℕ), ?_, b, ?_, ?_, ?_, ?_, ?_, (⌜ψ⌝ : ℕ), ?_, ?_, ?_⟩
    · rw [hcode]; exact Bootstrapping.index_le_qqAlls _ _
    · rw [hcode]; exact Bootstrapping.le_qqAlls _ _
    · exact hcode
    · rw [hb]
      exact (FirstOrder.Semiformula.quote_isSemiformula (V := ℕ)
        (Rew.fixitr 0 χ.fvSup ▹ χ : Semiproposition L (0 + χ.fvSup))).isUFormula
    · -- shift b = b: the closure body is freevar-free, so meta `shift` fixes it
      rw [hb]
      have hnf : ∀ x, ¬(Rew.fixitr 0 χ.fvSup ▹ χ : Semiproposition L (0 + χ.fvSup)).FVar? x := by
        intro x
        rw [Rew.eq_bind (Rew.fixitr 0 χ.fvSup)]
        simp only [Function.comp_def, Rew.fixitr_bvar, Rew.fixitr_fvar, Fin.natAdd_mk, zero_add]
        intro hh
        rcases FirstOrder.Semiformula.fvar?_rew hh with (⟨z, hz⟩ | ⟨z, hz, hx⟩)
        · simp at hz
        · have : z < χ.fvSup := FirstOrder.Semiformula.lt_fvSup_of_fvar? hz
          simp [this] at hx
      have hshift : Rewriting.shift (Rew.fixitr 0 χ.fvSup ▹ χ : Semiproposition L (0 + χ.fvSup))
          = (Rew.fixitr 0 χ.fvSup ▹ χ : Semiproposition L (0 + χ.fvSup)) :=
        FirstOrder.Semiformula.rew_eq_self_of (by simp) (fun x hx ↦ absurd hx (hnf x))
      rw [← FirstOrder.Semiformula.quote_shift (V := ℕ)
        (Rew.fixitr 0 χ.fvSup ▹ χ : Semiproposition L (0 + χ.fvSup)), hshift]
    · rw [hb]; exact (Bootstrapping.bv_quote_fixitr χ).trans (zero_add _).symm
    · rw [hs]
      rcases Nat.eq_or_lt_of_le (hle ψ) with h' | h'
      · exact le_def.mpr (Or.inl h')
      · exact le_def.mpr (Or.inr h')
    · simpa using FirstOrder.Semiformula.quote_isSemiformula (V := ℕ) ψ
    · exact hs

/-! ## Schema membership massaging -/

omit [L.Encodable] [L.LORDefinable] in
/-- Membership of a proposition in the range of a universally closed schema,
rewritten through `univCl'`. -/
lemma mem_range_univCl_iff {a : ℕ} (F : Semiproposition L a → Proposition L)
    (φ : Proposition L) :
    (∃ σ ∈ Set.range (fun ψ : Semiproposition L a => FirstOrder.Semiformula.univCl (F ψ)),
        φ = (σ : Proposition L))
      ↔ ∃ ψ : Semiproposition L a, φ = (F ψ).univCl' := by
  constructor
  · rintro ⟨σ, ⟨ψ, rfl⟩, rfl⟩
    exact ⟨ψ, by simp⟩
  · rintro ⟨ψ, rfl⟩
    exact ⟨FirstOrder.Semiformula.univCl (F ψ), ⟨ψ, rfl⟩, by simp⟩

end LeanProofs.ZFCinPA
