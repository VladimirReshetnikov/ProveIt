import ZFCinPA.OpenedClosure
import ZFCinPA.InternalInterpretation
import ZFCinPA.ModelCodedOpenSchemaAxioms

set_option autoImplicit false
noncomputable section

/-!
# The peel for an internal interpretation

A schema axiom code is the closure `qqAlls b m` of a body `b`. Under an
interpretation `P` with domain `d = dom P` the closure becomes `m` guarded
universal quantifiers, `^∀ (¬d ∨ ·)`, so a derivation of the opened body
`subst (fvarVec m) b` whose side formulas are the domain hypotheses
`¬d(&0), …, ¬d(&(m + e - 1))` yields a derivation of the interpreted closure
with side formulas `¬d(&0), …, ¬d(&(e - 1))` (`peel`). Each step is the Tait
rule for `∀` with the variable `&0`: the side formula `¬d(&0)` joins the
interpreted body as the guard, and the remaining side formulas are the
shifts of `domSet d (k + e)` (`domSet_succ_subset`). The opened-variable
bookkeeping is `LPeel`'s (`free_subst_qVec_fvarVec`), restated here.

`derivable_mp` is modus ponens under side formulas.
-/

namespace LeanProofs.ZFCinPA.NativePeel

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA LeanProofs.ZFCinPA.InternalInterpretation
open LeanProofs.BoundedPAConsistency.InternalRelativization

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {U : SetTheory} [U.Δ₁]

/-! ## Modus ponens under side formulas -/

/-- From `U ⊢ A → B` and a derivation of `A` with side formulas `s`, a
derivation of `B` with the same side formulas. -/
lemma derivable_mp {A B s : V} (hB : IsFormula ℒₛₑₜ B)
    (hC : Provable U (Bootstrapping.imp ℒₛₑₜ A B)) (hA : Derivable U (insert A s)) :
    Derivable U (insert B s) := by
  have hAs := hA.isFormulaSet.insert
  have hAf : IsFormula ℒₛₑₜ A := hAs.1
  have hs : IsFormulaSet ℒₛₑₜ s := hAs.2
  have hCf : IsFormula ℒₛₑₜ (Bootstrapping.imp ℒₛₑₜ A B) := by
    simp [Bootstrapping.imp, hAf, hB]
  refine Derivable.cut (Bootstrapping.imp ℒₛₑₜ A B) ?_ ?_
  · refine Derivable.wk (by simp [hCf, hB, hs]) ?_ hC.toDerivable
    intro x hx
    simp only [mem_bitInsert_iff] at hx ⊢
    rcases hx with rfl | hx
    · exact Or.inl rfl
    · simp at hx
  · have e : neg ℒₛₑₜ (Bootstrapping.imp ℒₛₑₜ A B) = A ^⋏ neg ℒₛₑₜ B := by
      simp [Bootstrapping.imp, hAf.isUFormula, hB.isUFormula]
    rw [e]
    refine Derivable.and ?_ ?_
    · refine Derivable.wk (by simp [hAf, hB, hs]) ?_ hA
      intro x hx
      simp only [mem_bitInsert_iff] at hx ⊢
      tauto
    · exact Derivable.em (by simp [hB, hs]) B (by simp) (by simp)

/-! ## Side formulas -/

variable {d : V}

/-- `{¬d(&i) | i < k + 1}` lies in `¬d(&0)` together with the shift of
`{¬d(&i) | i < k}`. -/
lemma domSet_succ_subset (hd : IsSemiformula ℒₛₑₜ 1 d) (hds : shift ℒₛₑₜ d = d) (k : V) :
    domSet ℒₛₑₜ d (k + 1) ⊆ insert (domF ℒₛₑₜ d 0) (setShift ℒₛₑₜ (domSet ℒₛₑₜ d k)) :=
  fun _ hy => (domSet_succ hd hds k) ▸ hy

/-! ## The opened closure -/

lemma shift_qqAlls {body : V} (hb : IsUFormula ℒₛₑₜ body) (count : V) :
    shift ℒₛₑₜ (qqAlls body count) = qqAlls (shift ℒₛₑₜ body) count :=
  OpenedClosure.shift_qqAlls hb count

/-- Freeing the first binder of an opened closure opens one more variable. -/
theorem free_subst_qVec_fvarVec {k B : V} (hB : IsSemiformula ℒₛₑₜ (k + 1) B)
    (hs : shift ℒₛₑₜ B = B) :
    free ℒₛₑₜ (subst ℒₛₑₜ (qVec ℒₛₑₜ (fvarVec k)) B) = subst ℒₛₑₜ (fvarVec (k + 1)) B :=
  OpenedClosure.free_subst_qVec_fvarVec hB hs

/-! ## The peel -/

variable {P : V}

/-- **One peel step**: the freed body with one more domain hypothesis gives
the interpreted universal. -/
theorem peel_step (hP : Good P) {j x : V} (hx : IsSemiformula ℒₛₑₜ 1 x)
    (h : Derivable U (insert (interp P (free ℒₛₑₜ x)) (domSet ℒₛₑₜ (dom P) (j + 1)))) :
    Derivable U (insert (interp P (^∀ x)) (domSet ℒₛₑₜ (dom P) j)) := by
  have hd := hP.isDom
  have hds := hP.domShift
  have hIx : IsSemiformula ℒₛₑₜ 1 (interp P x) := isSemiformula_interp hP hx
  have hnd : IsSemiformula ℒₛₑₜ 1 (neg ℒₛₑₜ (dom P)) := by simpa using hd.neg
  rw [interp_all hx.isUFormula]
  refine Derivable.all (by simp [hnd, hIx]) ?_
  rw [free_or hnd hIx, free_neg_domain hd hds, interp_free hP hx]
  refine Derivable.or (Derivable.wk ?_ ?_ h)
  · simp [isFormula_domF hd, isSemiformula_interp hP hx.free, (isFormulaSet_domSet hd j).setShift]
  · intro y hy
    rcases mem_bitInsert_iff.mp hy with rfl | hy
    · simp
    · rcases mem_bitInsert_iff.mp (domSet_succ_subset hd hds j hy) with rfl | hy
      · simp
      · simp [hy]

/-- **The peel**: a derivation of the opened body with `m + e` domain
hypotheses gives one of the interpreted closure with `e`. -/
theorem peel (hP : Good P) {m b e : V} (hb : IsSemiformula ℒₛₑₜ m b) (hs : shift ℒₛₑₜ b = b)
    (base : Derivable U (insert (interp P (subst ℒₛₑₜ (fvarVec m) b))
      (domSet ℒₛₑₜ (dom P) (m + e)))) :
    Derivable U (insert (interp P (qqAlls b m)) (domSet ℒₛₑₜ (dom P) e)) := by
  have key : ∀ i : V, i ≤ m → Derivable U
      (insert (interp P (subst ℒₛₑₜ (fvarVec (m - i)) (qqAlls b i)))
        (domSet ℒₛₑₜ (dom P) (m - i + e))) := by
    intro i
    induction i using ISigma1.sigma1_succ_induction
    · definability
    case zero => intro _; simpa using base
    case succ i ih =>
      intro hi
      obtain ⟨k, rfl⟩ : ∃ k, m = k + (i + 1) := ⟨m - (i + 1), (tsub_add_cancel_of_le hi).symm⟩
      have e1 : k + (i + 1) - i = k + 1 := by
        rw [add_comm i 1, ← add_assoc, add_tsub_cancel_right]
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
      apply peel_step hP (hB.subst hw)
      rw [free_subst_qVec_fvarVec hB hBs, show k + e + 1 = k + 1 + e by
        rw [add_assoc, add_comm e 1, ← add_assoc]]
      exact ih'
  have h := key m le_rfl
  rw [tsub_self, zero_add] at h
  have hc : IsSemiformula ℒₛₑₜ 0 (qqAlls b m) := IsSemiformula.qqAlls (by simpa using hb)
  rwa [subst_eq_self hc (ModelCodedBindFree.fvarVec_isTermVec (L := ℒₛₑₜ) 0) (by simp)] at h

/-- An interpretation of each schema body extends to every recognized closure. -/
theorem schema_obligation (hP : Good P) {a : ℕ} (Fval : V → V)
    (hbase : ∀ K : V, IsSemiformula ℒₛₑₜ (a : V) K →
      ∃ e, Derivable U (insert (interp P (Fval K)) (domSet ℒₛₑₜ (dom P) e)))
    {p : V} (hp : SchemaRecognizer ℒₛₑₜ a Fval p) :
    ∃ e, Derivable U (insert (interp P p) (domSet ℒₛₑₜ (dom P) e)) := by
  obtain ⟨m, -, b, -, rfl, hbU, hbs, hbv, K, -, hK, hKb⟩ := hp
  have hb : IsSemiformula ℒₛₑₜ m b := by simpa [hbv] using hbU.isSemiformula
  obtain ⟨e, he⟩ := hbase K hK
  refine ⟨e, peel hP hb hbs ?_⟩
  rw [hKb]
  exact InternalInterpretation.derivable_domSet_mono hP.isDom le_add_self (he.isFormulaSet.insert.1) he

lemma domSet_zero (d : V) : domSet ℒₛₑₜ d 0 = ∅ :=
  mem_ext fun y => by simp [mem_domSet_iff]

/-- A recognized member of a finite list inherits its interpreted proof. -/
theorem list_obligation (l : List SetTheorySentence)
    (hAx : ∀ σ ∈ l, Provable U (interp P ⌜σ⌝)) {p : V}
    (hp : V ⊧/![p] (Theory.Δ₁.ofList l).ch.val) :
    ∃ e, Derivable U (insert (interp P p) (domSet ℒₛₑₜ (dom P) e)) := by
  obtain ⟨σ, hσ, rfl⟩ := (FiniteTheoryRecognizer.ofList_class_iff l p).mp hp
  refine ⟨0, ?_⟩
  rw [domSet_zero]
  exact (hAx σ hσ).toDerivable

/-- The same obligation for a finite theory's canonical recognizer. -/
theorem finite_obligation (T : SetTheory) (hT : T.Finite)
    (hAx : ∀ σ ∈ T, Provable U (interp P ⌜σ⌝)) {p : V}
    (hp : V ⊧/![p] (Theory.Δ₁.ofFinite T hT).ch.val) :
    ∃ e, Derivable U (insert (interp P p) (domSet ℒₛₑₜ (dom P) e)) := by
  apply list_obligation hT.toFinset.toList ?_ hp
  intro σ hσ
  exact hAx σ (by simpa using hσ)

end LeanProofs.ZFCinPA.NativePeel
