/-
  BLUE–GOLDBERG, OBSERVATION 1(2), PROVED.

  "If `Y ⊆ λ` is cofinal with `ot(Y) < λ`, there is no `j : (V_α, Y) → (V_α, Y)`."

  This was an admitted input of the barrier (`Published.not_REx_shortCofinal`).  It is now
  a theorem, with the Kunen inconsistency (`Published.critSeq_cofinal`) as the only
  admitted ingredient:

  * the trace `Y ∩ λ` is definable in `(V_α, ∈, Y)` from `λ` by a formula of the language
    with the predicate (`traceF`, written directly in Mathlib's first-order syntax), so
    it is an element of `X` fixed by `j` (`trace_fixed`);
  * a fixed subset of `λ` of size below `λ` lies below the critical point
    (`RelWitness.fixed_small_subset`), so it is not cofinal.

  Nothing is admitted in this file.
-/
import Cardinals.WitnessFacts

universe u

namespace Cardinals

open ZFSet Ordinal Cardinal FirstOrder FirstOrder.Language

namespace ObsOne

/-- `t₁ ∈ t₂`. -/
def memT {β : Type} {n : ℕ} (t₁ t₂ : Lex.Term (β ⊕ Fin n)) : Lex.BoundedFormula β n :=
  Relations.boundedFormula₂ (ExRel.mem : Lex.Relations 2) t₁ t₂

/-- `t` satisfies the predicate. -/
def predT {β : Type} {n : ℕ} (t : Lex.Term (β ⊕ Fin n)) : Lex.BoundedFormula β n :=
  Relations.boundedFormula₁ (ExRel.pred : Lex.Relations 1) t

/-- `∀ z (z ∈ v₀ ↔ z ∈ v₁ ∧ P z)`: "`v₀` is the trace of the predicate on `v₁`". -/
def traceF : Lex.BoundedFormula (Fin 2) 0 :=
  ∀' ((memT (Term.var (Sum.inr (0 : Fin 1))) (Term.var (Sum.inl (0 : Fin 2)))).iff
    (memT (Term.var (Sum.inr (0 : Fin 1))) (Term.var (Sum.inl (1 : Fin 2))) ⊓
      predT (Term.var (Sum.inr (0 : Fin 1)))))

/-- `∃ y ∀ z (z ∈ y ↔ z ∈ v₀ ∧ P z)`. -/
def traceExF : Lex.BoundedFormula (Fin 1) 0 :=
  ∃' ∀' ((memT (Term.var (Sum.inr (1 : Fin 2))) (Term.var (Sum.inr (0 : Fin 2)))).iff
    (memT (Term.var (Sum.inr (1 : Fin 2))) (Term.var (Sum.inl (0 : Fin 1))) ⊓
      predT (Term.var (Sum.inr (1 : Fin 2)))))

theorem realize_traceF (A Y : ZFSet.{u}) (v : Fin 2 → Str A Y) :
    traceF.Realize v default ↔ ∀ z : Str A Y, z.1 ∈ (v 0).1 ↔ (z.1 ∈ (v 1).1 ∧ z.1 ∈ Y) := by
  simp only [traceF, memT, predT, BoundedFormula.realize_all, BoundedFormula.realize_iff,
    BoundedFormula.realize_inf, BoundedFormula.realize_rel₂, BoundedFormula.realize_rel₁,
    Term.realize_var, Sum.elim_inl, Sum.elim_inr]
  exact Iff.rfl

theorem realize_traceExF (A Y : ZFSet.{u}) (v : Fin 1 → Str A Y) :
    traceExF.Realize v default ↔
      ∃ y : Str A Y, ∀ z : Str A Y, z.1 ∈ y.1 ↔ (z.1 ∈ (v 0).1 ∧ z.1 ∈ Y) := by
  simp only [traceExF, memT, predT, BoundedFormula.realize_ex, BoundedFormula.realize_all,
    BoundedFormula.realize_iff, BoundedFormula.realize_inf, BoundedFormula.realize_rel₂,
    BoundedFormula.realize_rel₁, Term.realize_var, Sum.elim_inl, Sum.elim_inr]
  exact Iff.rfl

end ObsOne

namespace RelWitness

variable {lam α : Ordinal.{u}} {Y : ZFSet.{u}} (w : RelWitness lam α Y)

/-- **The trace of the predicate on `λ` is an element of `X` fixed by `j`.** -/
theorem trace_fixed : ∃ d : Str w.X Y, d.1 = Y ∩ ordZ lam ∧ w.jv d = Y ∩ ordZ lam := by
  have hA := isTransitive_vonNeumann α
  have hlamA : ordZ lam ∈ V_ α := w.X_sub w.lam_mem
  have hTA : Y ∩ ordZ lam ∈ V_ α := subset_mem_V (fun t ht => (mem_inter.mp ht).2) hlamA
  -- extensionality over `V_ α`
  have hext : ∀ y : Carrier (V_ α),
      (∀ z : Str (V_ α) Y, z.1 ∈ y.1 ↔ (z.1 ∈ ordZ lam ∧ z.1 ∈ Y)) → y.1 = Y ∩ ordZ lam := by
    intro y hy
    ext t
    rw [mem_inter]
    constructor
    · intro ht
      have := (hy ⟨t, hA.subset_of_mem y.2 ht⟩).mp ht
      exact ⟨this.2, this.1⟩
    · rintro ⟨h1, h2⟩
      exact (hy ⟨t, hA.subset_of_mem hlamA h2⟩).mpr ⟨h2, h1⟩
  -- the trace exists in `V_ α`, hence in `X`
  let lamV : Str (V_ α) Y := ⟨ordZ lam, hlamA⟩
  have hV : @BoundedFormula.Realize Lex (Str (V_ α) Y) _ _ _ ObsOne.traceExF
      (fun _ : Fin 1 => lamV) default := by
    rw [ObsOne.realize_traceExF (V_ α) Y]
    refine ⟨(⟨Y ∩ ordZ lam, hTA⟩ : Str (V_ α) Y), fun z => ?_⟩
    show z.1 ∈ Y ∩ ordZ lam ↔ _
    rw [mem_inter]
    exact and_comm
  have hX : ObsOne.traceExF.Realize (fun _ : Fin 1 => w.lamX) default := by
    have h := w.incl.map_boundedFormula ObsOne.traceExF (fun _ : Fin 1 => w.lamX) default
    refine h.mp ?_
    have e1 : (w.incl ∘ fun _ : Fin 1 => w.lamX) = fun _ : Fin 1 => lamV := by
      funext i
      exact Subtype.ext (w.incl_val _)
    rw [e1, show (w.incl ∘ (default : Fin 0 → Str w.X Y)) = default from Subsingleton.elim _ _]
    exact hV
  rw [ObsOne.realize_traceExF w.X Y] at hX
  obtain ⟨d, hd⟩ := hX
  -- `X ⊨ traceF[d, λ]`
  let v : Fin 2 → Str w.X Y := fun i => if i = 0 then d else w.lamX
  have hXd : ObsOne.traceF.Realize v default := by
    rw [ObsOne.realize_traceF w.X Y]
    exact hd
  refine ⟨d, ?_, ?_⟩
  · have h := (w.incl.map_boundedFormula ObsOne.traceF v default).mpr hXd
    rw [show (w.incl ∘ (default : Fin 0 → Str w.X Y)) = default from Subsingleton.elim _ _,
      ObsOne.realize_traceF (V_ α) Y] at h
    have h' : ∀ z : Str (V_ α) Y, z.1 ∈ (w.incl d).1 ↔ (z.1 ∈ (w.incl w.lamX).1 ∧ z.1 ∈ Y) := h
    rw [w.incl_val, w.incl_val] at h'
    exact hext ⟨d.1, w.X_sub d.2⟩ h'
  · have h := (w.j.map_boundedFormula ObsOne.traceF v default).mpr hXd
    rw [show (w.j ∘ (default : Fin 0 → Str w.X Y)) = default from Subsingleton.elim _ _,
      ObsOne.realize_traceF (V_ α) Y] at h
    have h' : ∀ z : Str (V_ α) Y, z.1 ∈ (w.j d).1 ↔ (z.1 ∈ (w.j w.lamX).1 ∧ z.1 ∈ Y) := h
    have hjl : (w.j w.lamX).1 = ordZ lam := w.j_lam
    rw [hjl] at h'
    exact hext (w.j d) h'

end RelWitness

/-- **Blue–Goldberg, Observation 1(2).**  No cardinal is exacting relative to a short
cofinal subset of itself. -/
theorem not_REx_shortCofinal (c : Cardinal.{u}) (hc : ℵ₀ ≤ c) (a : ZFSet.{u})
    (ha : ShortCofinal a c.ord) : ¬ REx c.ord a := by
  rintro ⟨α₀, h⟩
  -- a limit height above everything relevant
  let α : Ordinal.{u} := max α₀ (c.ord + 1) + ω
  have hlim : Order.IsSuccLimit α := Ordinal.isSuccLimit_add _ Ordinal.isSuccLimit_omega0
  have hα : ∀ b < α, b + 1 < α := fun b hb => by simpa using hlim.succ_lt hb
  have hα₀ : α₀ ≤ α := (le_max_left _ _).trans le_self_add
  have hlamα : c.ord < α :=
    lt_of_lt_of_le (Order.lt_add_one_iff.mpr le_rfl) ((le_max_right _ _).trans le_self_add)
  have hasub : a ⊆ ordZ c.ord := subOrd_iff_subset.mp ha.1.1
  have haV : a ⊆ V_ α := fun t ht => by
    obtain ⟨ξ, hξ, rfl⟩ := Ordinal.mem_toZFSet_iff.mp (hasub ht)
    exact ordZ_mem_V (hξ.trans hlamα)
  obtain ⟨w⟩ := h α hα₀ hlamα haV
  obtain ⟨d, hd, hjd⟩ := w.trace_fixed
  have hda : d.1 = a := by
    rw [hd]
    ext t
    rw [mem_inter]
    exact ⟨fun ht => ht.1, fun ht => ⟨ht, hasub ht⟩⟩
  have hcard : ZFSet.card d.1 < c := by
    rw [hda]
    have := ha.2
    rwa [card_ord] at this
  have hsmall := w.fixed_small_subset hc hα d (by rw [hda]; exact hasub) (hjd.trans hd.symm) hcard
  obtain ⟨η, hκη, -, hηa⟩ := ha.1.2 w.crit w.crit_lt
  have : ordZ η ∈ ordZ w.crit := hsmall (by rw [hda]; exact hηa)
  exact absurd (Ordinal.toZFSet_mem_toZFSet_iff.mp this) (not_lt.mpr hκη)

end Cardinals
