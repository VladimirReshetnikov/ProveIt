import PAListCoding.BoundedCipherDioph
import PAListCoding.ExactTrace

/-!
# Diophantine exact iteration from bounded universals

An exact run of input-dependent length is represented by two Goedel-beta
numbers (`code` and `step`).  Endpoint lookups are elementary; the adjacent
transition clause is a bounded universal and is discharged by the cipher
compiler.  This file packages that argument for an arbitrary Diophantine
binary relation, still parameterized only by the arithmetic cipher primitive
closures.
-/

namespace PAListCoding

namespace IterationDioph

open BoundedDioph BoundedCipher BoundedCipherDioph
open CircuitDioph SparseCipher
open Fin2
open scoped Dioph

/-! ## One decoded adjacency clause -/

/-- A clause at the distinguished index of an `Option` valuation. -/
def TraceClause {α : Type} (R : ℕ → ℕ → Prop)
    (code step : (α → ℕ) → ℕ) (v : Option α → ℕ) : Prop :=
  ∃ current next,
    BetaEntry (code (v ∘ some)) (step (v ∘ some)) (v none) current ∧
    BetaEntry (code (v ∘ some)) (step (v ∘ some)) (v none + 1) next ∧
    R current next

private abbrev ClauseWire := Fin 2

private def clauseValues (current next : ℕ) : ClauseWire → ℕ :=
  ![current, next]

theorem traceClause_dioph {α : Type} {R : ℕ → ℕ → Prop}
    {code step : (α → ℕ) → ℕ}
    (dR : Dioph {v : Vector3 ℕ 2 | R (v &0) (v &1)})
    (dcode : Dioph.DiophFn code) (dstep : Dioph.DiophFn step) :
    Dioph {v : Option α → ℕ | TraceClause R code step v} := by
  have dcode' : Dioph.DiophFn
      (fun v : (Option α ⊕ ClauseWire) → ℕ =>
        code (fun a => v (.inl (some a)))) :=
    Dioph.reindex_diophFn (fun a => Sum.inl (some a)) dcode
  have dstep' : Dioph.DiophFn
      (fun v : (Option α ⊕ ClauseWire) → ℕ =>
        step (fun a => v (.inl (some a)))) :=
    Dioph.reindex_diophFn (fun a => Sum.inl (some a)) dstep
  have dindex : Dioph.DiophFn
      (fun v : (Option α ⊕ ClauseWire) → ℕ => v (.inl none)) :=
    Dioph.proj_dioph (Sum.inl none)
  have done : Dioph.DiophFn
      (fun _v : (Option α ⊕ ClauseWire) → ℕ => 1) :=
    constFn_dioph 1
  have dnextIndex : Dioph.DiophFn
      (fun v : (Option α ⊕ ClauseWire) → ℕ => v (.inl none) + 1) :=
    Dioph.add_dioph dindex done
  have dcurrent : Dioph.DiophFn
      (fun v : (Option α ⊕ ClauseWire) → ℕ => v (.inr 0)) :=
    Dioph.proj_dioph (Sum.inr 0)
  have dnext : Dioph.DiophFn
      (fun v : (Option α ⊕ ClauseWire) → ℕ => v (.inr 1)) :=
    Dioph.proj_dioph (Sum.inr 1)
  have hcurrent := betaEntry_dioph dcode' dstep' dindex dcurrent
  have hnext := betaEntry_dioph dcode' dstep' dnextIndex dnext
  have hrel : Dioph {v : (Option α ⊕ ClauseWire) → ℕ |
      R (v (.inr 0)) (v (.inr 1))} :=
    Dioph.dioph_comp2 dcurrent dnext dR
  have hbody : Dioph {v : (Option α ⊕ ClauseWire) → ℕ |
      BetaEntry (code (fun a => v (.inl (some a))))
          (step (fun a => v (.inl (some a)))) (v (.inl none)) (v (.inr 0)) ∧
      BetaEntry (code (fun a => v (.inl (some a))))
          (step (fun a => v (.inl (some a)))) (v (.inl none) + 1) (v (.inr 1)) ∧
      R (v (.inr 0)) (v (.inr 1))} :=
    and_dioph hcurrent (and_dioph hnext hrel)
  apply Dioph.ext (Dioph.ex_dioph hbody)
  intro v
  simp only [Set.mem_setOf_eq, TraceClause]
  constructor
  · rintro ⟨w, hcurrent, hnext, hrel⟩
    exact ⟨w 0, w 1, hcurrent, hnext, hrel⟩
  · rintro ⟨current, next, hcurrent, hnext, hrel⟩
    exact ⟨clauseValues current next, by
      simpa [clauseValues, Function.comp_def] using
        (show
          BetaEntry (code (v ∘ some)) (step (v ∘ some)) (v none) current ∧
          BetaEntry (code (v ∘ some)) (step (v ∘ some)) (v none + 1) next ∧
          R current next
        from ⟨hcurrent, hnext, hrel⟩)⟩

/-! ## Beta traces -/

/-- A beta-coded exact trace is Diophantine whenever the step relation is,
assuming the five primitive cipher closure contracts. -/
theorem betaTrace_dioph
    {α : Type} {R : ℕ → ℕ → Prop}
    {code step height start finish : (α → ℕ) → ℕ}
    (hcode : TernarySubstitutionClosed Code)
    (hconstFixed : ∀ k, TernarySubstitutionClosed
      (fun len q code => ConstCode len q k code))
    (hconst : QuaternarySubstitutionClosed ConstCode)
    (hindex : TernarySubstitutionClosed IndexCode)
    (hmul : QuinarySubstitutionClosed MulRel)
    (dR : Dioph {v : Vector3 ℕ 2 | R (v &0) (v &1)})
    (dcode : Dioph.DiophFn code) (dstep : Dioph.DiophFn step)
    (dheight : Dioph.DiophFn height) (dstart : Dioph.DiophFn start)
    (dfinish : Dioph.DiophFn finish) :
    Dioph {v : α → ℕ |
      BetaTrace R (code v) (step v) (height v) (start v) (finish v)} := by
  have dzero : Dioph.DiophFn (fun _v : α → ℕ => 0) := constFn_dioph 0
  have hstartEntry := betaEntry_dioph dcode dstep dzero dstart
  have hfinishEntry := betaEntry_dioph dcode dstep dheight dfinish
  have hclause := traceClause_dioph dR dcode dstep
  have hsteps : Dioph (BoundedForall height
      {w : Option α → ℕ | TraceClause R code step w}) :=
    boundedForall_dioph hcode hconstFixed hconst hindex hmul
      dheight hclause
  apply Dioph.ext (and_dioph hstartEntry (and_dioph hfinishEntry hsteps))
  intro v
  simp only [Set.mem_setOf_eq, BetaTrace, TraceClause, consValue_none]
  rfl

/-! ## Exact iteration -/

private abbrev TraceWire := Fin 2

private def traceValues (code step : ℕ) : TraceWire → ℕ :=
  ![code, step]

/-- Exact iteration of every Diophantine binary relation is Diophantine under
arbitrary Diophantine substitutions for the length and endpoints. -/
theorem exactIter_dioph
    {α : Type} {R : ℕ → ℕ → Prop}
    {height start finish : (α → ℕ) → ℕ}
    (hcode : TernarySubstitutionClosed Code)
    (hconstFixed : ∀ k, TernarySubstitutionClosed
      (fun len q code => ConstCode len q k code))
    (hconst : QuaternarySubstitutionClosed ConstCode)
    (hindex : TernarySubstitutionClosed IndexCode)
    (hmul : QuinarySubstitutionClosed MulRel)
    (dR : Dioph {v : Vector3 ℕ 2 | R (v &0) (v &1)})
    (dheight : Dioph.DiophFn height) (dstart : Dioph.DiophFn start)
    (dfinish : Dioph.DiophFn finish) :
    Dioph {v : α → ℕ | ExactIter R (height v) (start v) (finish v)} := by
  have dheight' : Dioph.DiophFn
      (fun v : (α ⊕ TraceWire) → ℕ => height (v ∘ Sum.inl)) :=
    Dioph.reindex_diophFn Sum.inl dheight
  have dstart' : Dioph.DiophFn
      (fun v : (α ⊕ TraceWire) → ℕ => start (v ∘ Sum.inl)) :=
    Dioph.reindex_diophFn Sum.inl dstart
  have dfinish' : Dioph.DiophFn
      (fun v : (α ⊕ TraceWire) → ℕ => finish (v ∘ Sum.inl)) :=
    Dioph.reindex_diophFn Sum.inl dfinish
  have dcode : Dioph.DiophFn
      (fun v : (α ⊕ TraceWire) → ℕ => v (.inr 0)) :=
    Dioph.proj_dioph (Sum.inr 0)
  have dstep : Dioph.DiophFn
      (fun v : (α ⊕ TraceWire) → ℕ => v (.inr 1)) :=
    Dioph.proj_dioph (Sum.inr 1)
  have htrace := betaTrace_dioph hcode hconstFixed hconst hindex hmul dR
    dcode dstep dheight' dstart' dfinish'
  apply Dioph.ext (Dioph.ex_dioph htrace)
  intro v
  simp only [Set.mem_setOf_eq]
  rw [exactIter_iff_exists_betaTrace]
  constructor
  · rintro ⟨w, htrace⟩
    exact ⟨w 0, w 1, htrace⟩
  · rintro ⟨code, step, htrace⟩
    exact ⟨traceValues code step, by simpa [traceValues] using htrace⟩

end IterationDioph

end PAListCoding
