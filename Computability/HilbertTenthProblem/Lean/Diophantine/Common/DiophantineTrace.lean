import PAListCoding.CipherOnes
import PAListCoding.CipherRelations
import PAListCoding.IterationDioph

/-!
# Diophantine bounded universals and finite traces

ProveIt's `PAListCoding` cipher development proves the arithmetic closure contracts
required for bounded universal quantification and finite exact iteration.
This module discharges those contracts, leaving only the mathematical
transition relation and its Diophantine substitutions as hypotheses.

The assembly follows the generic reachability proof in ProveIt's
`HyperoperationDiophantine.lean`; the history of the former vendored copy is in
`TRACE_INTEGRATION.md`. No hyperoperation or arithmetic-foundation module
is imported here.
-/

namespace Diophantine

open PAListCoding
open scoped Dioph

private theorem onesClosed : CipherRelations.OnesSubstitutionClosed := by
  intro α len q ones shifted dlen dq dones dshifted
  exact CipherOnes.onesCodes_dioph dlen dq dones dshifted

private theorem codeClosed :
    CircuitDioph.TernarySubstitutionClosed SparseCipher.Code :=
  CipherRelations.code_closed_of_ones onesClosed

private theorem fixedConstClosed :
    ∀ k, CircuitDioph.TernarySubstitutionClosed
      (fun len q code => SparseCipher.ConstCode len q k code) :=
  CipherRelations.constCode_fixed_closed_of_ones onesClosed

private theorem constClosed :
    BoundedCipherDioph.QuaternarySubstitutionClosed SparseCipher.ConstCode := by
  change CipherRelations.QuaternarySubstitutionClosed SparseCipher.ConstCode
  exact CipherRelations.constCode_closed_of_ones onesClosed

private theorem indexClosed :
    CircuitDioph.TernarySubstitutionClosed SparseCipher.IndexCode :=
  CipherRelations.indexCode_closed_of_ones onesClosed

private theorem mulClosed :
    CircuitDioph.QuinarySubstitutionClosed BoundedCipher.MulRel :=
  CipherRelations.mulRel_closed_of_ones onesClosed

/-- Bounded universal quantification preserves Diophantineness when the
bound is itself Diophantine. The cipher closure contracts are proved. -/
theorem boundedForall_dioph {α : Type} {R : Set (Option α → ℕ)}
    {bound : (α → ℕ) → ℕ} (dbound : Dioph.DiophFn bound) (dR : Dioph R) :
    Dioph (BoundedDioph.BoundedForall bound R) :=
  BoundedCipherDioph.boundedForall_dioph codeClosed fixedConstClosed
    constClosed indexClosed mulClosed dbound dR

/-- Exact iteration of a Diophantine relation is Diophantine under
Diophantine substitutions for its length and endpoints. -/
theorem exactIter_dioph {α : Type} {R : ℕ → ℕ → Prop}
    {height start finish : (α → ℕ) → ℕ}
    (dR : Dioph {v : Vector3 ℕ 2 | R (v &0) (v &1)})
    (dheight : Dioph.DiophFn height) (dstart : Dioph.DiophFn start)
    (dfinish : Dioph.DiophFn finish) :
    Dioph {v : α → ℕ | ExactIter R (height v) (start v) (finish v)} :=
  IterationDioph.exactIter_dioph codeClosed fixedConstClosed constClosed
    indexClosed mulClosed dR dheight dstart dfinish

/-- Finite reachability in a Diophantine relation is Diophantine under
Diophantine endpoint substitutions. The length is existentially quantified. -/
theorem existsExactIter_dioph {α : Type} {R : ℕ → ℕ → Prop}
    {start finish : (α → ℕ) → ℕ}
    (dR : Dioph {v : Vector3 ℕ 2 | R (v &0) (v &1)})
    (dstart : Dioph.DiophFn start) (dfinish : Dioph.DiophFn finish) :
    Dioph {v : α → ℕ | ∃ steps, ExactIter R steps (start v) (finish v)} := by
  have dstart' : Dioph.DiophFn
      (fun v : (α ⊕ Unit) → ℕ => start (v ∘ Sum.inl)) :=
    Dioph.reindex_diophFn Sum.inl dstart
  have dfinish' : Dioph.DiophFn
      (fun v : (α ⊕ Unit) → ℕ => finish (v ∘ Sum.inl)) :=
    Dioph.reindex_diophFn Sum.inl dfinish
  have dsteps : Dioph.DiophFn
      (fun v : (α ⊕ Unit) → ℕ => v (Sum.inr ())) :=
    Dioph.proj_dioph (Sum.inr ())
  have diter : Dioph {v : (α ⊕ Unit) → ℕ |
      ExactIter R (v (Sum.inr ()))
        (start (v ∘ Sum.inl)) (finish (v ∘ Sum.inl))} :=
    exactIter_dioph dR dsteps dstart' dfinish'
  have dex : Dioph {v : α → ℕ |
      ∃ w : Unit → ℕ, ExactIter R (w ()) (start v) (finish v)} := by
    apply Dioph.ext (Dioph.ex_dioph diter)
    intro v
    rfl
  apply Dioph.ext dex
  intro v
  constructor
  · rintro ⟨w, hrun⟩
    exact ⟨w (), hrun⟩
  · rintro ⟨steps, hrun⟩
    exact ⟨fun _ => steps, hrun⟩

end Diophantine
