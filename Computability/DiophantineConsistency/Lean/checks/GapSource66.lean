import DiophantineConsistency.GapSource66

open DiophantineConsistency.GapSource66

private def ones : Fin 31 → ℤ := fun _ => 1
private def ports : Fin 4 → ℤ := fun _ => 1

/-- The carrier and transport coordinates are not shifted. -/
example : toOld ports ones 16=3 := by decide
example : toOld ports ones 18=3 := by decide
example : toOld ports ones 3=1 := by decide

/-- Positive arbitrary tuples need not have positive inverse gaps.
The old-source-zero premise in fromOld_positive is necessary. -/
example : fromOld ports ones 16=(-1) := by decide
example : fromOld ports ones 18=(-1) := by decide
example : ¬Positive (fromOld ports ones) := by
  intro h
  have hi := h 16
  change (0:ℤ)<(-1) at hi
  omega

/-- The extra N-q source term is visible at the smallest positive tuple. -/
example : rows ports ones 3=(-3) := by decide
example : rows ports ones 1=(-1) := by decide

example (p : Fin 4 → ℤ) (hβ : 0<p 0) (x : Fin 31 → ℕ)
    (hx : ∀ i,0<x i) (hs : ∀ k,rows p (fun i => (x i:ℤ)) k=0) :
    ∃ y : Fin 31 → ℕ, (∀ i,0<y i) ∧ ∀ k,
      DiophantineConsistency.SplitCertificate59.sourceRows p (fun i => (y i:ℤ)) k=0 :=
  (exists_positive_nat_zero_iff p hβ).mp ⟨x,hx,hs⟩

#print axioms fromOld_toOld
#print axioms toOld_fromOld
#print axioms row_identity
#print axioms zero_iff_toOld
#print axioms old_positive_gaps
#print axioms toOld_positive
#print axioms fromOld_positive
#print axioms positiveZeroEquiv
#print axioms exists_positive_zero_iff
#print axioms exists_positive_nat_zero_iff
