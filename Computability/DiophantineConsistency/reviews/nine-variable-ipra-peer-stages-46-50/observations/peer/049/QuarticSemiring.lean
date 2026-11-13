import DiophantineConsistency.GatesSemiring

/-! # Exact semantics of the stored quartic residual system over semirings -/
namespace DiophantineConsistency.QuarticCompiler
variable {R : Type*} [CommSemiring R]

def semiringAssignment {m : ℕ} {p q : NatExpr (Empty ⊕ Fin m)}
    (x : R) (w : Witness p q → R) : Option (Witness p q) → R := Option.elim' x w

def semiringWitnesses {m : ℕ} (p q : NatExpr (Empty ⊕ Fin m))
    (v : Fin m → R) : Witness p q → R
  | Sum.inl i => v i
  | Sum.inr (Sum.inl i) => Gates.semiringValues p (Sum.elim Empty.elim v) i
  | Sum.inr (Sum.inr (Sum.inl i)) => Gates.semiringValues q (Sum.elim Empty.elim v) i
  | Sum.inr (Sum.inr (Sum.inr _)) => 1

private theorem left_residual_iff {m : ℕ} (p q : NatExpr (Empty ⊕ Fin m)) (x : R)
    (w : Witness p q → R) (k : Gates.Wire p) :
    (residualSyntax p q (Sum.inr (Sum.inl k))).SemiringZero (semiringAssignment x w) ↔
    (Gates.residualSyntax p k).SemiringZero
      (Gates.semiringAssignment (Sum.elim Empty.elim (fun i => w (Sum.inl i)))
        (fun i => w (Sum.inr (Sum.inl i)))) := by
  rw [residualSyntax,Expr.semiringZero_rename]
  apply Iff.of_eq
  apply congrArg ((Gates.residualSyntax p k).SemiringZero)
  funext i
  cases i with
  | inl i => cases i with
    | inl i => exact i.elim
    | inr i => rfl
  | inr i => rfl

private theorem right_residual_iff {m : ℕ} (p q : NatExpr (Empty ⊕ Fin m)) (x : R)
    (w : Witness p q → R) (k : Gates.Wire q) :
    (residualSyntax p q (Sum.inr (Sum.inr (Sum.inl k)))).SemiringZero (semiringAssignment x w) ↔
    (Gates.residualSyntax q k).SemiringZero
      (Gates.semiringAssignment (Sum.elim Empty.elim (fun i => w (Sum.inl i)))
        (fun i => w (Sum.inr (Sum.inr (Sum.inl i))))) := by
  rw [residualSyntax,Expr.semiringZero_rename]
  apply Iff.of_eq
  apply congrArg ((Gates.residualSyntax q k).SemiringZero)
  funext i
  cases i with
  | inl i => cases i with
    | inl i => exact i.elim
    | inr i => rfl
  | inr i => rfl

theorem residuals_sound {m : ℕ} (p q : NatExpr (Empty ⊕ Fin m)) (x : R)
    (w : Witness p q → R)
    (h : ∀ i, (residualSyntax p q i).SemiringZero (semiringAssignment x w)) :
    p.evalSemiring (Sum.elim Empty.elim (fun i => w (Sum.inl i))) =
      q.evalSemiring (Sum.elim Empty.elim (fun i => w (Sum.inl i))) := by
  have hl := Gates.semiring_sound p
    (Sum.elim Empty.elim (fun i => w (Sum.inl i)))
    (fun i => w (Sum.inr (Sum.inl i))) (fun k => by
      exact (left_residual_iff p q x w k).mp (h (Sum.inr (Sum.inl k))))
  have hr := Gates.semiring_sound q
    (Sum.elim Empty.elim (fun i => w (Sum.inl i)))
    (fun i => w (Sum.inr (Sum.inr (Sum.inl i)))) (fun k => by
      exact (right_residual_iff p q x w k).mp (h (Sum.inr (Sum.inr (Sum.inl k)))))
  have hout := (Expr.semiringZero_var_var _ _ _).mp (h (Sum.inr (Sum.inr (Sum.inr 0))))
  exact hl.symm.trans (hout.trans hr)

theorem residuals_complete {m : ℕ} (p q : NatExpr (Empty ⊕ Fin m)) (x : R)
    (v : Fin m → R) (h : p.evalSemiring (Sum.elim Empty.elim v)=
      q.evalSemiring (Sum.elim Empty.elim v)) :
    ∀ i, (residualSyntax p q i).SemiringZero
      (semiringAssignment x (semiringWitnesses p q v)) := by
  intro i
  cases i with
  | inl i => exact (Expr.semiringZero_var_nat _ 1 _).mpr (by simp [semiringAssignment,semiringWitnesses])
  | inr i =>
    cases i with
    | inl k =>
      apply (left_residual_iff p q x (semiringWitnesses p q v) k).mpr
      exact Gates.semiring_complete p (Sum.elim Empty.elim v) k
    | inr i =>
      cases i with
      | inl k =>
        apply (right_residual_iff p q x (semiringWitnesses p q v) k).mpr
        exact Gates.semiring_complete q (Sum.elim Empty.elim v) k
      | inr i =>
        apply (Expr.semiringZero_var_var _ _ _).mpr
        simpa only [semiringAssignment,Option.elim',semiringWitnesses,Gates.semiringValues_root] using h

theorem exists_residuals_iff {m : ℕ} (p q : NatExpr (Empty ⊕ Fin m)) (x : R) :
    (∃ w : Witness p q → R, ∀ i,
      (residualSyntax p q i).SemiringZero (semiringAssignment x w)) ↔
    ∃ v : Fin m → R, p.evalSemiring (Sum.elim Empty.elim v)=
      q.evalSemiring (Sum.elim Empty.elim v) := by
  constructor
  · rintro ⟨w,hw⟩
    exact ⟨fun i => w (Sum.inl i),residuals_sound p q x w hw⟩
  · rintro ⟨v,hv⟩
    exact ⟨semiringWitnesses p q v,residuals_complete p q x v hv⟩

end DiophantineConsistency.QuarticCompiler
