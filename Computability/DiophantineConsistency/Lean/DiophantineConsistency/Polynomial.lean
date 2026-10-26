import Diophantine.Paper1982.NineMain

/-!
# Specializing a recursively enumerable proposition to a fixed equation

These constructions remove the distinguished input from Jones's proved
nine-variable representation and from its 58-witness quartic alternative.
The coefficients are selected from the existing existence theorems. Thus
these definitions give fixed ordinary polynomials and closed correctness
theorems, but do not yet give an executable coefficient recipe. In particular
they do not assert the correctness of the report's explicit P₆₇ circuit.
-/

namespace DiophantineConsistency

open MvPolynomial

/-- Replace the distinguished input by the fixed integer `1`, leaving only
the `n` unknowns. This operation contains no consistency decision. -/
noncomputable def specializeOne {n : ℕ} (p : MvPolynomial (Fin (n + 1)) ℤ) :
    MvPolynomial (Fin n) ℤ :=
  MvPolynomial.eval₂ MvPolynomial.C
    (Fin.cons (MvPolynomial.C 1) MvPolynomial.X) p

theorem eval_specializeOne {n : ℕ} (p : MvPolynomial (Fin (n + 1)) ℤ)
    (a : Fin n → ℤ) :
    MvPolynomial.eval a (specializeOne p) =
      MvPolynomial.eval (Fin.cons 1 a) p := by
  unfold specializeOne
  rw [← MvPolynomial.eval_assoc]
  apply congrArg (fun f => MvPolynomial.eval f p)
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

/-- Fixing the input does not increase the degree. -/
theorem totalDegree_specializeOne_le {n : ℕ} (p : MvPolynomial (Fin (n + 1)) ℤ) :
    (specializeOne p).totalDegree ≤ p.totalDegree := by
  classical
  unfold specializeOne
  rw [MvPolynomial.eval₂_eq]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro d hd
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, zero_add]
  refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
  refine le_trans (Finset.sum_le_sum (fun i hi => ?_)) (MvPolynomial.le_totalDegree hd)
  change (((Fin.cons (C 1) X : Fin (n + 1) → MvPolynomial (Fin n) ℤ) i) ^ d i).totalDegree ≤ d i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

/-- Natural solutions of an integer polynomial. -/
def HasNaturalZero {n : ℕ} (p : MvPolynomial (Fin n) ℤ) : Prop :=
  ∃ a : Fin n → ℕ, MvPolynomial.eval (fun i => (a i : ℤ)) p = 0

private theorem cast_cons_one {n : ℕ} (a : Fin n → ℕ) :
    (fun i => ((Fin.cons 1 a : Fin (n + 1) → ℕ) i : ℤ)) =
      Fin.cons 1 (fun i => (a i : ℤ)) := by
  exact Fin.comp_cons (fun t : ℕ => (t : ℤ)) 1 a

/-- The nine-variable polynomial selected from the representation of the
constant recursively enumerable predicate with truth value `A`. -/
noncomputable def ninePolynomial (A : Prop) (hA : REPred (fun _ : ℕ => A)) :
    MvPolynomial (Fin 9) ℤ :=
  specializeOne (Classical.choose (Jones1982.nine_unknowns hA))

/-- Correctness after input specialization, with no remaining input variable. -/
theorem hasNaturalZero_ninePolynomial (A : Prop) (hA : REPred (fun _ : ℕ => A)) :
    HasNaturalZero (ninePolynomial A hA) ↔ A := by
  have h := Classical.choose_spec (Jones1982.nine_unknowns hA) 1 (by decide)
  change A ↔ _ at h
  simpa only [ninePolynomial, HasNaturalZero, eval_specializeOne, cast_cons_one] using h.symm

theorem noNaturalZero_ninePolynomial (A : Prop) (hA : REPred (fun _ : ℕ => A)) :
    (¬ HasNaturalZero (ninePolynomial A hA)) ↔ ¬ A :=
  not_congr (hasNaturalZero_ninePolynomial A hA)

/-- The quartic polynomial selected before its input is fixed. -/
noncomputable def quarticRepresentation (A : Prop) (hA : REPred (fun _ : ℕ => A)) :
    MvPolynomial (Fin 59) ℤ :=
  Classical.choose (Jones1982.rePred_quartic58 hA)

/-- The fixed 58-variable alternative, of degree at most four. -/
noncomputable def quarticPolynomial (A : Prop) (hA : REPred (fun _ : ℕ => A)) :
    MvPolynomial (Fin 58) ℤ :=
  specializeOne (quarticRepresentation A hA)

theorem totalDegree_quarticPolynomial_le_four (A : Prop)
    (hA : REPred (fun _ : ℕ => A)) :
    (quarticPolynomial A hA).totalDegree ≤ 4 :=
  (totalDegree_specializeOne_le _).trans
    (Classical.choose_spec (Jones1982.rePred_quartic58 hA)).1

private theorem wset_specializeOne {n : ℕ} (p : MvPolynomial (Fin (n + 1)) ℤ) :
    Jones1982.Wset p 1 ↔ HasNaturalZero (specializeOne p) := by
  constructor
  · rintro ⟨zs, h0, hz⟩
    refine ⟨Fin.tail zs, ?_⟩
    have he : Fin.cons 1 (Fin.tail zs) = zs := by
      simpa only [h0] using Fin.cons_self_tail zs
    simpa only [eval_specializeOne, ← cast_cons_one, he] using hz
  · rintro ⟨a, ha⟩
    refine ⟨Fin.cons 1 a, rfl, ?_⟩
    simpa only [cast_cons_one, eval_specializeOne] using ha

theorem hasNaturalZero_quarticPolynomial (A : Prop)
    (hA : REPred (fun _ : ℕ => A)) :
    HasNaturalZero (quarticPolynomial A hA) ↔ A := by
  have h := (Classical.choose_spec (Jones1982.rePred_quartic58 hA)).2.2 1 (by decide)
  change A ↔ Jones1982.Wset (quarticRepresentation A hA) 1 at h
  exact (wset_specializeOne _).symm.trans h.symm

theorem noNaturalZero_quarticPolynomial (A : Prop)
    (hA : REPred (fun _ : ℕ => A)) :
    (¬ HasNaturalZero (quarticPolynomial A hA)) ↔ ¬ A :=
  not_congr (hasNaturalZero_quarticPolynomial A hA)

end DiophantineConsistency
