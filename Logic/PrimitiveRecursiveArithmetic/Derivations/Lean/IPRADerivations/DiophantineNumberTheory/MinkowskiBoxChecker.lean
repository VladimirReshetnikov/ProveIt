import IPRADerivations.DiophantineNumberTheory.MinkowskiRationalContent
import IPRADerivations.DiophantineNumberTheory.MinkowskiGuardChecker
import IPRADerivations.Core.Header

/-!
# The original rational box-certificate checker

The fixed PR2 checker tests the canonical input list, paired box fields,
canonical rational endpoint vectors, positive rational sides, the literal
separating-axis condition and the actual rational content sum greater than
one.  Every quantified test has a displayed finite bound and is compiled
by `BoundedSyntax`; bounded quantifiers are never used as QF induction
formulas.  Checker acceptance supplies the proved actual rational-mesh
extraction theorem.  Geometric `Inside` remains a separate formula input.
-/

set_option linter.unusedSimpArgs false
set_option maxRecDepth 8192

namespace LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiBoxChecker

open_ipra
open LeanProofs.IPRA.Foundations
open LeanProofs.IPRA.Foundations.BoundedSyntax
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence subst_entry subst_sequence)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length)
open LeanProofs.IPRA.Analysis.RationalArgmin (left rationalLE)
open LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiRationalScaling (rationalLT)
open LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiRationalBoxes
  (lowerRow upperRow mesh integerBoxes rationalSide rationalSides rationalSeparationAt rationalSeparated rationalDisjoint)
open LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiRationalContent
  (contentNumerator contentDenominator rational_mesh)
open LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiWellFormed (entryBody vectorGuard)
open LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiGuardChecker (vectorSyntax vector_formula)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def boxShapes (N B : PTm n) : Fm PTm n :=
  (B ≐ sequence entryBody (length B) B) ⋏
    .all (lt (var 0) (length (Syn.shift B)) ⟶
      ((entry (Syn.shift B) (var 0) ≐ pairT (lowerRow (Syn.shift B) (var 0)) (upperRow (Syn.shift B) (var 0))) ⋏
        (vectorGuard (Syn.shift N) (lowerRow (Syn.shift B) (var 0)) ⋏
          vectorGuard (Syn.shift N) (upperRow (Syn.shift B) (var 0)))))

def boxOK (N B : PTm n) : Fm PTm n :=
  le one (length B) ⋏ (boxShapes N B ⋏ (rationalSides N B ⋏
    (rationalDisjoint N B ⋏ lt (contentDenominator N B) (contentNumerator N B))))

def shapeSyntax (N B : PTm n) : BFm n :=
  .and (.eq B (sequence entryBody (length B) B))
    (.all (length B)
      (.and (.eq (entry (Syn.shift B) (var 0))
          (pairT (lowerRow (Syn.shift B) (var 0)) (upperRow (Syn.shift B) (var 0))))
        (.and (vectorSyntax (Syn.shift N) (lowerRow (Syn.shift B) (var 0)))
          (vectorSyntax (Syn.shift N) (upperRow (Syn.shift B) (var 0))))))

def sideSyntax (N B : PTm n) : BFm n :=
  .all (length B) (.all (Syn.shift N)
    (.lt (left (entry (lowerRow (Syn.shift (Syn.shift B)) (var 1)) (var 0))
        (entry (upperRow (Syn.shift (Syn.shift B)) (var 1)) (var 0)))
      (left (entry (upperRow (Syn.shift (Syn.shift B)) (var 1)) (var 0))
        (entry (lowerRow (Syn.shift (Syn.shift B)) (var 1)) (var 0)))))

def separationSyntax (B i j k : PTm n) : BFm n :=
  .or (.le (left (entry (upperRow B i) k) (entry (lowerRow B j) k))
      (left (entry (lowerRow B j) k) (entry (upperRow B i) k)))
    (.le (left (entry (upperRow B j) k) (entry (lowerRow B i) k))
      (left (entry (lowerRow B i) k) (entry (upperRow B j) k)))

def disjointSyntax (N B : PTm n) : BFm n :=
  .all (length B) (.all (var 0)
    (.ex (Syn.shift (Syn.shift N))
      (separationSyntax (Syn.shift (Syn.shift (Syn.shift B))) (var 1) (var 2) (var 0))))

def certificateSyntax (N B : PTm n) : BFm n :=
  .and (.le one (length B)) (.and (shapeSyntax N B) (.and (sideSyntax N B)
    (.and (disjointSyntax N B) (.lt (contentDenominator N B) (contentNumerator N B)))))

theorem shape_formula (N B : PTm n) : formula (shapeSyntax N B) = boxShapes N B := by
  simp only [shapeSyntax,formula,boxShapes,vector_formula,Syn.shift,subst_length]

theorem sides_formula (N B : PTm n) : formula (sideSyntax N B) = rationalSides N B := by
  simp only [sideSyntax,formula,BFm.lt,BFm.le,rationalSides,rationalSide,rationalLT,
    Syn.shift,subst_length]
  rfl

theorem separation_formula (B i j k : PTm n) :
    formula (separationSyntax B i j k) = rationalSeparationAt B i j k := rfl

theorem disjoint_formula (N B : PTm n) : formula (disjointSyntax N B) = rationalDisjoint N B := by
  simp only [disjointSyntax,formula,rationalDisjoint,rationalSeparated,separation_formula,
    Syn.shift,subst_length,Syn.subst_var,Syn.shift_var]
  rfl

theorem certificate_formula (N B : PTm n) : formula (certificateSyntax N B) = boxOK N B := by
  simp only [certificateSyntax,formula,BFm.le,BFm.lt,shape_formula,sides_formula,disjoint_formula,boxOK]
  rfl

@[simp] theorem subst_boxShapes {k : ℕ} (σ : Fin n → PTm k) (N B : PTm n) :
    (boxShapes N B).subst σ = boxShapes (Syn.subst σ N) (Syn.subst σ B) := by
  simp only [boxShapes,Fm.subst_and,Fm.subst_eq,Fm.subst_all,Fm.subst_imp,
    subst_lt,subst_entry,subst_sequence,subst_length,subst_pairT,
    MinkowskiRationalBoxes.subst_lowerRow,MinkowskiRationalBoxes.subst_upperRow,
    MinkowskiWellFormed.subst_vectorGuard,Syn.subst_var,Syn.up_zero,Syn.up_succ,
    Syn.subst_shift,Syn.shift_subst]

@[simp] theorem subst_boxOK {k : ℕ} (σ : Fin n → PTm k) (N B : PTm n) :
    (boxOK N B).subst σ = boxOK (Syn.subst σ N) (Syn.subst σ B) := by
  simp only [boxOK,Fm.subst_and,subst_le,subst_lt,subst_length,subst_boxShapes,
    MinkowskiRationalBoxes.subst_rationalSides,MinkowskiRationalBoxes.subst_rationalDisjoint,
    MinkowskiRationalContent.subst_contentNumerator,MinkowskiRationalContent.subst_contentDenominator,
    ConciseIPRA.PTm.subst_zero,ConciseIPRA.PTm.subst_succ]

def checkerF : PR 2 := bitF (certificateSyntax (var 0) (var 1) : BFm 2)
def check (N B : PTm n) : PTm n := ap2 checkerF N B

theorem checker_program (N B : PTm n) : Γ ⊢[PRAAx] check N B ≐
    bit (certificateSyntax (var 0) (var 1) : BFm 2) ![N,B] :=
  program_correct (certificateSyntax (var 0) (var 1) : BFm 2) ![N,B]

theorem checker_reflection (N B : PTm n) : Γ ⊢[PRAAx] Fm.iff (check N B ≐ one) (boxOK N B) := by
  have h : Γ ⊢[PRAAx] Fm.iff (bit (certificateSyntax (var 0) (var 1) : BFm 2) ![N,B] ≐ one) (boxOK N B) := by
    have r := bounded_reflection (Γ := Γ) (certificateSyntax (var 0) (var 1) : BFm 2) ![N,B]
    rw [certificate_formula] at r
    simpa only [subst_boxOK,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using r
  have p := checker_program (Γ := Γ) N B
  exact .iffI (.impI (h.wk.iffMp (p.wk.eqSymm.eqTrans Prf.hyp0)))
    (.impI (p.wk.eqTrans (h.wk.iffMpr Prf.hyp0)))

theorem checker_boolean (N B : PTm n) : Γ ⊢[PRAAx] (check N B ≐ zero) ⋎ (check N B ≐ one) := by
  have p := checker_program (Γ := Γ) N B
  exact .orE (bit_cases (certificateSyntax (var 0) (var 1) : BFm 2) ![N,B])
    (.orI₁ (p.wk.eqTrans Prf.hyp0)) (.orI₂ (p.wk.eqTrans Prf.hyp0))

theorem accepted_mesh (N B : PTm n) (h : Γ ⊢[PRAAx] check N B ≐ one) :
    Γ ⊢[PRAAx] MinkowskiMesh.correct N (mesh N B) (MinkowskiBoxes.boxes N (integerBoxes N B))
      (ap3 MinkowskiMesh.meshF N (mesh N B) (MinkowskiBoxes.boxes N (integerBoxes N B))) := by
  have cert := (checker_reflection N B).iffMp h
  exact rational_mesh N B (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ cert)))
    (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ cert))))
    (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ cert))))

theorem box_checker_reflection_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (Fm.iff (check (var 0) (var 1) ≐ one) (boxOK (var 0) (var 1))) :=
  closeUniv 2 (checker_reflection _ _)

theorem box_checker_boolean_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    ((check (var 0) (var 1) ≐ zero) ⋎ (check (var 0) (var 1) ≐ one)) :=
  closeUniv 2 (checker_boolean _ _)

theorem accepted_mesh_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (check (var 0) (var 1) ≐ one ⟶
      MinkowskiMesh.correct (var 0) (mesh (var 0) (var 1)) (MinkowskiBoxes.boxes (var 0) (integerBoxes (var 0) (var 1)))
        (ap3 MinkowskiMesh.meshF (var 0) (mesh (var 0) (var 1)) (MinkowskiBoxes.boxes (var 0) (integerBoxes (var 0) (var 1))))) :=
  closeUniv 2 (.impI (accepted_mesh _ _ Prf.hyp0))

end LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiBoxChecker
