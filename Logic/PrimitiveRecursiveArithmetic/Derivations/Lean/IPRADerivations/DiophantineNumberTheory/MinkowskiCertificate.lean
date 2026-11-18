import IPRADerivations.DiophantineNumberTheory.MinkowskiBoxChecker
import IPRADerivations.DiophantineNumberTheory.MinkowskiInside

/-!
# Minkowski's rational box-certificate theorem, with arbitrary membership

Source `minkowski_ipra/paper/01_foundations.tex`, `thm:main`. The actual fixed
PR2 extractor returns two cell indices, a signed integer vector and a searched
nonzero coordinate. Acceptance of the original numerical rational-box checker
supplies its count, distinctness and mesh hypotheses. The original guarded
`Inside` formula supplies the two generated centers through their proved box
membership; guarded symmetry and midpoint closure then give membership of the
canonical rational embedding of the actual returned integer vector.

Only the fixed membership formula is an external schema parameter. Dimension,
box list and persistent formula parameters are internal. No membership,
collision, successful count or formula-extensionality conclusion is assumed.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiCertificate

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length)
open LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiRationalBoxes
  (mesh integerBoxes rationalSides mesh_positive)
open LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiBoxChecker
  (check boxOK checker_reflection)
open LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiCenterVectors
  (coordinateEquations signedCoordinate centerVector integerVector holdsAt)
open LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiWellFormed
  (vectorGuard symmetricGuarded midpointGuarded canonical_integer_membership)
open LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiInside
  (insideGuarded enumerated_center_membership)
open LeanProofs.IPRA.DiophantineNumberTheory.SignedEuclidean (decode)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- The original extractor is kept intact, including its two witness indices. -/
abbrev solutionF : PR 2 := MinkowskiRationalContent.extractorF
def solution (N B : PTm n) : PTm n := ap2 solutionF N B

def firstIndex (N B : PTm n) : PTm n := fstT (fstT (solution N B))
def secondIndex (N B : PTm n) : PTm n := sndT (fstT (solution N B))
def integerOutput (N B : PTm n) : PTm n := fstT (sndT (solution N B))
def nonzeroCoordinate (N B : PTm n) : PTm n := sndT (sndT (solution N B))
def cells (N B : PTm n) : PTm n := MinkowskiBoxes.boxes N (integerBoxes N B)

@[simp] theorem subst_solution {l : ℕ} (σ : Fin n → PTm l) (N B : PTm n) :
    Syn.subst σ (solution N B) = solution (Syn.subst σ N) (Syn.subst σ B) := by simp only [solution,subst_ap2]
@[simp] theorem subst_firstIndex {l : ℕ} (σ : Fin n → PTm l) (N B : PTm n) :
    Syn.subst σ (firstIndex N B) = firstIndex (Syn.subst σ N) (Syn.subst σ B) := by simp only [firstIndex,subst_fstT,subst_solution]
@[simp] theorem subst_secondIndex {l : ℕ} (σ : Fin n → PTm l) (N B : PTm n) :
    Syn.subst σ (secondIndex N B) = secondIndex (Syn.subst σ N) (Syn.subst σ B) := by simp only [secondIndex,subst_fstT,subst_sndT,subst_solution]
@[simp] theorem subst_integerOutput {l : ℕ} (σ : Fin n → PTm l) (N B : PTm n) :
    Syn.subst σ (integerOutput N B) = integerOutput (Syn.subst σ N) (Syn.subst σ B) := by simp only [integerOutput,subst_fstT,subst_sndT,subst_solution]
@[simp] theorem subst_nonzeroCoordinate {l : ℕ} (σ : Fin n → PTm l) (N B : PTm n) :
    Syn.subst σ (nonzeroCoordinate N B) = nonzeroCoordinate (Syn.subst σ N) (Syn.subst σ B) := by simp only [nonzeroCoordinate,subst_sndT,subst_solution]
@[simp] theorem subst_cells {l : ℕ} (σ : Fin n → PTm l) (N B : PTm n) :
    Syn.subst σ (cells N B) = cells (Syn.subst σ N) (Syn.subst σ B) := by
  simp only [cells,MinkowskiBoxes.subst_boxes,MinkowskiRationalBoxes.subst_integerBoxes]

/-- All hypotheses of the actual PR2 extractor follow from checker acceptance. -/
theorem accepted_program (N B : PTm n) (h : Γ ⊢[PRAAx] check N B ≐ one) :
    Γ ⊢[PRAAx] MinkowskiMesh.good N (mesh N B) (cells N B)
      (firstIndex N B) (secondIndex N B) (integerOutput N B) (nonzeroCoordinate N B) := by
  have cert := (checker_reflection N B).iffMp h
  exact MinkowskiRationalContent.rational_program_correct N B
    (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ cert)))
    (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ cert))))
    (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ cert))))

/-- The mesh equation is the center-cancellation equation on the same actual
points. This adapter is proved at symbolic inputs before substituting programs. -/
theorem mesh_center_equations (N m L i j z : PTm n)
    (h : Γ ⊢[PRAAx] MinkowskiMesh.equations N m L i j z) :
    Γ ⊢[PRAAx] coordinateEquations N m (entry L i) (entry L j) z := by
  simpa only [MinkowskiMesh.equations,coordinateEquations,signedCoordinate,
    Syn.shift,subst_entry] using h

/-- A signed integer vector with one genuine nonzero coordinate, and its
canonical rational embedding in the body described by the arbitrary formula. -/
def outputLaw (Φ : Fm PTm 2) (N x z k : PTm n) : Fm PTm n :=
  (length z ≐ N) ⋏ (lt k N ⋏
    (neg (ZT.eq (decode (entry z k)) (ZT.natLit 0)) ⋏
      (vectorGuard N (integerVector N z) ⋏ holdsAt Φ (integerVector N z) x)))

@[simp] theorem subst_outputLaw {l : ℕ} (σ : Fin n → PTm l) (Φ : Fm PTm 2) (N x z k : PTm n) :
    (outputLaw Φ N x z k).subst σ = outputLaw Φ (Syn.subst σ N) (Syn.subst σ x)
      (Syn.subst σ z) (Syn.subst σ k) := by
  simp only [outputLaw,Fm.subst_and,Fm.subst_eq,subst_neg,subst_lt,subst_length,
    subst_entry,SignedEuclidean.subst_decode,ZT.subst_eq,ZT.subst_natLit,
    MinkowskiWellFormed.subst_vectorGuard,MinkowskiCenterVectors.subst_integerVector,
    MinkowskiCenterVectors.subst_holdsAt]

/-- The complete output predicate refers to fields of the actual PR2 result. -/
def success (Φ : Fm PTm 2) (N B x : PTm n) : Fm PTm n :=
  outputLaw Φ N x (integerOutput N B) (nonzeroCoordinate N B)

@[simp] theorem subst_success {l : ℕ} (σ : Fin n → PTm l) (Φ : Fm PTm 2) (N B x : PTm n) :
    (success Φ N B x).subst σ = success Φ (Syn.subst σ N) (Syn.subst σ B) (Syn.subst σ x) := by
  simp only [success,subst_outputLaw,subst_integerOutput,subst_nonzeroCoordinate]

/-- The source existential result, retaining the concrete nonzero coordinate
and canonical embedding guard as additional witness information. -/
def existsInteger (Φ : Fm PTm 2) (N x : PTm n) : Fm PTm n :=
  .ex (.ex (outputLaw Φ (Syn.shift (Syn.shift N)) (Syn.shift (Syn.shift x)) (var 1) (var 0)))

theorem output_exists (Φ : Fm PTm 2) (N x z k : PTm n)
    (h : Γ ⊢[PRAAx] outputLaw Φ N x z k) : Γ ⊢[PRAAx] existsInteger Φ N x := by
  refine .exI z ?_
  have second : Γ ⊢[PRAAx] .ex (outputLaw Φ (Syn.shift N) (Syn.shift x) (Syn.shift z) (var 0)) := by
    refine .exI k ?_
    simpa only [subst_outputLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using h
  simpa only [existsInteger,Fm.subst_ex,subst_outputLaw,Syn.subst_var,Syn.up_zero,Syn.up_one,
    Syn.subst_shift,Syn.shift_subst,Syn.inst_zero,Syn.subst_inst_shift,Syn.up_succ,Syn.inst_succ,Syn.shift,Syn.subst_subst] using second

/-- The source certificate theorem for the fixed arbitrary membership formula.
The numerical checker, Inside, symmetry and midpoint closure are its only
substantive input contracts. Dimension positivity is the original source guard. -/
theorem certificate_correct (Φ : Fm PTm 2) (N B x : PTm n)
    (_hN : Γ ⊢[PRAAx] le one N) (hcheck : Γ ⊢[PRAAx] check N B ≐ one)
    (hInside : Γ ⊢[PRAAx] insideGuarded Φ N B x)
    (hSym : Γ ⊢[PRAAx] symmetricGuarded Φ N x)
    (hMid : Γ ⊢[PRAAx] midpointGuarded Φ N x) : Γ ⊢[PRAAx] success Φ N B x := by
  have cert := (checker_reflection N B).iffMp hcheck
  have sides : Γ ⊢[PRAAx] rationalSides N B := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ cert))
  have out := accepted_program N B hcheck
  have jRange : Γ ⊢[PRAAx] lt (secondIndex N B) (length (cells N B)) :=
    Prf.andE₁ (Prf.andE₂ (Prf.andE₂ out))
  have iRange : Γ ⊢[PRAAx] lt (firstIndex N B) (length (cells N B)) :=
    Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ out)))
  have vectorLength : Γ ⊢[PRAAx] length (integerOutput N B) ≐ N :=
    Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ out))))
  have eqs : Γ ⊢[PRAAx] MinkowskiMesh.equations N (mesh N B) (cells N B)
      (firstIndex N B) (secondIndex N B) (integerOutput N B) :=
    Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ out)))))
  have nonzero : Γ ⊢[PRAAx] lt (nonzeroCoordinate N B) N ⋏
      neg (ZT.eq (decode (entry (integerOutput N B) (nonzeroCoordinate N B))) (ZT.natLit 0)) :=
    Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ out)))))
  have lengthCells : Γ ⊢[PRAAx] length (cells N B) ≐ MinkowskiBoxUnion.total N (integerBoxes N B) :=
    MinkowskiBoxes.boxes_length N (integerBoxes N B)
  have firstCenter := enumerated_center_membership Φ N B x (firstIndex N B) sides hInside
    (lt_congr (.eqRefl _) lengthCells iRange)
  have secondCenter := enumerated_center_membership Φ N B x (secondIndex N B) sides hInside
    (lt_congr (.eqRefl _) lengthCells jRange)
  have member := canonical_integer_membership Φ N (mesh N B)
    (entry (cells N B) (firstIndex N B)) (entry (cells N B) (secondIndex N B)) (integerOutput N B) x
    (mesh_positive N B) (mesh_center_equations N (mesh N B) (cells N B)
      (firstIndex N B) (secondIndex N B) (integerOutput N B) eqs) hSym hMid firstCenter secondCenter
  exact .andI vectorLength (.andI (Prf.andE₁ nonzero) (.andI (Prf.andE₂ nonzero) member))

/-- All numerical data and the persistent membership parameter are internally
quantified; only the fixed arithmetic membership formula remains schematic. -/
theorem certificate_closed (Φ : Fm PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 0) ⟶ check (var 0) (var 1) ≐ one ⟶ insideGuarded Φ (var 0) (var 1) (var 2) ⟶
      symmetricGuarded Φ (var 0) (var 2) ⟶ midpointGuarded Φ (var 0) (var 2) ⟶
        success Φ (var 0) (var 1) (var 2)) :=
  closeUniv 3 (.impI (.impI (.impI (.impI (.impI (certificate_correct Φ _ _ _
    Prf.hyp1.wk.wk.wk Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))))

theorem certificate_exists (Φ : Fm PTm 2) (N B x : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (hcheck : Γ ⊢[PRAAx] check N B ≐ one)
    (hInside : Γ ⊢[PRAAx] insideGuarded Φ N B x)
    (hSym : Γ ⊢[PRAAx] symmetricGuarded Φ N x)
    (hMid : Γ ⊢[PRAAx] midpointGuarded Φ N x) : Γ ⊢[PRAAx] existsInteger Φ N x :=
  output_exists Φ N x (integerOutput N B) (nonzeroCoordinate N B)
    (certificate_correct Φ N B x hN hcheck hInside hSym hMid)

theorem certificate_exists_closed (Φ : Fm PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 0) ⟶ check (var 0) (var 1) ≐ one ⟶ insideGuarded Φ (var 0) (var 1) (var 2) ⟶
      symmetricGuarded Φ (var 0) (var 2) ⟶ midpointGuarded Φ (var 0) (var 2) ⟶
        existsInteger Φ (var 0) (var 2)) :=
  closeUniv 3 (.impI (.impI (.impI (.impI (.impI (certificate_exists Φ _ _ _
    Prf.hyp1.wk.wk.wk Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))))

def integerOutputF : PR 2 := PTm.toPR (integerOutput (var 0) (var 1))
def nonzeroCoordinateF : PR 2 := PTm.toPR (nonzeroCoordinate (var 0) (var 1))

theorem integerOutput_at (N B : PTm n) : Γ ⊢[PRAAx] ap2 integerOutputF N B ≐ integerOutput N B := by
  simpa only [integerOutputF,ap2,subst_integerOutput,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
    toPR_eq (Γ := Γ) (integerOutput (var 0) (var 1) : PTm 2) ![N,B]

theorem nonzeroCoordinate_at (N B : PTm n) : Γ ⊢[PRAAx] ap2 nonzeroCoordinateF N B ≐ nonzeroCoordinate N B := by
  simpa only [nonzeroCoordinateF,ap2,subst_nonzeroCoordinate,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
    toPR_eq (Γ := Γ) (nonzeroCoordinate (var 0) (var 1) : PTm 2) ![N,B]

theorem solution_programs_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    ((ap2 solutionF (var 0) (var 1) ≐ MinkowskiRationalContent.extractor (var 0) (var 1)) ⋏
      ((ap2 integerOutputF (var 0) (var 1) ≐ integerOutput (var 0) (var 1)) ⋏
        (ap2 nonzeroCoordinateF (var 0) (var 1) ≐ nonzeroCoordinate (var 0) (var 1)))) :=
  closeUniv 2 (.andI (MinkowskiRationalContent.extractor_at _ _)
    (.andI (integerOutput_at _ _) (nonzeroCoordinate_at _ _)))

end LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiCertificate
