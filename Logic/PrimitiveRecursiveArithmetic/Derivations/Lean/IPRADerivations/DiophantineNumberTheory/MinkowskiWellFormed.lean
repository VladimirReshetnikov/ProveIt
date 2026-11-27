import IPRADerivations.Analysis.RationalArithmetic.Representations.RationalNormalForm
import IPRADerivations.DiophantineNumberTheory.MinkowskiCenterVectors

/-!
# Canonical vector guards in Minkowski's arbitrary-formula scheme

Source: `minkowski_ipra/paper/01_foundations.tex`, canonical coding and the
implicit well-formed guards on `Sym`, `Mid` and `Inside`.  A vector is the
actual canonical sequence of its decoded entries, has its stated length,
and every in-range rational entry is reduced.  The generated center,
opposite, midpoint and integer vectors satisfy these guards.  Applying the
source's guarded symmetry/midpoint laws then yields integer membership by
literal code equality, with no value-extensionality premise on membership.

This is the guard adapter.  It does not supply the rational box/volume
frontend or the original `Inside` certificate.
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiWellFormed

open_ipra exports
open LeanProofs.IPRA.Analysis LeanProofs.IPRA.Foundations
open LeanProofs.IPRA.Analysis.RationalIntegerNormalization (normalize integerCode normalize_integer)
open LeanProofs.IPRA.Analysis.RationalNormalForm (wellFormed normalize_well_formed)
open LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiCenters
  (center opposite midpoint centerNumerator midpointNumerator midpointDenominator midpoint_denominator_positive)
open LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiCenterVectors
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_length sequence_decode)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem scalar_guard_congr {c d : PTm n} (h : Γ ⊢[PRAAx] c ≐ d)
    (hc : Γ ⊢[PRAAx] wellFormed c) : Γ ⊢[PRAAx] wellFormed d := by
  have e := Prf.eqSubst (wellFormed (var 0) : Fm PTm 1) ![c] ![d]
    (fun i => by fin_cases i; exact h) (by simpa using hc)
  simpa using e

def entryBody : PTm 2 := entry (var 1) (var 0)

def scalarGuards (N C : PTm n) : Fm PTm n :=
  .all (lt (var 0) (Syn.shift N) ⟶ wellFormed (entry (Syn.shift C) (var 0)))

/-- Equality with the actual sequence reconstruction excludes surplus stack
data and malformed raw sequence representations. -/
def vectorGuard (N C : PTm n) : Fm PTm n :=
  (length C ≐ N) ⋏ ((C ≐ sequence entryBody N C) ⋏ scalarGuards N C)

@[simp] theorem subst_scalarGuards {k : ℕ} (σ : Fin n → PTm k) (N C : PTm n) :
    (scalarGuards N C).subst σ = scalarGuards (Syn.subst σ N) (Syn.subst σ C) := by
  simp only [scalarGuards,Fm.subst_all,Fm.subst_imp,subst_lt,
    RationalNormalForm.subst_wellFormed,MasterCertificate.subst_entry,
    Syn.subst_var,Syn.up_zero,Syn.up_succ,Syn.subst_shift,Syn.shift_subst]

@[simp] theorem subst_vectorGuard {k : ℕ} (σ : Fin n → PTm k) (N C : PTm n) :
    (vectorGuard N C).subst σ = vectorGuard (Syn.subst σ N) (Syn.subst σ C) := by
  simp only [vectorGuard,Fm.subst_and,Fm.subst_eq,SequenceComposition.subst_length,
    MasterCertificate.subst_sequence,subst_scalarGuards]

theorem constructed_reconstruction (A : PTm 2) (N x : PTm n) :
    Γ ⊢[PRAAx] sequence A N x ≐ sequence entryBody N (sequence A N x) := by
  apply sequence_equal
  refine .allI (.impI ?_)
  have e := (sequence_decode (Γ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift)
    A (x := Syn.shift x) Prf.hyp0).eqSymm
  simpa only [entryBody,inst2,Syn.shift,MasterCertificate.subst_entry,MasterCertificate.subst_sequence,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons,Matrix.tail_cons] using e

theorem constructed_guard (A : PTm 2) (N x : PTm n)
    (h : Γ ⊢[PRAAx] scalarGuards N (sequence A N x)) :
    Γ ⊢[PRAAx] vectorGuard N (sequence A N x) :=
  .andI (sequence_length _ _ _) (.andI (constructed_reconstruction A N x) h)

theorem center_scalar_guard (a : ZT n) (m : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] wellFormed (center a m) := normalize_well_formed _ _ hm
theorem opposite_scalar_guard (c : PTm n) : Γ ⊢[PRAAx] wellFormed (opposite c) :=
  normalize_well_formed _ _ (RationalNormalForm.denominator_positive c)
theorem midpoint_scalar_guard (c d : PTm n) : Γ ⊢[PRAAx] wellFormed (midpoint c d) :=
  normalize_well_formed _ _ (midpoint_denominator_positive c d)
theorem integer_scalar_guard (a : ZT n) : Γ ⊢[PRAAx] wellFormed (integerCode a) := by
  have h : Γ ⊢[PRAAx] ZT.eq a (ZT.ofNat one*a) := by
    ipra_lc
  exact scalar_guard_congr (normalize_integer a a one (le_refl _) h)
    (normalize_well_formed a one (le_refl _))

theorem center_vector_guard (N m a : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] vectorGuard N (centerVector N m a) := by
  apply constructed_guard
  refine .allI (.impI ?_)
  have pos : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift m) := by
    simpa only [Fm.shift,subst_le,ConciseIPRA.PTm.subst_zero,ConciseIPRA.PTm.subst_succ,Syn.shift] using hm.shift
  have e := center_lookup (Γ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift)
    (Syn.shift N) (Syn.shift m) (Syn.shift a) (var 0) Prf.hyp0
  simpa only [Syn.shift,centerVector,MasterCertificate.subst_sequence,subst_pairT] using
    scalar_guard_congr e.eqSymm (center_scalar_guard _ _ pos.wk)

theorem opposite_vector_guard (N C : PTm n) :
    Γ ⊢[PRAAx] vectorGuard N (oppositeVector N C) := by
  apply constructed_guard
  refine .allI (.impI ?_)
  have e := opposite_lookup (Γ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift)
    (Syn.shift N) (Syn.shift C) (var 0) Prf.hyp0
  simpa only [Syn.shift,oppositeVector,MasterCertificate.subst_sequence] using
    scalar_guard_congr e.eqSymm (opposite_scalar_guard _)

theorem midpoint_vector_guard (N C D : PTm n) :
    Γ ⊢[PRAAx] vectorGuard N (midpointVector N C D) := by
  apply constructed_guard
  refine .allI (.impI ?_)
  have e := midpoint_lookup (Γ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift)
    (Syn.shift N) (Syn.shift C) (Syn.shift D) (var 0) Prf.hyp0
  simpa only [Syn.shift,midpointVector,MasterCertificate.subst_sequence,subst_pairT] using
    scalar_guard_congr e.eqSymm (midpoint_scalar_guard _ _)

theorem integer_vector_guard (N z : PTm n) :
    Γ ⊢[PRAAx] vectorGuard N (integerVector N z) := by
  apply constructed_guard
  refine .allI (.impI ?_)
  have e := integer_lookup (Γ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift)
    (Syn.shift N) (Syn.shift z) (var 0) Prf.hyp0
  simpa only [Syn.shift,integerVector,MasterCertificate.subst_sequence] using
    scalar_guard_congr e.eqSymm (integer_scalar_guard _)

/-- Parameters of membership stay object-language data.  Only the fixed
membership formula is an external schema parameter. -/
def symmetricGuarded (Φ : Fm PTm 2) (N x : PTm n) : Fm PTm n :=
  .all (vectorGuard (Syn.shift N) (var 0) ⟶ holdsAt Φ (var 0) (Syn.shift x) ⟶
    holdsAt Φ (oppositeVector (Syn.shift N) (var 0)) (Syn.shift x))
def midpointGuarded (Φ : Fm PTm 2) (N x : PTm n) : Fm PTm n :=
  .all (.all (vectorGuard (Syn.shift (Syn.shift N)) (var 1) ⟶
    vectorGuard (Syn.shift (Syn.shift N)) (var 0) ⟶
    holdsAt Φ (var 1) (Syn.shift (Syn.shift x)) ⟶
    holdsAt Φ (var 0) (Syn.shift (Syn.shift x)) ⟶
    holdsAt Φ (midpointVector (Syn.shift (Syn.shift N)) (var 1) (var 0)) (Syn.shift (Syn.shift x))))

theorem symmetry_guarded_at (Φ : Fm PTm 2) (N C x : PTm n)
    (h : Γ ⊢[PRAAx] symmetricGuarded Φ N x)
    (hC : Γ ⊢[PRAAx] vectorGuard N C) (hΦ : Γ ⊢[PRAAx] holdsAt Φ C x) :
    Γ ⊢[PRAAx] holdsAt Φ (oppositeVector N C) x := by
  have rule : Γ ⊢[PRAAx] vectorGuard N C ⟶ holdsAt Φ C x ⟶ holdsAt Φ (oppositeVector N C) x := by
    simpa only [symmetricGuarded,Fm.subst_imp,subst_vectorGuard,subst_holdsAt,subst_oppositeVector,
      Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using Prf.allE C h
  exact .impE (.impE rule hC) hΦ

theorem midpoint_guarded_at (Φ : Fm PTm 2) (N C D x : PTm n)
    (h : Γ ⊢[PRAAx] midpointGuarded Φ N x)
    (hC : Γ ⊢[PRAAx] vectorGuard N C) (hD : Γ ⊢[PRAAx] vectorGuard N D)
    (hΦC : Γ ⊢[PRAAx] holdsAt Φ C x) (hΦD : Γ ⊢[PRAAx] holdsAt Φ D x) :
    Γ ⊢[PRAAx] holdsAt Φ (midpointVector N C D) x := by
  have first := Prf.allE C h
  simp only [Fm.subst_all, Fm.subst_imp, subst_vectorGuard, subst_holdsAt, subst_midpointVector, Syn.subst_var,
    Syn.up_zero, Syn.up_one, Syn.up_succ, Syn.inst_succ, Syn.subst_shift] at first
  have second := Prf.allE D first
  have cancel (t : PTm n) : Syn.subst (Syn.inst D) (Syn.subst (fun i => Syn.shift (var i)) t) = t := by
    simpa only [Syn.shift,Syn.subst_var] using Syn.subst_inst_shift D t
  have rule : Γ ⊢[PRAAx] vectorGuard N C ⟶ vectorGuard N D ⟶ holdsAt Φ C x ⟶ holdsAt Φ D x ⟶
      holdsAt Φ (midpointVector N C D) x := by
    simpa only [Fm.subst_imp,subst_vectorGuard,subst_holdsAt,subst_midpointVector,
      Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift,cancel] using second
  exact .impE (.impE (.impE (.impE rule hC) hD) hΦC) hΦD

theorem canonical_integer_membership (Φ : Fm PTm 2) (N m a b z x : PTm n)
    (hm : Γ ⊢[PRAAx] le one m) (he : Γ ⊢[PRAAx] coordinateEquations N m a b z)
    (hs : Γ ⊢[PRAAx] symmetricGuarded Φ N x) (hc : Γ ⊢[PRAAx] midpointGuarded Φ N x)
    (ha : Γ ⊢[PRAAx] holdsAt Φ (centerVector N m a) x)
    (hb : Γ ⊢[PRAAx] holdsAt Φ (centerVector N m b) x) :
    Γ ⊢[PRAAx] vectorGuard N (integerVector N z) ⋏ holdsAt Φ (integerVector N z) x := by
  have opp := symmetry_guarded_at Φ N _ x hs (center_vector_guard N m b hm) hb
  have mid := midpoint_guarded_at Φ N _ _ x hc (center_vector_guard N m a hm)
    (opposite_vector_guard N _) ha opp
  exact .andI (integer_vector_guard N z)
    (holdsAt_congr Φ x (midpoint_vector_integer N m a b z hm he) mid)

theorem canonical_vector_guards_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶
      (vectorGuard (var 0) (centerVector (var 0) (var 1) (var 2)) ⋏
        (vectorGuard (var 0) (oppositeVector (var 0) (var 2)) ⋏
          (vectorGuard (var 0) (midpointVector (var 0) (var 1) (var 2)) ⋏
            vectorGuard (var 0) (integerVector (var 0) (var 2)))))) :=
  closeUniv 3 (.impI (.andI (center_vector_guard _ _ _ Prf.hyp0) (.andI (opposite_vector_guard _ _)
    (.andI (midpoint_vector_guard _ _ _) (integer_vector_guard _ _)))))

theorem guarded_membership_closed (Φ : Fm PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le one (var 1) ⟶ coordinateEquations (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      symmetricGuarded Φ (var 0) (var 5) ⟶ midpointGuarded Φ (var 0) (var 5) ⟶
      holdsAt Φ (centerVector (var 0) (var 1) (var 2)) (var 5) ⟶
      holdsAt Φ (centerVector (var 0) (var 1) (var 3)) (var 5) ⟶
        (vectorGuard (var 0) (integerVector (var 0) (var 4)) ⋏
          holdsAt Φ (integerVector (var 0) (var 4)) (var 5))) :=
  closeUniv 6 (.impI (.impI (.impI (.impI (.impI (.impI
    (canonical_integer_membership Φ _ _ _ _ _ _ Prf.hyp1.wk.wk.wk.wk Prf.hyp1.wk.wk.wk
      Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0)))))))

end LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiWellFormed
