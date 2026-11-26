import IPRADerivations.DiophantineNumberTheory.MinkowskiCenters
import IPRADerivations.DiophantineNumberTheory.SignedEuclidean
import IPRADerivations.Foundations.SequenceEquality
import IPRADerivations.Core.CongruenceTactic
import IPRADerivations.Core.SubstCommand

/-!
# Literal runtime-vector midpoint cancellation for Minkowski centers

Packet `diophantine-number-theory/minkowski_ipra`, the midpoint replacement
in the finite mesh proof. This module supplies the vector-code arithmetic
and arbitrary-formula substitution step; the geometric grid producer and
its symmetry/midpoint-closure certificates are separate inputs.

All four vector programs are actual `MasterCertificate.sequence`
constructors. Signed input coordinates use the total pair/entry decoder.
A bounded family of genuine integer coordinate equations implies equality
of the entire constructed midpoint code with the constructed integer-vector
code. Equality uses the checked stack program, not an extensionality axiom
for arbitrary sequence codes. This literal equality supports substitution
in an arbitrary fixed membership formula.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiCenterVectors

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiCenters
  (center opposite midpoint midpoint_code_integer)
open LeanProofs.IPRA.DiophantineNumberTheory.SignedEuclidean (decode)
open LeanProofs.IPRA.Analysis.RationalIntegerNormalization (integerCode)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_decode sequence_length)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)
open LeanProofs.IPRA.Foundations.SequenceEquality (agree sequence_equal)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def signedCoordinate (a k : PTm n) : ZT n := decode (entry a k)
def centerBody : PTm 2 := center (signedCoordinate (sndT (var 1)) (var 0)) (fstT (var 1))
def oppositeBody : PTm 2 := opposite (entry (var 1) (var 0))
def midpointBody : PTm 2 := midpoint (entry (fstT (var 1)) (var 0)) (entry (sndT (var 1)) (var 0))
def integerBody : PTm 2 := integerCode (signedCoordinate (var 1) (var 0))

def centerVector (N m a : PTm n) : PTm n := sequence centerBody N (pairT m a)
def oppositeVector (N C : PTm n) : PTm n := sequence oppositeBody N C
def midpointVector (N C D : PTm n) : PTm n := sequence midpointBody N (pairT C D)
def integerVector (N z : PTm n) : PTm n := sequence integerBody N z

ipra_subst signedCoordinate
ipra_subst centerVector
ipra_subst oppositeVector
ipra_subst midpointVector
ipra_subst integerVector

theorem center_congr {a a' m m' : PTm n} (ha : Γ ⊢[PRAAx] a ≐ a') (hm : Γ ⊢[PRAAx] m ≐ m') :
    Γ ⊢[PRAAx] center (decode a) m ≐ center (decode a') m' := by
  ipra_congr (center (decode (var 0)) (var 1) : PTm 2) with [ha, hm]
theorem opposite_congr {c c' : PTm n} (hc : Γ ⊢[PRAAx] c ≐ c') : Γ ⊢[PRAAx] opposite c ≐ opposite c' := by
  ipra_congr (opposite (var 0) : PTm 1) with [hc]
theorem midpoint_congr {c c' d d' : PTm n} (hc : Γ ⊢[PRAAx] c ≐ c') (hd : Γ ⊢[PRAAx] d ≐ d') :
    Γ ⊢[PRAAx] midpoint c d ≐ midpoint c' d' := by
  ipra_congr (midpoint (var 0) (var 1) : PTm 2) with [hc, hd]

theorem center_body_at (k m a : PTm n) :
    Γ ⊢[PRAAx] inst2 centerBody k (pairT m a) ≐ center (signedCoordinate a k) m := by
  have e : inst2 centerBody k (pairT m a) =
      center (signedCoordinate (sndT (pairT m a)) k) (fstT (pairT m a)) := by simp [inst2,centerBody]
  rw [e]
  exact center_congr (entry_congr (snd_pair _ _) (.eqRefl _)) (fst_pair _ _)

theorem midpoint_body_at (k C D : PTm n) :
    Γ ⊢[PRAAx] inst2 midpointBody k (pairT C D) ≐ midpoint (entry C k) (entry D k) := by
  have e : inst2 midpointBody k (pairT C D) =
      midpoint (entry (fstT (pairT C D)) k) (entry (sndT (pairT C D)) k) := by simp [inst2,midpointBody]
  rw [e]
  exact midpoint_congr (entry_congr (fst_pair _ _) (.eqRefl _)) (entry_congr (snd_pair _ _) (.eqRefl _))

theorem integer_body_at (k z : PTm n) :
    Γ ⊢[PRAAx] inst2 integerBody k z ≐ integerCode (signedCoordinate z k) := by simp [inst2,integerBody]; exact .eqRefl _

theorem center_lookup (N m a k : PTm n) (hk : Γ ⊢[PRAAx] lt k N) :
    Γ ⊢[PRAAx] entry (centerVector N m a) k ≐ center (signedCoordinate a k) m :=
  (sequence_decode centerBody hk).eqTrans (center_body_at k m a)
theorem opposite_lookup (N C k : PTm n) (hk : Γ ⊢[PRAAx] lt k N) :
    Γ ⊢[PRAAx] entry (oppositeVector N C) k ≐ opposite (entry C k) := by
  simpa [oppositeVector,inst2,oppositeBody] using sequence_decode (Γ := Γ) oppositeBody (x := C) hk
theorem midpoint_lookup (N C D k : PTm n) (hk : Γ ⊢[PRAAx] lt k N) :
    Γ ⊢[PRAAx] entry (midpointVector N C D) k ≐ midpoint (entry C k) (entry D k) :=
  (sequence_decode midpointBody hk).eqTrans (midpoint_body_at k C D)
theorem integer_lookup (N z k : PTm n) (hk : Γ ⊢[PRAAx] lt k N) :
    Γ ⊢[PRAAx] entry (integerVector N z) k ≐ integerCode (signedCoordinate z k) :=
  (sequence_decode integerBody hk).eqTrans (integer_body_at k z)

theorem center_length (N m a : PTm n) : Γ ⊢[PRAAx] length (centerVector N m a) ≐ N := sequence_length _ _ _
theorem opposite_length (N C : PTm n) : Γ ⊢[PRAAx] length (oppositeVector N C) ≐ N := sequence_length _ _ _
theorem midpoint_length (N C D : PTm n) : Γ ⊢[PRAAx] length (midpointVector N C D) ≐ N := sequence_length _ _ _
theorem integer_length (N z : PTm n) : Γ ⊢[PRAAx] length (integerVector N z) ≐ N := sequence_length _ _ _

def coordinateEquations (N m a b z : PTm n) : Fm PTm n :=
  .all (lt (var 0) (Syn.shift N) ⟶
    ZT.eq (signedCoordinate (Syn.shift a) (var 0)-signedCoordinate (Syn.shift b) (var 0))
      (ZT.ofNat (Syn.shift m)*signedCoordinate (Syn.shift z) (var 0)))

@[simp] theorem subst_coordinateEquations {l : ℕ} (σ : Fin n → PTm l) (N m a b z : PTm n) :
    (coordinateEquations N m a b z).subst σ = coordinateEquations (Syn.subst σ N) (Syn.subst σ m)
      (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ z) := by
  simp only [coordinateEquations,Fm.subst_all,Fm.subst_imp,subst_lt,ZT.subst_eq,ZT.subst_sub,
    ZT.subst_mul,ZT.subst_ofNat,subst_signedCoordinate,Syn.subst_var,Syn.up_zero,Syn.up_succ,
    Syn.subst_shift,Syn.shift_subst]

theorem coordinate_equations_at (N m a b z k : PTm n) (h : Γ ⊢[PRAAx] coordinateEquations N m a b z)
    (hk : Γ ⊢[PRAAx] lt k N) :
    Γ ⊢[PRAAx] ZT.eq (signedCoordinate a k-signedCoordinate b k) (ZT.ofNat m*signedCoordinate z k) := by
  have rule : Γ ⊢[PRAAx] lt k N ⟶
      ZT.eq (signedCoordinate a k-signedCoordinate b k) (ZT.ofNat m*signedCoordinate z k) := by
    simpa only [coordinateEquations,Fm.subst_imp,subst_lt,ZT.subst_eq,ZT.subst_sub,ZT.subst_mul,
      ZT.subst_ofNat,subst_signedCoordinate,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using Prf.allE k h
  exact .impE rule hk

theorem midpoint_coordinate (N m a b z k : PTm n) (hm : Γ ⊢[PRAAx] le one m) (hk : Γ ⊢[PRAAx] lt k N)
    (h : Γ ⊢[PRAAx] ZT.eq (signedCoordinate a k-signedCoordinate b k) (ZT.ofNat m*signedCoordinate z k)) :
    Γ ⊢[PRAAx] midpoint (entry (centerVector N m a) k)
      (entry (oppositeVector N (centerVector N m b)) k) ≐ integerCode (signedCoordinate z k) :=
  (midpoint_congr (center_lookup N m a k hk)
    ((opposite_lookup N _ k hk).eqTrans (opposite_congr (center_lookup N m b k hk)))).eqTrans
    (midpoint_code_integer _ _ _ _ hm h)

/-- Literal equality of actual vector codes; all numerical data, including
dimension zero and modulus one, remain internal. -/
theorem midpoint_vector_integer (N m a b z : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (h : Γ ⊢[PRAAx] coordinateEquations N m a b z) :
    Γ ⊢[PRAAx] midpointVector N (centerVector N m a) (oppositeVector N (centerVector N m b)) ≐ integerVector N z := by
  apply sequence_equal midpointBody integerBody N (pairT (centerVector N m a) (oppositeVector N (centerVector N m b))) z
  refine .allI (.impI ?_)
  have positive : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift m) := by
    simpa only [Fm.shift,subst_le,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift] using hm.shift
  have eqs : Γ.map Fm.shift ⊢[PRAAx] coordinateEquations (Syn.shift N) (Syn.shift m) (Syn.shift a) (Syn.shift b) (Syn.shift z) := by
    simpa only [Fm.shift,subst_coordinateEquations,Syn.shift] using h.shift
  have result := (midpoint_body_at (Γ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift) (var 0)
      (centerVector (Syn.shift N) (Syn.shift m) (Syn.shift a))
      (oppositeVector (Syn.shift N) (centerVector (Syn.shift N) (Syn.shift m) (Syn.shift b)))).eqTrans
    ((midpoint_coordinate _ _ _ _ _ _ positive.wk Prf.hyp0
      (coordinate_equations_at _ _ _ _ _ _ eqs.wk Prf.hyp0)).eqTrans (integer_body_at _ _).eqSymm)
  simpa only [Syn.shift,subst_pairT,subst_centerVector,subst_oppositeVector] using result

/-! ## Arbitrary-formula substitution and genuine geometric closure contracts -/

def holds (Φ : Fm PTm 1) (C : PTm n) : Fm PTm n := Φ.subst ![C]

@[simp] theorem subst_holds {l : ℕ} (σ : Fin n → PTm l) (Φ : Fm PTm 1) (C : PTm n) :
    (holds Φ C).subst σ = holds Φ (Syn.subst σ C) := by
  simp only [holds,Fm.subst_subst]
  congr 1; funext i; fin_cases i; rfl

theorem holds_congr (Φ : Fm PTm 1) {C D : PTm n} (h : Γ ⊢[PRAAx] C ≐ D)
    (hC : Γ ⊢[PRAAx] holds Φ C) : Γ ⊢[PRAAx] holds Φ D :=
  Prf.eqSubst Φ ![C] ![D] (fun i => by fin_cases i; exact h) hC

/-- `Φ` is arbitrary and need not be quantifier-free or invariant under
rational-value equality. Replacement is justified by literal code equality. -/
theorem midpoint_membership (Φ : Fm PTm 1) (N m a b z : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (h : Γ ⊢[PRAAx] coordinateEquations N m a b z)
    (hK : Γ ⊢[PRAAx] holds Φ (midpointVector N (centerVector N m a) (oppositeVector N (centerVector N m b)))) :
    Γ ⊢[PRAAx] holds Φ (integerVector N z) := holds_congr Φ (midpoint_vector_integer N m a b z hm h) hK

def symmetric (Φ : Fm PTm 1) (N : PTm n) : Fm PTm n :=
  .all (holds Φ (var 0) ⟶ holds Φ (oppositeVector (Syn.shift N) (var 0)))
def midpointClosed (Φ : Fm PTm 1) (N : PTm n) : Fm PTm n :=
  .all (.all (holds Φ (var 1) ⟶ holds Φ (var 0) ⟶
    holds Φ (midpointVector (Syn.shift (Syn.shift N)) (var 1) (var 0))))

theorem symmetry_at (Φ : Fm PTm 1) (N C : PTm n) (h : Γ ⊢[PRAAx] symmetric Φ N)
    (hC : Γ ⊢[PRAAx] holds Φ C) : Γ ⊢[PRAAx] holds Φ (oppositeVector N C) := by
  have rule : Γ ⊢[PRAAx] holds Φ C ⟶ holds Φ (oppositeVector N C) := by
    simpa only [symmetric,Fm.subst_imp,subst_holds,subst_oppositeVector,Syn.subst_var,
      Syn.inst_zero,Syn.subst_inst_shift] using Prf.allE C h
  exact .impE rule hC

theorem midpoint_closed_at (Φ : Fm PTm 1) (N C D : PTm n) (h : Γ ⊢[PRAAx] midpointClosed Φ N)
    (hC : Γ ⊢[PRAAx] holds Φ C) (hD : Γ ⊢[PRAAx] holds Φ D) :
    Γ ⊢[PRAAx] holds Φ (midpointVector N C D) := by
  have first := Prf.allE C h
  simp only [midpointClosed,Fm.subst_all,Fm.subst_imp,subst_holds,subst_midpointVector,
    Syn.subst_var,Syn.up_zero,Syn.up_one,Syn.up_succ,Syn.inst_succ,Syn.subst_shift,Syn.shift_subst] at first
  have second := Prf.allE D first
  have cancel : Syn.subst (Syn.inst D) (Syn.subst (fun i => Syn.shift (var i)) N) = N := by
    simpa only [Syn.shift,Syn.subst_var] using Syn.subst_inst_shift D N
  have rule : Γ ⊢[PRAAx] holds Φ C ⟶ holds Φ D ⟶ holds Φ (midpointVector N C D) := by
    simpa only [Fm.subst_imp,subst_holds,subst_midpointVector,Syn.subst_var,
      Syn.inst_zero,Syn.subst_inst_shift,cancel] using second
  exact .impE (.impE rule hC) hD

/-- The symmetry and midpoint hypotheses are genuine input closure laws;
membership of the final integer vector is derived by actual code equality. -/
theorem integer_membership_of_centers (Φ : Fm PTm 1) (N m a b z : PTm n)
    (hm : Γ ⊢[PRAAx] le one m) (h : Γ ⊢[PRAAx] coordinateEquations N m a b z)
    (hs : Γ ⊢[PRAAx] symmetric Φ N) (hc : Γ ⊢[PRAAx] midpointClosed Φ N)
    (ha : Γ ⊢[PRAAx] holds Φ (centerVector N m a)) (hb : Γ ⊢[PRAAx] holds Φ (centerVector N m b)) :
    Γ ⊢[PRAAx] holds Φ (integerVector N z) :=
  midpoint_membership Φ N m a b z hm h
    (midpoint_closed_at Φ N _ _ hc ha (symmetry_at Φ N _ hs hb))

/-! ## Fixed PR metadata and closed internal endpoints -/

def centerVectorF : PR 3 := PTm.toPR (centerVector (var 0) (var 1) (var 2))
def oppositeVectorF : PR 2 := PTm.toPR (oppositeVector (var 0) (var 1))
def midpointVectorF : PR 3 := PTm.toPR (midpointVector (var 0) (var 1) (var 2))
def integerVectorF : PR 2 := PTm.toPR (integerVector (var 0) (var 1))

theorem center_at (N m a : PTm n) : Γ ⊢[PRAAx] ap3 centerVectorF N m a ≐ centerVector N m a := by
  simpa [centerVectorF,ap3] using toPR_eq (Γ := Γ) (centerVector (var 0) (var 1) (var 2) : PTm 3) ![N,m,a]
theorem opposite_at (N C : PTm n) : Γ ⊢[PRAAx] ap2 oppositeVectorF N C ≐ oppositeVector N C := by
  simpa [oppositeVectorF,ap2] using toPR_eq (Γ := Γ) (oppositeVector (var 0) (var 1) : PTm 2) ![N,C]
theorem midpoint_at (N C D : PTm n) : Γ ⊢[PRAAx] ap3 midpointVectorF N C D ≐ midpointVector N C D := by
  simpa [midpointVectorF,ap3] using toPR_eq (Γ := Γ) (midpointVector (var 0) (var 1) (var 2) : PTm 3) ![N,C,D]
theorem integer_at (N z : PTm n) : Γ ⊢[PRAAx] ap2 integerVectorF N z ≐ integerVector N z := by
  simpa [integerVectorF,ap2] using toPR_eq (Γ := Γ) (integerVector (var 0) (var 1) : PTm 2) ![N,z]

theorem vector_programs_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((ap3 centerVectorF (var 0) (var 1) (var 2) ≐ centerVector (var 0) (var 1) (var 2)) ⋏
      ((ap2 oppositeVectorF (var 0) (var 1) ≐ oppositeVector (var 0) (var 1)) ⋏
        ((ap3 midpointVectorF (var 0) (var 1) (var 2) ≐ midpointVector (var 0) (var 1) (var 2)) ⋏
          (ap2 integerVectorF (var 0) (var 1) ≐ integerVector (var 0) (var 1))))) :=
  closeUniv 3 (.andI (center_at _ _ _) (.andI (opposite_at _ _) (.andI (midpoint_at _ _ _) (integer_at _ _))))

theorem vector_lengths_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((length (centerVector (var 0) (var 1) (var 2)) ≐ var 0) ⋏
      ((length (oppositeVector (var 0) (var 1)) ≐ var 0) ⋏
        ((length (midpointVector (var 0) (var 1) (var 2)) ≐ var 0) ⋏
          (length (integerVector (var 0) (var 1)) ≐ var 0)))) :=
  closeUniv 3 (.andI (center_length _ _ _) (.andI (opposite_length _ _) (.andI (midpoint_length _ _ _) (integer_length _ _))))

theorem vector_lookups_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 3) (var 0) ⟶
      ((entry (centerVector (var 0) (var 1) (var 2)) (var 3) ≐ center (signedCoordinate (var 2) (var 3)) (var 1)) ⋏
        ((entry (oppositeVector (var 0) (var 1)) (var 3) ≐ opposite (entry (var 1) (var 3))) ⋏
          ((entry (midpointVector (var 0) (var 1) (var 2)) (var 3) ≐ midpoint (entry (var 1) (var 3)) (entry (var 2) (var 3))) ⋏
            (entry (integerVector (var 0) (var 1)) (var 3) ≐ integerCode (signedCoordinate (var 1) (var 3))))))) :=
  closeUniv 4 (.impI (.andI (center_lookup _ _ _ _ Prf.hyp0) (.andI (opposite_lookup _ _ _ Prf.hyp0)
    (.andI (midpoint_lookup _ _ _ _ Prf.hyp0) (integer_lookup _ _ _ Prf.hyp0)))))

theorem vector_midpoint_integer_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 1) ⟶ coordinateEquations (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      (midpointVector (var 0) (centerVector (var 0) (var 1) (var 2))
        (oppositeVector (var 0) (centerVector (var 0) (var 1) (var 3))) ≐ integerVector (var 0) (var 4))) :=
  closeUniv 5 (.impI (.impI (midpoint_vector_integer _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem arbitrary_membership_transport_closed (Φ : Fm PTm 1) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 1) ⟶ coordinateEquations (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      holds Φ (midpointVector (var 0) (centerVector (var 0) (var 1) (var 2))
        (oppositeVector (var 0) (centerVector (var 0) (var 1) (var 3)))) ⟶ holds Φ (integerVector (var 0) (var 4))) :=
  closeUniv 5 (.impI (.impI (.impI (midpoint_membership Φ _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

theorem integer_membership_from_closure_closed (Φ : Fm PTm 1) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 1) ⟶ coordinateEquations (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      symmetric Φ (var 0) ⟶ midpointClosed Φ (var 0) ⟶
      holds Φ (centerVector (var 0) (var 1) (var 2)) ⟶ holds Φ (centerVector (var 0) (var 1) (var 3)) ⟶
        holds Φ (integerVector (var 0) (var 4))) :=
  closeUniv 5 (.impI (.impI (.impI (.impI (.impI (.impI
    (integer_membership_of_centers Φ _ _ _ _ _ Prf.hyp1.wk.wk.wk.wk Prf.hyp1.wk.wk.wk
      Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0)))))))

#print axioms center_lookup
#print axioms midpoint_coordinate
#print axioms midpoint_vector_integer
#print axioms holds_congr
#print axioms midpoint_membership
#print axioms integer_membership_of_centers
#print axioms vector_programs_closed
#print axioms vector_lengths_closed
#print axioms vector_lookups_closed
#print axioms vector_midpoint_integer_closed
#print axioms arbitrary_membership_transport_closed
#print axioms integer_membership_from_closure_closed

/-! ## Membership formulas with persistent numerical parameters

The source suppresses additional numerical parameters in `Φ`. Here its
second free argument is persistent numerical data, retained under every
symmetry/midpoint binder. The guarded variants below require the stored
vector length; that guard alone is not a full canonical-code or geometric
well-formedness certificate.
-/

def holdsAt (Φ : Fm PTm 2) (C x : PTm n) : Fm PTm n := Φ.subst ![C,x]

@[simp] theorem subst_holdsAt {l : ℕ} (σ : Fin n → PTm l) (Φ : Fm PTm 2) (C x : PTm n) :
    (holdsAt Φ C x).subst σ = holdsAt Φ (Syn.subst σ C) (Syn.subst σ x) := by
  simp only [holdsAt,Fm.subst_subst]
  congr 1; funext i; fin_cases i <;> rfl

theorem holdsAt_congr (Φ : Fm PTm 2) (x : PTm n) {C D : PTm n} (h : Γ ⊢[PRAAx] C ≐ D)
    (hC : Γ ⊢[PRAAx] holdsAt Φ C x) : Γ ⊢[PRAAx] holdsAt Φ D x :=
  Prf.eqSubst Φ ![C,x] ![D,x] (fun i => by fin_cases i; exact h; exact .eqRefl _) hC

theorem midpoint_membership_at (Φ : Fm PTm 2) (N m a b z x : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (h : Γ ⊢[PRAAx] coordinateEquations N m a b z)
    (hK : Γ ⊢[PRAAx] holdsAt Φ (midpointVector N (centerVector N m a) (oppositeVector N (centerVector N m b))) x) :
    Γ ⊢[PRAAx] holdsAt Φ (integerVector N z) x :=
  holdsAt_congr Φ x (midpoint_vector_integer N m a b z hm h) hK

/-- This is the stronger closure law on every numerical code satisfying
the membership formula, with persistent data `x`. -/
def symmetricAt (Φ : Fm PTm 2) (N x : PTm n) : Fm PTm n :=
  .all (holdsAt Φ (var 0) (Syn.shift x) ⟶
    holdsAt Φ (oppositeVector (Syn.shift N) (var 0)) (Syn.shift x))
def midpointClosedAt (Φ : Fm PTm 2) (N x : PTm n) : Fm PTm n :=
  .all (.all (holdsAt Φ (var 1) (Syn.shift (Syn.shift x)) ⟶
    holdsAt Φ (var 0) (Syn.shift (Syn.shift x)) ⟶
      holdsAt Φ (midpointVector (Syn.shift (Syn.shift N)) (var 1) (var 0)) (Syn.shift (Syn.shift x))))

private theorem cancel_shift (D t : PTm n) :
    Syn.subst (Syn.inst D) (Syn.subst (fun i => Syn.shift (var i)) t) = t := by
  simpa only [Syn.shift,Syn.subst_var] using Syn.subst_inst_shift D t

theorem symmetry_at_parameter (Φ : Fm PTm 2) (N x C : PTm n) (h : Γ ⊢[PRAAx] symmetricAt Φ N x)
    (hC : Γ ⊢[PRAAx] holdsAt Φ C x) : Γ ⊢[PRAAx] holdsAt Φ (oppositeVector N C) x := by
  have rule : Γ ⊢[PRAAx] holdsAt Φ C x ⟶ holdsAt Φ (oppositeVector N C) x := by
    simpa only [symmetricAt,Fm.subst_imp,subst_holdsAt,subst_oppositeVector,Syn.subst_var,
      Syn.inst_zero,Syn.subst_inst_shift] using Prf.allE C h
  exact .impE rule hC

theorem midpoint_at_parameter (Φ : Fm PTm 2) (N x C D : PTm n)
    (h : Γ ⊢[PRAAx] midpointClosedAt Φ N x) (hC : Γ ⊢[PRAAx] holdsAt Φ C x)
    (hD : Γ ⊢[PRAAx] holdsAt Φ D x) : Γ ⊢[PRAAx] holdsAt Φ (midpointVector N C D) x := by
  have first := Prf.allE C h
  simp only [midpointClosedAt,Fm.subst_all,Fm.subst_imp,subst_holdsAt,subst_midpointVector,
    Syn.subst_var,Syn.up_zero,Syn.up_one,Syn.up_succ,Syn.inst_succ,Syn.subst_shift,Syn.shift_subst] at first
  have second := Prf.allE D first
  have rule : Γ ⊢[PRAAx] holdsAt Φ C x ⟶ holdsAt Φ D x ⟶ holdsAt Φ (midpointVector N C D) x := by
    simpa only [Fm.subst_imp,subst_holdsAt,subst_midpointVector,Syn.subst_var,
      Syn.inst_zero,Syn.subst_inst_shift,cancel_shift] using second
  exact .impE (.impE rule hC) hD

theorem integer_membership_of_centers_at (Φ : Fm PTm 2) (N m a b z x : PTm n)
    (hm : Γ ⊢[PRAAx] le one m) (h : Γ ⊢[PRAAx] coordinateEquations N m a b z)
    (hs : Γ ⊢[PRAAx] symmetricAt Φ N x) (hc : Γ ⊢[PRAAx] midpointClosedAt Φ N x)
    (ha : Γ ⊢[PRAAx] holdsAt Φ (centerVector N m a) x) (hb : Γ ⊢[PRAAx] holdsAt Φ (centerVector N m b) x) :
    Γ ⊢[PRAAx] holdsAt Φ (integerVector N z) x :=
  midpoint_membership_at Φ N m a b z x hm h
    (midpoint_at_parameter Φ N x _ _ hc ha (symmetry_at_parameter Φ N x _ hs hb))

/-! ## Closure contracts guarded by the actual stored dimension -/

def shapedSymmetricAt (Φ : Fm PTm 2) (N x : PTm n) : Fm PTm n :=
  .all ((length (var 0) ≐ Syn.shift N) ⟶ holdsAt Φ (var 0) (Syn.shift x) ⟶
    holdsAt Φ (oppositeVector (Syn.shift N) (var 0)) (Syn.shift x))
def shapedMidpointClosedAt (Φ : Fm PTm 2) (N x : PTm n) : Fm PTm n :=
  .all (.all ((length (var 1) ≐ Syn.shift (Syn.shift N)) ⟶
    (length (var 0) ≐ Syn.shift (Syn.shift N)) ⟶
      holdsAt Φ (var 1) (Syn.shift (Syn.shift x)) ⟶ holdsAt Φ (var 0) (Syn.shift (Syn.shift x)) ⟶
        holdsAt Φ (midpointVector (Syn.shift (Syn.shift N)) (var 1) (var 0)) (Syn.shift (Syn.shift x))))

theorem shaped_symmetry_at (Φ : Fm PTm 2) (N x C : PTm n)
    (h : Γ ⊢[PRAAx] shapedSymmetricAt Φ N x) (hlen : Γ ⊢[PRAAx] length C ≐ N)
    (hC : Γ ⊢[PRAAx] holdsAt Φ C x) : Γ ⊢[PRAAx] holdsAt Φ (oppositeVector N C) x := by
  have rule : Γ ⊢[PRAAx] (length C ≐ N) ⟶ holdsAt Φ C x ⟶ holdsAt Φ (oppositeVector N C) x := by
    simpa only [shapedSymmetricAt,Fm.subst_imp,Fm.subst_eq,Foundations.SequenceComposition.subst_length,
      subst_holdsAt,subst_oppositeVector,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using Prf.allE C h
  exact .impE (.impE rule hlen) hC

theorem shaped_midpoint_at (Φ : Fm PTm 2) (N x C D : PTm n)
    (h : Γ ⊢[PRAAx] shapedMidpointClosedAt Φ N x) (hC_len : Γ ⊢[PRAAx] length C ≐ N)
    (hD_len : Γ ⊢[PRAAx] length D ≐ N) (hC : Γ ⊢[PRAAx] holdsAt Φ C x)
    (hD : Γ ⊢[PRAAx] holdsAt Φ D x) : Γ ⊢[PRAAx] holdsAt Φ (midpointVector N C D) x := by
  have first := Prf.allE C h
  simp only [shapedMidpointClosedAt,Fm.subst_all,Fm.subst_imp,Fm.subst_eq,
    Foundations.SequenceComposition.subst_length,subst_holdsAt,subst_midpointVector,
    Syn.subst_var,Syn.up_zero,Syn.up_one,Syn.up_succ,Syn.inst_succ,Syn.subst_shift,Syn.shift_subst] at first
  have second := Prf.allE D first
  have rule : Γ ⊢[PRAAx] (length C ≐ N) ⟶ (length D ≐ N) ⟶ holdsAt Φ C x ⟶ holdsAt Φ D x ⟶
      holdsAt Φ (midpointVector N C D) x := by
    simpa only [Fm.subst_imp,Fm.subst_eq,Foundations.SequenceComposition.subst_length,
      subst_holdsAt,subst_midpointVector,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift,cancel_shift] using second
  exact .impE (.impE (.impE (.impE rule hC_len) hD_len) hC) hD

/-- The shape guards are discharged from actual sequence constructors,
including the reflected center. No output-membership premise is supplied. -/
theorem integer_membership_of_shaped_centers (Φ : Fm PTm 2) (N m a b z x : PTm n)
    (hm : Γ ⊢[PRAAx] le one m) (h : Γ ⊢[PRAAx] coordinateEquations N m a b z)
    (hs : Γ ⊢[PRAAx] shapedSymmetricAt Φ N x) (hc : Γ ⊢[PRAAx] shapedMidpointClosedAt Φ N x)
    (ha : Γ ⊢[PRAAx] holdsAt Φ (centerVector N m a) x) (hb : Γ ⊢[PRAAx] holdsAt Φ (centerVector N m b) x) :
    Γ ⊢[PRAAx] holdsAt Φ (integerVector N z) x :=
  midpoint_membership_at Φ N m a b z x hm h
    (shaped_midpoint_at Φ N x _ _ hc (center_length N m a) (opposite_length N _)
      ha (shaped_symmetry_at Φ N x _ hs (center_length N m b) hb))

theorem parameterized_membership_transport_closed (Φ : Fm PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le one (var 1) ⟶ coordinateEquations (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      holdsAt Φ (midpointVector (var 0) (centerVector (var 0) (var 1) (var 2))
        (oppositeVector (var 0) (centerVector (var 0) (var 1) (var 3)))) (var 5) ⟶
          holdsAt Φ (integerVector (var 0) (var 4)) (var 5)) :=
  closeUniv 6 (.impI (.impI (.impI (midpoint_membership_at Φ _ _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

theorem parameterized_integer_membership_closed (Φ : Fm PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le one (var 1) ⟶ coordinateEquations (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      symmetricAt Φ (var 0) (var 5) ⟶ midpointClosedAt Φ (var 0) (var 5) ⟶
      holdsAt Φ (centerVector (var 0) (var 1) (var 2)) (var 5) ⟶
      holdsAt Φ (centerVector (var 0) (var 1) (var 3)) (var 5) ⟶
        holdsAt Φ (integerVector (var 0) (var 4)) (var 5)) :=
  closeUniv 6 (.impI (.impI (.impI (.impI (.impI (.impI
    (integer_membership_of_centers_at Φ _ _ _ _ _ _ Prf.hyp1.wk.wk.wk.wk Prf.hyp1.wk.wk.wk
      Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0)))))))

theorem shaped_integer_membership_closed (Φ : Fm PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le one (var 1) ⟶ coordinateEquations (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      shapedSymmetricAt Φ (var 0) (var 5) ⟶ shapedMidpointClosedAt Φ (var 0) (var 5) ⟶
      holdsAt Φ (centerVector (var 0) (var 1) (var 2)) (var 5) ⟶
      holdsAt Φ (centerVector (var 0) (var 1) (var 3)) (var 5) ⟶
        holdsAt Φ (integerVector (var 0) (var 4)) (var 5)) :=
  closeUniv 6 (.impI (.impI (.impI (.impI (.impI (.impI
    (integer_membership_of_shaped_centers Φ _ _ _ _ _ _ Prf.hyp1.wk.wk.wk.wk Prf.hyp1.wk.wk.wk
      Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0)))))))

#print axioms holdsAt_congr
#print axioms midpoint_membership_at
#print axioms symmetry_at_parameter
#print axioms midpoint_at_parameter
#print axioms integer_membership_of_centers_at
#print axioms shaped_symmetry_at
#print axioms shaped_midpoint_at
#print axioms integer_membership_of_shaped_centers
#print axioms parameterized_membership_transport_closed
#print axioms parameterized_integer_membership_closed
#print axioms shaped_integer_membership_closed

end LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiCenterVectors
